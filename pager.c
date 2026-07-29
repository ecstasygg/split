#include "split.h"

#ifndef SHARED_WRITE
#define SHARED_WRITE 0
#endif

static unsigned mapping[SLOTS], next = PAGES;
static unsigned available[FRAMES - PAGES], returned;
static seL4_CPtr caps[SLOTS];
static int started, busy = -1;
static char line[384];
static unsigned used;
static volatile uint32_t *uart = (void *)0x70000000ul;

static unsigned char *frame(unsigned f) {
  return (unsigned char *)(BACKING + f * BYTES);
}

static void done(void) { microkit_dbg_puts("@done\n"); }

static seL4_Word physical(seL4_CPtr cap) {
  seL4_ARM_Page_GetAddress_t result = seL4_ARM_Page_GetAddress(cap);
  require(result.error == seL4_NoError, "frame address query");
  return result.paddr;
}

static int length(const char *text, unsigned *size) {
  unsigned n = 0;
  while (text[n]) if (++n > LIMIT) return 0;
  *size = n;
  return 1;
}

static void map(unsigned k, seL4_CPtr page, int write) {
  seL4_CapRights_t rights = seL4_CapRights_new(0, 0, 1, write);
  require(seL4_ARM_Page_Map(page, microkit_cspace_root_slot_to_cptr(1 + k / PAGES),
    BASE + (k % PAGES) * BYTES, rights,
    seL4_ARM_Default_VMAttributes | seL4_ARM_ExecuteNever) == seL4_NoError,
    "page map");
}

static void table(void) {
  microkit_dbg_puts("SPLIT TABLE");
  for (unsigned k = 0; k < SLOTS; ++k) {
    microkit_dbg_puts(" "); number(mapping[k]);
  }
  microkit_dbg_puts("\n");
}

void init(void) {
  for (unsigned f = 0; f < FRAMES; ++f)
    for (unsigned b = 0; b < BYTES; ++b) frame(f)[b] = 0;
  for (unsigned k = 0; k < SLOTS; ++k) {
    mapping[k] = k % PAGES;
    caps[k] = microkit_cspace_root_slot_to_cptr(10 + k);
    map(k, caps[k], SHARED_WRITE);
  }
  uart[0x30 / 4] |= 0x301;
  uart[0x2c / 4] = 0x60;
  uart[0x44 / 4] = 0x7ff;
  uart[0x38 / 4] = 0x10;
  microkit_irq_ack(5);
  table();
  microkit_dbg_puts("@ready\n");
}

seL4_Bool fault(microkit_child child, microkit_msginfo info, microkit_msginfo *reply) {
  require(child < CLIENTS && microkit_msginfo_get_label(info) == seL4_Fault_VMFault,
    "unexpected fault");
  seL4_Word address = microkit_mr_get(seL4_VMFault_Addr);
  seL4_Word fsr = microkit_mr_get(seL4_VMFault_FSR);
  seL4_Word ip = microkit_mr_get(seL4_VMFault_IP);
  require(address >= BASE && address < BASE + PAGES * BYTES && (fsr & (1ul << 6)),
    "not a managed write fault");
  unsigned k = child * PAGES + (address - BASE) / BYTES;
  unsigned old = mapping[k], fresh = returned ? available[--returned] : next++;
  require(old < PAGES && fresh < FRAMES, "frame pool exhausted");
  seL4_Word source = physical(caps[k]);
  seL4_CPtr destination = microkit_cspace_root_slot_to_cptr(30 + fresh - PAGES);
  seL4_Word target = physical(destination);
  for (unsigned b = 0; b < BYTES; ++b) frame(fresh)[b] = frame(old)[b];
  require(seL4_ARM_Page_Unmap(caps[k]) == seL4_NoError, "page unmap");
  caps[k] = microkit_cspace_root_slot_to_cptr(30 + fresh - PAGES);
  map(k, caps[k], 1);
  mapping[k] = fresh;
  microkit_dbg_puts("SPLIT COPY "); number(k);
  microkit_dbg_puts(" "); number(old);
  microkit_dbg_puts(" "); number(fresh); microkit_dbg_puts("\n");
  table();
  microkit_dbg_puts("SPLIT FAULT "); number(k);
  microkit_dbg_puts(" "); number(address);
  microkit_dbg_puts(" "); number(ip);
  microkit_dbg_puts(" "); number(fsr);
  microkit_dbg_puts(" "); number(source);
  microkit_dbg_puts(" "); number(target); microkit_dbg_puts("\n");
  *reply = microkit_msginfo_new(0, 0);
  return seL4_True;
}

microkit_msginfo protected(microkit_channel channel, microkit_msginfo info) {
  require(channel < CLIENTS && (int)channel == busy, "unexpected worker");
  if (microkit_msginfo_get_label(info) == 1) {
    unsigned p = microkit_mr_get(0), offset = microkit_mr_get(1), byte = microkit_mr_get(2);
    require(p < PAGES && offset <= LIMIT && byte < 256, "write bounds");
    unsigned k = channel * PAGES + p;
    require(frame(mapping[k])[offset] == byte, "write observation");
    microkit_dbg_puts("SPLIT W "); number(k);
    microkit_dbg_puts(" "); number(offset);
    microkit_dbg_puts(" "); number(byte); microkit_dbg_puts("\n");
  } else {
    require(microkit_msginfo_get_label(info) == 2, "unknown worker request");
    busy = -1;
    done();
  }
  return microkit_msginfo_new(0, 0);
}

static void request(void) {
  if (busy >= 0) { microkit_dbg_puts("@error worker busy\n"); return; }
  if (line[0] == 'B' && !started && line[1] == ' ' && line[2] >= '0' && line[2] <= '3' && line[3] == ' ') {
    unsigned p = line[2] - '0', size;
    if (!length(line + 4, &size)) { microkit_dbg_puts("@error field too long\n"); return; }
    for (unsigned b = 0; b < BYTES; ++b) frame(p)[b] = 0;
    for (unsigned i = 0; i < size; ++i) frame(p)[i] = line[4 + i];
    done();
  } else if (line[0] == 'S' && !line[1] && !started) {
    started = 1;
    done();
  } else if (!started) {
    microkit_dbg_puts("@error document not opened\n");
  } else if (line[0] == 'E' && line[1] == ' ' && line[2] >= '0' && line[2] <= '1' && line[3] == ' ' && line[4] >= '0' && line[4] <= '3' && line[5] == ' ') {
    unsigned c = line[2] - '0', p = line[4] - '0', size;
    if (!length(line + 6, &size)) { microkit_dbg_puts("@error field too long\n"); return; }
    volatile struct job *job = (void *)(TASK + c * BYTES);
    job->page = p;
    for (unsigned i = 0; i < size; ++i) job->text[i] = line[6 + i];
    job->text[size] = 0;
    job->length = size;
    busy = c;
    microkit_notify(c);
  } else if (line[0] == 'Q' && line[1] == ' ' && line[2] >= '0' && line[2] <= '2' && !line[3]) {
    unsigned c = line[2] - '0';
    for (unsigned p = 0; p < PAGES; ++p) {
      unsigned k = c * PAGES + p, f = c == 2 ? p : mapping[k];
      if (c < CLIENTS) {
        for (unsigned b = 0; b <= LIMIT; ++b) {
          microkit_dbg_puts("SPLIT R "); number(k);
          microkit_dbg_puts(" "); number(b);
          microkit_dbg_puts(" "); number(frame(f)[b]); microkit_dbg_puts("\n");
          if (!frame(f)[b]) break;
        }
      }
      microkit_dbg_puts("@field "); number(p); microkit_dbg_puts(" ");
      for (unsigned b = 0; b < LIMIT && frame(f)[b]; ++b) {
        char text[2] = {(char)frame(f)[b], 0}; microkit_dbg_puts(text);
      }
      microkit_dbg_puts("\n");
    }
    done();
  } else if (line[0] == 'P' && !line[1]) {
    for (unsigned k = 0; k < SLOTS; ++k) {
      microkit_dbg_puts("@map "); number(k);
      microkit_dbg_puts(" "); number(BASE + (k % PAGES) * BYTES);
      microkit_dbg_puts(" "); number(physical(caps[k]));
      microkit_dbg_puts(" "); number(mapping[k] >= PAGES); microkit_dbg_puts("\n");
    }
    done();
  } else if (line[0] == 'D' && line[1] == ' ' && line[2] >= '0' && line[2] <= '1' && !line[3]) {
    unsigned c = line[2] - '0';
    require(seL4_TCB_Suspend(BASE_TCB_CAP + c) == seL4_NoError, "worker suspend");
    microkit_dbg_puts("SPLIT STOP "); number(c); microkit_dbg_puts("\n");
    for (unsigned p = 0; p < PAGES; ++p) {
      unsigned k = c * PAGES + p, f = mapping[k];
      if (f < PAGES) continue;
      seL4_Word old = physical(caps[k]);
      require(seL4_ARM_Page_Unmap(caps[k]) == seL4_NoError, "private page unmap");
      caps[k] = microkit_cspace_root_slot_to_cptr(10 + k);
      map(k, caps[k], 0);
      mapping[k] = p;
      volatile unsigned char *bytes = frame(f);
      for (unsigned b = 0; b < BYTES; ++b) bytes[b] = 0;
      unsigned cleared = 0;
      for (unsigned b = 0; b < BYTES; ++b) cleared += bytes[b] == 0;
      require(cleared == BYTES && returned < FRAMES - PAGES, "frame scrub");
      available[returned++] = f;
      microkit_dbg_puts("SPLIT RELEASE "); number(k);
      microkit_dbg_puts(" "); number(f);
      microkit_dbg_puts(" "); number(old);
      microkit_dbg_puts(" "); number(physical(caps[k]));
      microkit_dbg_puts(" "); number(cleared); microkit_dbg_puts("\n");
    }
    table();
    require(seL4_TCB_Resume(BASE_TCB_CAP + c) == seL4_NoError, "worker resume");
    microkit_dbg_puts("SPLIT RUN "); number(c); microkit_dbg_puts("\n");
    done();
  } else if (line[0] == 'F' && !line[1]) {
    for (unsigned i = returned; i > 0; --i) {
      unsigned f = available[i - 1], cleared = 0;
      volatile unsigned char *bytes = frame(f);
      for (unsigned b = 0; b < BYTES; ++b) cleared += bytes[b] == 0;
      microkit_dbg_puts("@free "); number(f);
      microkit_dbg_puts(" "); number(physical(microkit_cspace_root_slot_to_cptr(30 + f - PAGES)));
      microkit_dbg_puts(" "); number(cleared); microkit_dbg_puts("\n");
      for (unsigned b = 0; b < 32; ++b) {
        microkit_dbg_puts("@zero "); number(f);
        microkit_dbg_puts(" "); number(b);
        microkit_dbg_puts(" "); number(bytes[b]); microkit_dbg_puts("\n");
      }
    }
    done();
  } else if (line[0] == 'H' && line[1] == ' ' && line[2] >= '0' && line[2] <= '2' && line[3] == ' ' && line[4] >= '0' && line[4] <= '3' && !line[5]) {
    unsigned c = line[2] - '0', p = line[4] - '0', k = c * PAGES + p;
    unsigned f = c == 2 ? p : mapping[k];
    seL4_CPtr cap = c == 2 ? microkit_cspace_root_slot_to_cptr(10 + p) : caps[k];
    microkit_dbg_puts("@addr "); number(c == 2 ? BACKING + p * BYTES : BASE + p * BYTES);
    microkit_dbg_puts(" "); number(physical(cap)); microkit_dbg_puts("\n");
    for (unsigned b = 0; b < 64; ++b) {
      if (c < CLIENTS) {
        microkit_dbg_puts("SPLIT R "); number(k);
        microkit_dbg_puts(" "); number(b);
        microkit_dbg_puts(" "); number(frame(f)[b]); microkit_dbg_puts("\n");
      }
      microkit_dbg_puts("@byte "); number(b);
      microkit_dbg_puts(" "); number(frame(f)[b]); microkit_dbg_puts("\n");
    }
    done();
  } else if (line[0] == 'M' && !line[1]) {
    table();
    done();
  } else {
    microkit_dbg_puts("@error unknown request\n");
  }
}

void notified(microkit_channel channel) {
  require(channel == 5, "unknown interrupt");
  uart[0x44 / 4] = 0x7ff;
  while (!(uart[0x18 / 4] & 0x10)) {
    unsigned ch = uart[0] & 255;
    if (ch == '\n') {
      line[used] = 0;
      request();
      used = 0;
    } else if (ch >= 32 && ch < 127 && used < sizeof(line) - 1) {
      line[used++] = ch;
    }
  }
  microkit_irq_ack(5);
}
