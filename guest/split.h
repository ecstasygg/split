#ifndef SPLIT_H
#define SPLIT_H
#include <microkit.h>
#include <stdint.h>

#define PAGES 4u
#define CLIENTS 2u
#define SLOTS (PAGES * CLIENTS)
#define FRAMES (PAGES + SLOTS)
#define BYTES 4096u
#define BASE 0x40000000ul
#define BACKING 0x60000000ul
#define TASK 0x50000000ul
#define LIMIT 255u

struct job {
  unsigned page, length;
  char text[LIMIT + 1];
};

static inline void number(unsigned long n) {
  char s[24];
  unsigned i = sizeof(s) - 1;
  s[i] = 0;
  do {
    s[--i] = '0' + n % 10;
    n /= 10;
  } while (n);
  microkit_dbg_puts(s + i);
}

static inline unsigned char seed(unsigned page, unsigned offset) {
  return (page * 17u + offset) % 256u;
}

static inline void require(int ok, const char *message) {
  if (ok) return;
  microkit_dbg_puts("@error ");
  microkit_dbg_puts(message);
  microkit_dbg_puts("\n");
  for (;;) seL4_Yield();
}
#endif
