#include "split.h"

void init(void) {}

void notified(microkit_channel channel) {
  require(channel == 0, "unknown notification");
  volatile struct job *job = (void *)TASK;
  unsigned p = job->page, length = job->length;
  require(p < PAGES && length <= LIMIT, "edit bounds");
  volatile unsigned char *page = (void *)(BASE + p * BYTES);
  for (unsigned i = 0; i <= length; ++i) {
    page[i] = job->text[i];
    microkit_mr_set(0, p);
    microkit_mr_set(1, i);
    microkit_mr_set(2, page[i]);
    (void)microkit_ppcall(0, microkit_msginfo_new(1, 3));
  }
  (void)microkit_ppcall(0, microkit_msginfo_new(2, 0));
}
