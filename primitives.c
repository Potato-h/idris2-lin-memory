#include <memory.h>

int read_ptr(int *ptr, int offset) { return *(ptr + offset); }

void write_ptr(int *ptr, int offset, int value) { *(ptr + offset) = value; }

void my_memcpy(void *dst, void *src, size_t bytes) { memcpy(dst, src, bytes); }