typedef long unsigned int size_t;
typedef size_t idx_t;
typedef int data_t;
typedef int bool_t;

extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));
extern void exit(int status);
extern void abort(void);

extern void ASSERT(int);
extern void ASSUME(int);
extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
extern void *memcpy(void *dest, const void *src, size_t n);
extern void *memset(void *s, int c, size_t n);
extern void *alloca (size_t);

#define NULL (void *) 0