#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

typedef struct {
    int32_t len, ptr;
    int32_t maxBufSize;
    char *buf;
} cbuffer_t;

void cbuffer_init(cbuffer_t* buf, char* arr, int32_t size)
{
    buf->buf = arr;
    buf->maxBufSize = size;
    buf->len = 0;
    buf->ptr = 0;
}

int cbuffer_append_int8(cbuffer_t* buf, int8_t n)
{
    *(buf->buf + buf->len) = (char)n;
    buf->len++;

    return 1;
}

int cbuffer_retrieve_int8(cbuffer_t* buf, int8_t* n)
{
    *n = *(int8_t *)(buf->buf + buf->ptr);
    buf->ptr++;

    return 1;
}


//#define assert(ARG)

struct A {
    int8_t a8;
    int8_t b8;
};

struct A a1;
struct A a2;

cbuffer_t mbuf;
char arr[20];

int main() {

    cbuffer_t *buf;

    buf = &mbuf;

    //a1.a8 = nondet_char();
    //a1.b8 = nondet_char();
	a1.a8 = 'a';
    a1.b8 = 'b';
	
    cbuffer_init(buf, arr, 20);

    cbuffer_append_int8(buf, a1.a8);

    cbuffer_retrieve_int8(buf, &(a2.a8));

    assert(a1.a8 == a2.a8);
	return 0;
}
