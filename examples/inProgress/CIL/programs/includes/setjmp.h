struct __jmp_buf_tag {
	unsigned char used;
};
typedef struct __jmp_buf_tag jmp_buf[1];
int setjmp(jmp_buf env);
void longjmp(jmp_buf env, int val);
