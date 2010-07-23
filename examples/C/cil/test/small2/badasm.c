extern inline void __set_64bit (unsigned long long * ptr,
                unsigned int low, unsigned int high)
{
        __asm__ __volatile__ (
                "\n1:\t"
                "movl (%0), %%eax\n\t"
                "movl 4(%0), %%edx\n\t"
                "cmpxchg8b (%0)\n\t"
                "jnz 1b"
                :
                :       "D"(ptr),
                        "b"(low),
                        "c"(high)
                :       "ax","dx","memory");
}
