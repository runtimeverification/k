/* From Radar 7980096.  Test case by Shantonu Sen! */
#include <assert.h>

typedef union {
	struct {
		unsigned long long        count                   :8;
		unsigned long long        mcg_ctl_p               :1;
	}          bits;
	unsigned long long   u64;
} ia32_mcg_cap_t;

int main(int argc, char *argv[]) {
	unsigned long long ctl_p;
	ia32_mcg_cap_t   ia32_mcg_cap;

	ia32_mcg_cap.u64 = 0x806;

	ctl_p = ia32_mcg_cap.bits.mcg_ctl_p;
	assert(ctl_p == 0);

	return 0;
}
