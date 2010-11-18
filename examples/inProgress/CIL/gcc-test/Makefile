KCC ?= "../dist/kcc"
KCCPROFILE ?= "../dist/kcc -s -p"
GCC ?= "gcc -m32 -O0 -U __GNUC__ -pedantic -std=c99"
GCC34 ?= "gcc34 -m32 -O0 -U __GNUC__ -pedantic -std=c99"
ICC ?= "icc -m32 -O0 -U __GNUC__ -pedantic -std=c99"
CLANG ?= "clang -fcatch-undefined-behavior -m32 -O0 -U __GNUC__ -pedantic-errors -std=c99"
#LCC ?= "../junk/lcc4.2/builddir/lcc"
CILCC ?= "./cilcc.sh"

RUNTEST = runtest --tool=gcc

GCC_FLAGS = --outdir results/out.gcc --tool_exec $(GCC)
GCC34_FLAGS = --outdir results/out.gcc34 --tool_exec $(GCC34)
ICC_FLAGS = --outdir results/out.icc --tool_exec $(ICC)
KCC_FLAGS = --outdir results/out.kcc --tool_exec $(KCC)
KCC_PROFILE_FLAGS = --outdir results/out.kcc --tool_exec $(KCCPROFILE)
CIL_FLAGS = --outdir results/out.cilcc --tool_exec $(CILCC)
CLANG_FLAGS = --outdir results/out.clang --tool_exec $(CLANG)
#LCC_FLAGS = --outdir results/out.lcc --tool_exec $(LCC)

.PHONY: all default test test-gcc clean test-gcc-full test-icc-full test-kcc-full test-cilcc-full

all: test-kcc

default: 

test-kcc-profile: default
	-$(RUNTEST) gcc.profile/exp.exp $(KCC_PROFILE_FLAGS)
	@cat results/out.kcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\),:/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,kcc,\3,\1/p' > kcc.profile.csv

test-kcc-all: default
	-$(RUNTEST) gcc.all/exp.exp $(KCC_FLAGS)
	@cat results/out.kcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\),:/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,kcc,\3,\1/p' > kcc.all.csv
test-gcc-all: default
	-$(RUNTEST) gcc.all/exp.exp $(GCC_FLAGS)
#echo "test,tool,phase,status,timeout" > gcc.full.csv
	@cat results/out.gcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,gcc,\3,\1/p' > gcc.all.csv
test-gcc34-all: default
	-$(RUNTEST) gcc.all/exp.exp $(GCC34_FLAGS)
	@cat results/out.gcc34/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,gcc34,\3,\1/p' > gcc34.all.csv
test-icc-all: default
	-$(RUNTEST) gcc.all/exp.exp $(ICC_FLAGS)
	@cat results/out.icc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,icc,\3,\1/p' > icc.all.csv
test-cilcc-all: default
	-$(RUNTEST) gcc.all/exp.exp $(CIL_FLAGS)
	@cat results/out.cilcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,cilcc,\3,\1/p' > cilcc.all.csv
test-clang-all: default
	-$(RUNTEST) gcc.all/exp.exp $(CLANG_FLAGS)
	@cat results/out.clang/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,clang,\3,\1/p' > clang.all.csv	
	
test-gcc-full: default
	-$(RUNTEST) gcc.full/full.exp $(GCC_FLAGS)
#echo "test,tool,phase,status,timeout" > gcc.full.csv
	@cat results/out.gcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,gcc,\3,\1/p' > gcc.full.csv
test-gcc34-full: default
	-$(RUNTEST) gcc.full/full.exp $(GCC34_FLAGS)
	@cat results/out.gcc34/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,gcc34,\3,\1/p' > gcc34.full.csv
test-icc-full: default
	-$(RUNTEST) gcc.full/full.exp $(ICC_FLAGS)
	@cat results/out.icc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,icc,\3,\1/p' > icc.full.csv
test-cilcc-full: default
	-$(RUNTEST) gcc.full/full.exp $(CIL_FLAGS)
	@cat results/out.cilcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,cilcc,\3,\1/p' > cilcc.full.csv
test-clang-full: default
	-$(RUNTEST) gcc.full/full.exp $(CLANG_FLAGS)
	@cat results/out.clang/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,clang,\3,\1/p' > clang.full.csv	

	
test-kcc-fast: default
	-$(RUNTEST) gcc.fast/exp.exp $(KCC_FLAGS)
	@cat results/out.kcc/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\),:/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,kcc,\3,\1/p' > kcc.fast.csv
test-kcc-slow: default
	-$(RUNTEST) gcc.slow/exp.exp --outdir results/out.kcc.slow --tool_exec $(KCC)
	@cat results/out.kcc.slow/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,kcc,\3,\1/p' > kcc.slow.csv
test-kcc-superSlow: default
	-$(RUNTEST) gcc.superSlow/exp.exp --outdir results/out.kcc.superSlow --tool_exec $(KCC)
	@cat results/out.kcc.superSlow/gcc.sum | sed -n 's/^\(.*\):/\1,:/p' | sed '/timed out\./{N;s/WARNING: program timed out\.\n\(.*\):/\1,TIMEOUT:/}' | sed -n 's/^\(.*\): gcc\..*\/\(.*\) \(.*\),/\2,kcc,\3,\1/p' > kcc.superSlow.csv


spreadsheet:
# sed "1 d;$$ d" kcc.fast.csv > kcc.fast.csv.tmp
# sed "1 d;$$ d" kcc.slow.csv > kcc.slow.csv.tmp
# sed "1 d;$$ d" kcc.superSlow.csv > kcc.superSlow.csv.tmp
	cat kcc.fast.csv kcc.slow.csv kcc.superSlow.csv > kcc.full.csv.tmp
	echo "test,tool,phase,status,timeout" > kcc.full.out
	sort -t , -k 1,1 -k 3,3 kcc.full.csv.tmp >> kcc.full.out
	echo "test,tool,phase,status,timeout" > gcc.full.out
	sort -t , -k 1,1 -k 3,3 gcc.full.csv >> gcc.full.out
	echo "test,tool,phase,status,timeout" > gcc34.full.out
	sort -t , -k 1,1 -k 3,3 gcc34.full.csv >> gcc34.full.out
	echo "test,tool,phase,status,timeout" > icc.full.out
	sort -t , -k 1,1 -k 3,3 icc.full.csv >> icc.full.out
	echo "test,tool,phase,status,timeout" > cilcc.full.out
	sort -t , -k 1,1 -k 3,3 cilcc.full.csv >> cilcc.full.out
	paste -d, gcc.full.out gcc34.full.out icc.full.out cilcc.full.out kcc.full.out > output.csv
	
clean:
	rm -f kcompile_* compilation.log gcc.log gcc.sum *.pre.gen a.out *.maude.tmp *-gen.maude *.prepre.gen *.gen.maude *-compiled.maude *.warnings.log
