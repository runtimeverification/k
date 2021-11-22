KLLVMLIB=$(abspath $(CURDIR)/../../../lib/kllvm)
KOMPILE_FLAGS=--llvm-kompile-library --output interpreter -ccopt $(KLLVMLIB)/llvm/main/main.ll
export KOMPILE_FLAGS

all:
	$(MAKE) -C ../imp-llvm clean
	$(MAKE) -C ../imp-llvm
	$(MAKE) -C ../imp-llvm clean
