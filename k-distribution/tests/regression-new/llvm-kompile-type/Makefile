KLLVMLIB=$(abspath $(CURDIR)/../../../lib/kllvm)
KOMPILE_FLAGS=--llvm-kompile-type library --llvm-kompile-output interpreter -ccopt $(KLLVMLIB)/llvm/main/main.ll
export KOMPILE_FLAGS

all:
	$(MAKE) -C ../imp-llvm clean
	$(MAKE) -C ../imp-llvm
	$(MAKE) -C ../imp-llvm clean

clean:
update-results:
