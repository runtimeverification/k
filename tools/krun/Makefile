install:
	@${MAKE} try-install || (echo -e '\e[91mNOTE: Please type `make clean` followed by `cabal update` and try again before reporting any errors.\e[0m'; false)

try-install:
#ifneq (,$(wildcard ${K_BASE}/tools/maude-hs))
#	@cd ${K_BASE}/tools/maude-hs; hg pull -u 
#else
#	@hg clone http://code.google.com/p/maude-hs ${K_BASE}/tools/maude-hs
#endif
#	@cd ${K_BASE}/tools/maude-hs; cabal install
	cabal update
	@cd ${K_BASE}/tools/language-k; cabal install
	@cd ${K_BASE}/tools/krun; cabal install
	@cp ${K_BASE}/tools/krun/dist/build/krun/krun ${K_BASE}/core

debug-vars:
	@echo "K_BASE is set to:"
	@echo ${K_BASE}
	@echo "Testing if ${K_BASE}/tools/maude-hs exists:"
ifneq (,$(wildcard ${K_BASE}/tools/maude-hs))
	@echo "It exists."
else
	@echo "It does not exist."
endif
	

clean:
	cd ${K_BASE}/tools/language-k; cabal clean
	cd ${K_BASE}/tools/krun; cabal clean
#	rm -rf ${K_BASE}/tools/maude-hs
