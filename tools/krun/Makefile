install:
	cabal update
	cd ${K_BASE}/tools/language-k; cabal install
	cd ${K_BASE}/tools/krun; cabal install
	cp ${HOME}/.cabal/bin/krun ${K_BASE}/core

dev-install:
	cabal update
	hg clone http://code.google.com/p/maude-hs
	cd maude-hs; cabal install
	cd ${K_BASE}/tools/language-k; cabal install
	cd ${K_BASE}/tools/krun; cabal install
	cp ${HOME}/.cabal/bin/krun ${K_BASE}/core
	rm -rf maude-hs
