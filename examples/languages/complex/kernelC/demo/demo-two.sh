echo -en "\033[1;34m"
echo -en "Let us first try detecting races on the Peterson algorithm"
echo -en "\033[0m"
read
cp kernelc-race-detection-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo "kcompile-program.sh pPeterson.k KERNELC_RACE-DETECTION KERNELC-PETERSON pPeterson"
echo -en "\033[0m"
cp pPeterson.c pPeterson.k
kcompile-program.sh pPeterson.k KERNELC-RACE-DETECTION  KERNELC-PETERSON pPeterson
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pPeterson) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
krunf.sh checkDataracePeterson.maude
echo -en "\033[1;34m"
echo -en "Well we knew there were races, as this is what the algorithm is about.
Let's revert to the standard definition re-compile, and check mutual exclusion"
echo -en "\033[0m"
read
cp kernelc-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo "kcompile-program.sh pPeterson.k KERNELC  KERNELC-PETERSON pPeterson"
echo -en "\033[0m"
kcompile-program.sh pPeterson.k KERNELC  KERNELC-PETERSON pPeterson
echo -en "\033[1;34m"
echo -en "in Maude:  rewrite run('pPeterson) ."
echo -en "\033[0m"
krunf.sh runPeterson.maude
echo -en "\033[1;34m"
echo "Seems to work as expected (prints are not interleaved). Still, there could be more executions."
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -en "in Maude:  search run('pPeterson) =>! B:Bag ."
echo -en "\033[0m"
read
krunf.sh explorePeterson.maude
echo -en "\033[1;34m"
echo -n "Current definition guarantees mutual exclusion, because memory accesses are sequentialized (sequentially consistent).
Let's see what happens when using a relaxed memory model..."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "this might take a while"
echo "kompile.pl kernelc-relaxed"
echo -en "\033[0m"
kompile.pl kernelc-relaxed >/dev/null
cp kernelc-relaxed-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo "kcompile-program.sh pPeterson.k KERNELC-RELAXED KERNELC-PETERSON pPeterson"
echo -en "\033[0m"
kcompile-program.sh pPeterson.k KERNELC-RELAXED  KERNELC-PETERSON pPeterson
echo -en "\033[1;34m"
echo "in Maude:  rewrite run('pPeterson) ."
echo -en "\033[0m"
krunf.sh runPeterson.maude
echo -en "\033[1;34m"
echo "seems fine.  how about exploring it?"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
krunf.sh explorePeterson.maude
echo -en "\033[1;34m"
echo "Since it is not datarace free it is not guaranteed to behave the same in a relaxed memory model.  In particular, mutual exclusion is not ensured. 
Demo done."
echo -en "\033[0m"
