echo -en "\033[1;34m"
echo -en "Let us first try detecting races on the Peterson algorithm"
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pPeterson -cmod KERNELC-RACE-DETECTION  -pmod KERNELC-PETERSON"
echo -en "\033[0m"
cp pPeterson.c pPeterson.k
kompile -pgm pPeterson -cmod KERNELC-RACE-DETECTION  -pmod KERNELC-PETERSON 
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pPeterson) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
maude checkDataracePeterson.maude | grep "< \(thread\|id\|race\|k\|fstack\) >"
echo -en "\033[1;34m"
echo -en "Well we knew there were races, as this is what the algorithm is about.
Let's revert to the standard definition re-compile, and check mutual exclusion"
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pPeterson -cmod KERNELC  -pmod KERNELC-PETERSON"
echo -en "\033[0m"
kompile -pgm pPeterson -cmod KERNELC  -pmod KERNELC-PETERSON 
echo -en "\033[1;34m"
echo -en "in Maude:  rewrite run('pPeterson) ."
echo -en "\033[0m"
maude runPeterson.maude | grep "< result >"
echo -en "\033[1;34m"
echo "Seems to work as expected (prints are not interleaved). Still, there could be more executions."
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -en "in Maude:  search run('pPeterson) =>! B:Bag ."
echo -en "\033[0m"
read
maude explorePeterson.maude | grep "< result >"
echo -en "\033[1;34m"
echo -n "Current definition guarantees mutual exclusion, because memory accesses are sequentialized (sequentially consistent).
Let's see what happens when using a relaxed memory model..."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "this might take a while"
echo "kompile.pl kernelc-relaxed"
echo -en "\033[0m"
kompile kernelc-relaxed >/dev/null
echo -en "\033[1;34m"
echo "kompile -pgm pPeterson -cmod KERNELC-RELAXED  -pmod KERNELC-PETERSON"
echo -en "\033[0m"
kompile -pgm pPeterson -cmod KERNELC-RELAXED  -pmod KERNELC-PETERSON 
echo -en "\033[1;34m"
echo "in Maude:  rewrite run('pPeterson) ."
echo -en "\033[0m"
maude runPeterson.maude | grep "< result >"
echo -en "\033[1;34m"
echo "seems fine.  how about exploring it?"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
maude explorePeterson.maude | grep "< result >"
echo -en "\033[1;34m"
echo "Since it is not datarace free it is not guaranteed to behave the same in a relaxed memory model.  In particular, mutual exclusion is not ensured. 
Demo done."
echo -en "\033[0m"
