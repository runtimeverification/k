echo -en "\033[1;34m"
echo "First, we need to compile the definition of KernelC"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo "This might take a while..."
echo "kompile kernelc"
echo -en "\033[0m"
cp ../*.k .
kompile kernelc
cp kernelc-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo -n "Done. Now let's compile pAccount" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pAccount  -cmod KERNELC -pmod KERNELC-ACCOUNT"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kompile -pgm pAccount  -cmod KERNELC -pmod KERNELC-ACCOUNT 
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pAccount) ."
echo -en "\033[0m"
read
maude runAccount.maude | grep "< result >"
echo -en "\033[1;34m"
echo "Produces the expected output.  But still, is it the only one?"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
maude exploreAccount.maude | grep "< result >"
echo -en "\033[1;34m"
echo -n "Something is wrong.  Maybe a datarace?  We need more powerful tools.
Compile the datarace detector, recompile account for it, then search for dataraces."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "this might take a while"
echo "kompile kernelc-race-detection"
echo -en "\033[0m"
kompile kernelc-race-detection 2>/dev/null
cp kernelc-race-detection-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo "kompile -pgm pAccount  -cmod KERNELC-RACE-DETECTION -pmod KERNELC-ACCOUNT"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kompile -pgm pAccount  -cmod KERNELC-RACE-DETECTION -pmod KERNELC-ACCOUNT 
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
maude checkDataraceAccount.maude | grep "< \(thread\|id\|race\|k\|fstack\) >"
echo -en "\033[1;34m"
echo -n "datarace on b in transfer. go fix it, recompile, then re-check for dataraces."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pAccount  -cmod KERNELC-RACE-DETECTION -pmod KERNELC-ACCOUNT"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kompile -pgm pAccount  -cmod KERNELC-RACE-DETECTION -pmod KERNELC-ACCOUNT
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
maude checkDataraceAccount.maude 
echo -en "\033[1;34m"
echo "It is correct.  Are you sure?  Lets' check for deadlocks."
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search[1] run('pAccount) =>! <T> B:Bag </T> ."
echo -en "\033[0m"
read
maude checkDeadlockAccount.maude | grep "< \(thread\|id\|race\|k\|fstack\) >"
echo -en "\033[1;34m"
echo -n "Need a better fix. Resource ordering? fix, recompile, re-check dataraces"
echo -en "\033[0m"
read
cp pAccount.c pAccount.k
kompile -pgm pAccount  -cmod KERNELC-RACE-DETECTION -pmod KERNELC-ACCOUNT 
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
maude checkDataraceAccount.maude
echo -en "\033[1;34m"
echo "Good. Now deadlocks"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search[1] run('pAccount) =>! <T> B:Bag </T> ."
echo -en "\033[0m"
read
maude checkDeadlockAccount.maude
echo -en "\033[1;34m"
echo "Very good. now check again all possible outputs"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
maude exploreAccount.maude | grep "< result >"
echo -en "\033[1;34m"
echo "Deterministic. Excellent. Demo done. Implement it at you favorite bank :-)"
echo -en "\033[0m"
