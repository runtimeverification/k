echo -en "\033[1;34m"
echo "First, we need to compile the definition of KernelC"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo "This might take a while..."
echo "kompile.pl kernelc"
echo -en "\033[0m"
kompile.pl kernelc
cp kernelc-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo -n "Done. Now let's compile pAccount" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kcompile-program.sh pAccount.k KERNELC  KERNELC-ACCOUNT pAccount"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kcompile-program.sh pAccount.k KERNELC  KERNELC-ACCOUNT pAccount
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pAccount) ."
echo -en "\033[0m"
read
krunf.sh runAccount.maude
echo -en "\033[1;34m"
echo "Produces the expected output.  But still, is it the only one?"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
krunf.sh exploreAccount.maude
echo -en "\033[1;34m"
echo -n "Something is wrong.  Maybe a datarace?  We need more powerful tools.
Compile the datarace detector, recompile account for it, then search for dataraces."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "this might take a while"
echo "kompile.pl kernelc-race-detection"
echo -en "\033[0m"
kompile.pl kernelc-race-detection >/dev/null
cp kernelc-race-detection-compiled.maude kernelc-compiled-demo.maude
echo -en "\033[1;34m"
echo "kcompile-program.sh pAccount.k KERNELC-RACE-DETECTION  KERNELC-ACCOUNT pAccount"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kcompile-program.sh pAccount.k KERNELC-RACE-DETECTION  KERNELC-ACCOUNT pAccount
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
krunf.sh checkDataraceAccount.maude
echo -en "\033[1;34m"
echo -n "datarace on b in transfer. go fix it, recompile, then re-check for dataraces."
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kcompile-program.sh pAccount.k KERNELC-RACE-DETECTION  KERNELC-ACCOUNT pAccount"
echo -en "\033[0m"
cp pAccount.c pAccount.k
kcompile-program.sh pAccount.k KERNELC-RACE-DETECTION  KERNELC-ACCOUNT pAccount
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
krunf.sh checkDataraceAccount.maude
echo -en "\033[1;34m"
echo "It is correct.  Are you sure?  Lets' check for deadlocks."
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search[1] run('pAccount) =>! <T> B:Bag </T> ."
echo -en "\033[0m"
read
krunf.sh checkDeadlockAccount.maude
echo -en "\033[1;34m"
echo -n "Need a better fix. Resource ordering? fix, recompile, re-check dataraces"
echo -en "\033[0m"
read
cp pAccount.c pAccount.k
kcompile-program.sh pAccount.k KERNELC-RACE-DETECTION  KERNELC-ACCOUNT pAccount
echo -en "\033[1;34m"
echo "in Maude:  search[1] run('pAccount) =>* <raceDetected> B:Bag </raceDetected> ."
echo -en "\033[0m"
krunf.sh checkDataraceAccount.maude
echo -en "\033[1;34m"
echo "Good. Now deadlocks"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search[1] run('pAccount) =>! <T> B:Bag </T> ."
echo -en "\033[0m"
read
krunf.sh checkDeadlockAccount.maude
echo -en "\033[1;34m"
echo "Very good. now check again all possible outputs"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  search run('pAccount) =>! B:Bag ."
echo -en "\033[0m"
read
krunf.sh exploreAccount.maude
echo -en "\033[1;34m"
echo "Deterministic. Excellent. Demo done. Implement it at you favorite bank :-)"
echo -en "\033[0m"
