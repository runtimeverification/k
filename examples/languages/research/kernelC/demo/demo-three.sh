echo -en "\033[1;34m"
echo -n "Let's compile pMonteCarlo" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pMonteCarlo -cmod KERNELC -pmod KERNELC-MONTE-CARLO"
echo -en "\033[0m"
cp pMonteCarlo.c pMonteCarlo.k
kompile -pgm pMonteCarlo -cmod KERNELC -pmod KERNELC-MONTE-CARLO
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pMonteCarlo) ."
echo -en "\033[0m"
read
maude runMonteCarlo.maude | grep "< result >"
