#echo -en "\033[1;34m"
#echo "First, we need to compile the definition of KernelC"
#echo -en "\033[0m"
#echo -en "\033[1;34m"
#echo "This might take a while..."
#echo "kompile.pl kernelc"
#echo -en "\033[0m"
#kompile.pl kernelc
#cp kernelc-compiled.maude kernelc-compiled-demo.maude
#echo -en "\033[1;34m"
#echo -n "Done. Now let's compile pMonteCarlo" 
#echo -en "\033[0m"
#read
echo -en "\033[1;34m"
echo "kcompile-program.sh pMonteCarlo.k KERNELC  KERNELC-MONTE-CARLO pMonteCarlo"
echo -en "\033[0m"
cp pMonteCarlo.c pMonteCarlo.k
kcompile-program.sh pMonteCarlo.k KERNELC  KERNELC-MONTE-CARLO pMonteCarlo
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pMonteCarlo) ."
echo -en "\033[0m"
read
krunf.sh runMonteCarlo.maude
