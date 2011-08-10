echo -en "\033[1;34m"
echo "First, we need to compile the definition of KernelC"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo "This might take a while..."
echo "kompile kernelc"
echo -en "\033[0m"
cp ../*.k .
kompile kernelc
echo -en "\033[1;34m"
echo -n "Done. Now let's compile pReconfig" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -cfile kernelc-compiled-demo -pgm pReconfig.k -cmod KERNELC  -pmod KERNELC-RECONFIG "
echo -en "\033[0m"
cp pReconfig.c pReconfig.k
kompile -pgm pReconfig.k -cmod KERNELC  -pmod KERNELC-RECONFIG
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pReconfig) ."
echo -en "\033[0m"
read
maude runReconfig.maude |  grep "< result >"
