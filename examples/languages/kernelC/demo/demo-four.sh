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
echo -n "Done. Now let's compile pBST" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kcompile-program.sh pBST.k KERNELC  KERNELC-BST pBST"
echo -en "\033[0m"
cp pBST.c pBST.k
kcompile-program.sh pBST.k KERNELC  KERNELC-BST pBST
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pBST) ."
echo -en "\033[0m"
read
krunf.sh runBST.maude
