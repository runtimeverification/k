echo -en "\033[1;34m"
echo -n "Let's compile pBST" 
echo -en "\033[0m"
read
echo -en "\033[1;34m"
echo "kompile -pgm pBST -cmod KERNELC -pmod KERNELC-BST"
echo -en "\033[0m"
cp pBST.c pBST.k
kompile -pgm pBST -cmod KERNELC -pmod KERNELC-BST 
echo -en "\033[1;34m"
echo "Done. Now, let's execute it"
echo -en "\033[0m"
echo -en "\033[1;34m"
echo -n "in Maude:  rewrite run('pBST) ."
echo -en "\033[0m"
read
maude runBST.maude | grep "< result >"
