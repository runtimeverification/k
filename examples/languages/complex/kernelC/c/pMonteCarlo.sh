
for (( i=0 ; $i < $3 ; i=$i+1 )) 
do 
  (echo $i && cat $2) | $1
done
echo ""
