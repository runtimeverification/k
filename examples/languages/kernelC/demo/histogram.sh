for (( i=1 ; $i < $1 ; i = $i + 1 )) 
do
  echo -n "$i," 
  ./pMonteCarlo.sh $i | grep 0 | wc -l 
done
