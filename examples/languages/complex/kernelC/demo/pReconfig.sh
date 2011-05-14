RANDOM=$$
for (( i=0 ; $i < $1 ; i=$i+1 )) 
do 
  SEED=$SEED+$RANDOM
  let "SEED = SEED % 4294967296"
  maude -random-seed=$SEED runReconfig.maude | grep result 
done
echo "$i"
