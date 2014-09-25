#!/bin/bash


files=("sum" "collatz" "sum1" "sum_if" "primes")
extension=".imp"
indexed_dir=`pwd`"/indexed/"
normal_dir=`pwd`"/normal/"
begin=1
end=100



rm -rf ${indexed_dir}
rm -rf ${normal_dir}


mkdir ${indexed_dir}
mkdir ${normal_dir}

cd k 
# ant clean 2>&1			
# ant build

cd samples/java_rewrite_engine/tutorial/1_k/2_imp/indexing/
kompile --backend java imp.k -v

rm -rf *-log.txt

# kompile imp.k
for file in "${files[@]}"
do
echo $file

for i in `seq ${begin} ${end}`; do
 krun --backend java --smt none ${file}${extension} --index 2>&1 | tee -a ${file}"-indexed-log.txt"
done

VAR=`grep "\[" ${file}"-indexed-log.txt"` # ${indexed_dir} #>> ${file}"-indexed-times.txt"
echo -e $VAR > ${file}"-indexed-times.txt"
mv ${file}"-indexed-times.txt" ${indexed_dir}
mv ${file}"-indexed-log.txt" ${indexed_dir}

for i in `seq ${begin} ${end}`; do
 krun --backend java --smt none ${file}${extension} 2>&1 | tee -a ${file}"-normal-log.txt"
done

VAR=`grep "\[" ${file}"-normal-log.txt"`
echo -e $VAR > ${file}"-normal-times.txt"
#grep "\[" ${file}"-normal-log.txt" ${normal_dir} >> ${file}"-normal-times.txt"
mv ${file}"-normal-times.txt" ${normal_dir}
mv ${file}"-normal-log.txt" ${normal_dir}

done

cd -