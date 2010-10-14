grep -lrm 1 "?Int\|!Int\|FreeInt\|Int\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?Int/IntPatternExistential/g" $line
perl -p -i -e "s/\!Int/IntFunctionExistential/g" $line
perl -p -i -e "s/FreeInt/IntUniversal/g" $line
perl -p -i -e "s/Int\++/IntSymbolic/g" $line
fi
rm temp.txt
echo "Done with Int"
grep -lrm 1 "?Seq\|!Seq\|FreeSeq\|Seq\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?Seq/SeqPatternExistential/g" $line
perl -p -i -e "s/\!Seq/SeqFunctionExistential/g" $line
perl -p -i -e "s/FreeSeq/SeqUniversal/g" $line
perl -p -i -e "s/Seq\++/SeqSymbolic/g" $line
fi
rm temp.txt
echo "Done with Seq"
grep -lrm 1 "?MapItem\|!MapItem\|FreeMapItem\|MapItem\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?MapItem/MapItemPatternExistential/g" $line
perl -p -i -e "s/\!MapItem/MapItemFunctionExistential/g" $line
perl -p -i -e "s/FreeMapItem/MapItemUniversal/g" $line
perl -p -i -e "s/MapItem\++/MapItemSymbolic/g" $line
fi
rm temp.txt
echo "Done with MapItem"
grep -lrm 1 "?MathObj\|!MathObj\|FreeMathObj\|MathObj\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?MathObj/MathObjPatternExistential/g" $line
perl -p -i -e "s/\!MathObj/MathObjFunctionExistential/g" $line
perl -p -i -e "s/FreeMathObj/MathObjUniversal/g" $line
perl -p -i -e "s/MathObj\++/MathObjSymbolic/g" $line
fi
rm temp.txt
echo "Done with MathObj"
grep -lrm 1 "?IntTree\|!IntTree\|FreeIntTree\|IntTree\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?IntTree/IntTreePatternExistential/g" $line
perl -p -i -e "s/\!IntTree/IntTreeFunctionExistential/g" $line
perl -p -i -e "s/FreeIntTree/IntTreeUniversal/g" $line
perl -p -i -e "s/IntTree\++/IntTreeSymbolic/g" $line
fi
rm temp.txt
echo "Done with IntTree"
grep -lrm 1 "?IntTreeSeq\|!IntTreeSeq\|FreeIntTreeSeq\|IntTreeSeq\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?IntTreeSeq/IntTreeSeqPatternExistential/g" $line
perl -p -i -e "s/\!IntTreeSeq/IntTreeSeqFunctionExistential/g" $line
perl -p -i -e "s/FreeIntTreeSeq/IntTreeSeqUniversal/g" $line
perl -p -i -e "s/IntTreeSeq\++/IntTreeSeqSymbolic/g" $line
fi
rm temp.txt
echo "Done with IntTreeSeq"
grep -lrm 1 "?IntBag\|!IntBag\|FreeIntBag\|IntBag\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?IntBag/IntBagPatternExistential/g" $line
perl -p -i -e "s/\!IntBag/IntBagFunctionExistential/g" $line
perl -p -i -e "s/FreeIntBag/IntBagUniversal/g" $line
perl -p -i -e "s/IntBag\++/IntBagSymbolic/g" $line
fi
rm temp.txt
echo "Done with IntBag"
grep -lrm 1 "?Graph\|!Graph\|FreeGraph\|Graph\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?Graph/GraphPatternExistential/g" $line
perl -p -i -e "s/\!Graph/GraphFunctionExistential/g" $line
perl -p -i -e "s/FreeGraph/GraphUniversal/g" $line
perl -p -i -e "s/Graph\++/GraphSymbolic/g" $line
fi
rm temp.txt
echo "Done with Graph"
grep -lrm 1 "?MSet\|!MSet\|FreeMSet\|MSet\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?MSet/MSetPatternExistential/g" $line
perl -p -i -e "s/\!MSet/MSetFunctionExistential/g" $line
perl -p -i -e "s/FreeMSet/MSetUniversal/g" $line
perl -p -i -e "s/MSet\++/MSetSymbolic/g" $line
fi
rm temp.txt
echo "Done with MSet"
grep -lrm 1 "?Tree\|!Tree\|FreeTree\|Tree\++" $1 > temp.txt
perl -p -i -e "s/\n/ /g" temp.txt
read line < temp.txt
if [ -n "$line" ] 
then perl -p -i -e "s/\?Tree/TreePatternExistential/g" $line
perl -p -i -e "s/\!Tree/TreeFunctionExistential/g" $line
perl -p -i -e "s/FreeTree/TreeUniversal/g" $line
perl -p -i -e "s/Tree\++/TreeSymbolic/g" $line
fi
rm temp.txt
echo "And now to modify the conditions in utils.maude..."
perl -p -i -e "s/if substrString(string(Q), 0, 1) ==Bool \"?\" ./if findString(string(Q), \"PatternExistential\", 0) >=Int 1 ./g" $1/utils.maude
perl -p -i -e "s/= if substrString(string(getType(QC)), 0, 4) ==Bool \"Free\" then/= if findString(string(getType(QC)), \"Universal\", 0) >=Int 1 then/g" $1/utils.maude
echo "You should be done!"
