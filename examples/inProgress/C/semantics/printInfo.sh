echo -e "lines\twords\tbytes"
echo "rules"
echo "equations"
echo "everything"
echo "------------------------"
echo "common-c-statements"
cat common-c-statements.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-statements.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-statements.maude | perl maudeloc.pl | wc
echo "common-c-expressions"
cat common-c-expressions.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-expressions.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-expressions.maude | perl maudeloc.pl | wc
echo
echo "common-c-standard-lib"
cat common-c-standard-lib.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-standard-lib.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-standard-lib.maude | perl maudeloc.pl | wc
echo
echo "common-c-conversions"
cat common-c-conversions.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-conversions.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-conversions.maude | perl maudeloc.pl | wc
echo "common-c-semantics"
cat common-c-semantics.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-semantics.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-semantics.maude | perl maudeloc.pl | wc
echo "common-c-typing"
cat common-c-typing.maude | perl maudeloc.pl | grep "rule" | wc
cat common-c-typing.maude | perl maudeloc.pl | grep "eq " | wc
cat common-c-typing.maude | perl maudeloc.pl | wc
echo "dynamic-c-semantics"
cat dynamic-c-semantics.maude | perl maudeloc.pl | grep "rule" | wc
cat dynamic-c-semantics.maude | perl maudeloc.pl | grep "eq " | wc
cat dynamic-c-semantics.maude | perl maudeloc.pl | wc