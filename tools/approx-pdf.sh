echo "Running LaTeX to approximate height"
cat $1.tex | sed 's/\\begin{document}/\\geometry{portrait,papersize={1200mm,11in},textwidth=1180mm}\\pagestyle{empty}\\begin{document}/ ; s/\\newpage/\\bigskip/g' | latex --jobname=$1 >/dev/null 
PAGES=$(grep -o "[0-9]\+ pages\?, " $1.log | grep -o "[0-9]*")
echo "We have $PAGES page(s)"
exit $PAGES
