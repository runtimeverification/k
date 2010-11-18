rm -f maudeProfileDBfile.sqlite
for file in gcc.profile/*.profile
do
	echo "Processing $file...";
	perl ../analyzeProfile.pl $file
done
# perl ../analyzeProfile.pl xxx -p > rules-info.csv
# perl ../analyzeProfile.pl xxx -c > files-info.csv
