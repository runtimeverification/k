
sed -i 's|eq \(.*\) = \(.*\) \[metadata "heating"\] .|rl \1 => \2 \[metadata "heating"\] .|' $1