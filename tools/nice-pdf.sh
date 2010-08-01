#!/bin/bash
MAIN_FILE=$1
BBOX=$(grep -o "BoundingBox: [0-9. ]*" *.epsi)
W=$(echo "$BBOX" | sed 's/.* \([0-9.]*\) [0-9.]*$/\1/' |sort -n|tail -1)
H=$(echo "$BBOX" |sed 's/.* \([0-9.]*\)$/\1/' |sort -n | tail -1)
echo "
\documentclass{article}
\usepackage{pdfpages}
\usepackage[papersize={${W}px,${H}px}]{geometry}

\begin{document}
\includepdf[pages=-,templatesize={${W}px}{${H}px}]{$MAIN_FILE-crop}
\end{document}
" | pdflatex --jobname=$MAIN_FILE
