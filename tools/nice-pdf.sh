#!/bin/bash
MAIN_FILE=$1
BBOX=$(grep -o "BoundingBox: [0-9. ]*" *.eps)
W=$(echo "$BBOX" | sed 's/.* \([0-9.]*\) [0-9.]*$/\1/' |sort -n|tail -1)
#H=$(echo "$BBOX" |sed 's/.* \([0-9.]*\)$/\1/' |sort -n | tail -1)
echo "
\documentclass{article}
\usepackage{pdfpages}
\usepackage[papersize={${W}px,9.05in}]{geometry}

\begin{document}
\includepdf[pages=-,noautoscale,templatesize={${W}px}{9.05in}]{$MAIN_FILE-crop}
\end{document}
" | pdflatex --jobname=$MAIN_FILE
