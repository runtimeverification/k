#!/bin/bash
MAIN_FILE=$1
W=$(gs -dSAFER -dBATCH -dNOPAUSE -sDEVICE=bbox $MAIN_FILE-crop.pdf 2>&1 |grep %%BoundingBox |sed 's/.* \([0-9]*\) [0-9]*$/\1/' |sort -n|tail -1)
H=$(gs -dSAFER -dBATCH -dNOPAUSE -sDEVICE=bbox $MAIN_FILE-crop.pdf 2>&1 |grep %%BoundingBox |sed 's/.* \([0-9]*\)$/\1/' |sort -n | tail -1)
echo "
\documentclass{article}
\usepackage{pdfpages}
\usepackage[papersize={${W}px,${H}px}]{geometry}

\begin{document}
\includepdf[pages=-,templatesize={${W}px}{${H}px}]{$MAIN_FILE-crop}
\end{document}
" | pdflatex --jobname=$MAIN_FILE
