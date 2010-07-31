#!/bin/bash
MAIN_FILE=$1
W=$(identify -format "%[fx:w/72]\n" $MAIN_FILE-crop.pdf | sort -n| tail -1)
H=$(identify -format "%[fx:h/72]\n" $MAIN_FILE-crop.pdf | sort -n| tail -1)
echo "
\documentclass{article}
\usepackage{pdfpages}
\usepackage[papersize={${W}in,${H}in}]{geometry}

\begin{document}
\includepdf[pages=-,templatesize={${W}in}{${H}in}]{$MAIN_FILE-crop}
\end{document}
" | pdflatex --jobname=$MAIN_FILE
