require /modules/basic-run
require /modules/k-visitor
require /modules/quote-unquote

require ../ids
require /modules/exp
require /modules/if
require /modules/substitution
require /modules/lambda
require /modules/mu
require /modules/seq
require /modules/ref
require /modules/io
require /modules/while
require programs

kmod RUN is including QUOTE-UNQUOTE-PROGRAMS + BASIC-RUN 
  configuration <T><k> .K </k> <nextId>0</nextId> <mem>.Map</mem> <nextLoc>0</nextLoc><in>.List</in><out>.List</out></T>
endkm
