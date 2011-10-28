-------------------------------------------------------------------
--- Lots of SIMPLE programs to be used first to test the syntax ---
--- and then to test the semantics.                             ---
-------------------------------------------------------------------

kmod SIMPLE-UNTYPED-PROGRAMS is including SIMPLE-UNTYPED-SYNTAX
  syntax #Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m 
              | n | o | p | q | r | s | t | u | v | w | x | y | z 
              | main | divide2 | collatz | dummy1 | dummy2 | init | reverse 
              | printAll | writeArray | insertionSort | bubbleSort | siftDown 
              | heapSort | map | done | root | bottom | maxChild | temp
              | numbers | size | readArray | printArray | mulArray | transArray

  syntax Stmts ::= pFactorial | pCollatz | pInsertionSort1 | pInsertionSort2
                 | pInsertionSort3 | pInsertionSort4 | pBubbleSort
                 | pHeapSort | pSorting | pex01 | pArrays  

	

--- programs to test non-deterministic evaluation

  syntax Stmts ::= pNondet
  macro pNondet =
    var x;
    function main() {
      x = 1 ;
      x = ++ x / (++ x / x);
      write(x);
}
--- 0
--- 1
--- 2
--- 3
--- undefined (gets stuck with division-by-zero at top of computation)


--- programs to test dynamic threads and synchronization

endkm
