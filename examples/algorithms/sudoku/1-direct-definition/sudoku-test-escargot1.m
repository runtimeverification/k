load sudoku-compiled.maude
---rew easy .       --- should find the solution, search is not necessary
---rew escargot1 .  --- should not be able to find the solution, search is needed
search [1] escargot1 =>! < T > Bs:Bag  </ T > .
q
