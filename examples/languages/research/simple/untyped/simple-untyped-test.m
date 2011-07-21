load simple-untyped-compiled

***(
-------------------------------
--- Execute SIMPLE programs ---
-------------------------------

rew run('pFactorial) .
rew run('pCollatz) .
rew run('pSorting) .
rew run('pArrays, 
	    (ListItem(Int(6)(.List{K})) ListItem(Int(3)(.List{K}))
	     ListItem(Int(1)(.List{K})) ListItem(Int(2)(.List{K}))
                                        ListItem(Int(3)(.List{K}))
	     ListItem(Int(4)(.List{K})) ListItem(Int(5)(.List{K}))
                                        ListItem(Int(6)(.List{K}))
	     ListItem(Int(7)(.List{K})) ListItem(Int(8)(.List{K}))
                                        ListItem(Int(9)(.List{K}))
	     ListItem(Int(9)(.List{K})) ListItem(Int(8)(.List{K}))
                                        ListItem(Int(7)(.List{K}))
	     ListItem(Int(6)(.List{K})) ListItem(Int(5)(.List{K}))
                                        ListItem(Int(4)(.List{K}))
	     ListItem(Int(3)(.List{K})) ListItem(Int(2)(.List{K}))
                                        ListItem(Int(1)(.List{K}))
	    )) .
rew run('pExceptions1) .
rew run('pExceptions2) .
rew run('pExceptions3) .
rew run('pExceptions4) .
rew run('pExceptions5) .
rew run('pExceptions6) .
rew run('pExceptions7) .
rew run('pExceptions8) .
rew run('pExceptions9) .
rew run('pExceptions10) .
rew run('pExceptions11) .
rew run('pExceptions12) .
rew run('pExceptions13) .
rew run('pExceptions14) .
rew run('pExceptions15) .


------------------------------------------
--- Execute and search the state space ---
------------------------------------------

rew run('pThreads1) .
---search run('pThreads1) =>! B:Bag .  --- too many interleavings
rew run('pThreads2) .
---search run('pThreads2) =>! B:Bag .  --- 43 solutions
rew run('pThreads3) .
---search run('pThreads3) =>! B:Bag .
rew run('pThreads4) .
search run('pThreads4) =>! B:Bag .
rew run('pThreads5) .
---search run('pThreads5) =>! B:Bag .
rew run('pThreads6) .
---search run('pThreads6) =>! B:Bag .
rew run('pThreads7) .
---search run('pThreads7) =>! B:Bag .  --- infinitely many
rew run('pThreads8) .
search run('pThreads8) =>! B:Bag .
rew run('pThreads9) .
search run('pThreads9) =>! B:Bag .
rew run('pThreads10) .
search run('pThreads10) =>! B:Bag .

***)

---------------------------------
--- Search and Model checking ---
---------------------------------

select SIMPLE-UNTYPED .

mod DEKKER-PREDICATES is
  including SIMPLE-UNTYPED .
  including PL-MODEL-CHECKER-BUILTIN-MODULE .

  op cfg : Bag -> Model-Checker-State .
  op start : -> Model-Checker-State .
  eq start = cfg(run('pDekker)) .

  var X : Id .  var B : Bag .  var M1 M2 : Map .  var Loc : K .

  op enabled : Id -> Prop .
  eq cfg(< T > B
	   < genv > M1 Id X(.List{K}) |-> Loc </ genv >
           < store > M2 Loc |-> Int 1(.List{K}) </ store >
	 </ T >) LTL|= enabled(X) = true .
endm

reduce modelCheck(start, LTL[] LTL~(enabled(critical1) LTL/\ enabled(critical2))) .
