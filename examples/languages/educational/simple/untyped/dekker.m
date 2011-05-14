load simple-untyped-compiled
load ../../../k-model-checker
select SIMPLE-UNTYPED .


mod MODEL-CHECK-TEST is
	including SIMPLE-UNTYPED .
	including PL-MODEL-CHECKER .
	op modelBag : -> Bag .
	eq modelBag = run('pDekker) .
	op Start : -> Model-Checker-State .
	op state : Bag -> Model-Checker-State .
	eq Start = state(modelBag) .
	
	op set : Id -> Prop .
	--- eq state(
		--- B0:Bag
		--- < T > 
			--- B1:Bag
			--- < genv > 
				--- M0:Map
				--- Id X:Id(.List{K}) |-> Loc:K
			--- </ genv >
			--- < mem > 
				--- M1:Map  
				--- Loc:K |-> Rat piece(1, 8)(.List{K})
			--- </ mem >
		--- </ T >	
	--- ) |= set(X:Id) = true .
	
	op enabled : Id -> Prop .
	eq state(
		B0:Bag
		< T > 
			B1:Bag
			< threads >
				B2:Bag
				< thread >
					B3:Bag
					< k > 'Apply('Closure(Id X:Id(.List{K}),, K0:K,, K1:K),, K3:K) ~> K:K </ k >
				</ thread >
			</ threads >
		</ T >
	) |= enabled(X:Id) = true .
	--- 'Apply('Closure(Id critical2(.List{K}),, K0:K,, K1:K),, K3:K) ~> K:K
	
	--- op finishWith : Nat -> Prop .
	--- eq state(
		--- B0:Bag
		--- < resultValue > 'tv(Rat N:Nat(.List{K}),, Base-Type int(.List{K})) </ resultValue >	
	--- ) |= finishWith(N:Nat) = true .
endm

--- rew run('pDekker) .



red modelCheck(Start, [] ~ (enabled(critical1) /\ enabled(critical2))) .

---search modelBag =>! B:Bag . --- mutual exclusion and no deadlock
--- red modelCheck(Start, <> (set(done1) /\ set(done2))) .
--- red modelCheck(Start, <> (set(done1) )) .
--- red modelCheck(Start, <> enabled(critical)) .
 ---red modelCheck(Start, <> enabled(dekker1)) .
--- red modelCheck(Start, [] ~ (enabled(dekker1) /\ enabled(dekker2))) .
---red modelCheck(Start, (<> enabled(task1) /\ <> enabled(task2))) .
--- red modelCheck(Start, <> finishWith(10)) .
---red modelCheck(Start, (<> enabled(dekker1) /\ <> enabled(dekker2)) -> (<> enabled(critical1) /\ <> enabled(critical2))) .
