module ISSUE 

   declare sum : K K -> K
   define sum(X:#Int,0) => X
   define sum(0,Y:#Int) => Y
   define sum(X:#Int,Y:#Int) => X +Int Y
/*  should generate:
   op sum : K K -> K [metadata "function=()"]
   rule sum(X:#Int,0) => X  [metadata "function=()"]
   rule sum(0,Y:#Int) => Y [metadata "function=()"]
   rule sum(X:#Int,Y:#Int) => X +Int Y [metadata "function=()"]
*/
end module
