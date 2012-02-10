module ISSUE 
  op ifFromArrayInBounds : #Int #Int #Nat -> #Bool 
  rule ifFromArrayInBounds(Offset:#Int,I:#Int, Len:#Nat)
    => true
  when Offset:#Int +Int I:#Int <=Nat Len:#Nat
end module
