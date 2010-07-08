kmod PI-IO-PROGRAMS is including PI-IO-SYNTAX + PI-PROGRAMS
  op p2 : -> Proc
  macro p2 = receive x on read . send x on print . ()
  
  op p3 : -> Proc
  macro p3 = replicate p2 
  
  op p4 : -> Proc
  ops a b c onx ony : -> Id
  macro p4 =  (replicate receive c on b . (receive a on x .  send onx on c .  ()  +  receive a on y .  send ony on c .  ()) )   ||  (replicate receive a on read .  send c on b . send a on a .  ()  ||  replicate receive a on c .  send a on print .  () )
endkm