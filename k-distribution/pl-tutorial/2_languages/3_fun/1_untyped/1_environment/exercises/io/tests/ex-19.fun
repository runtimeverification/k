let p x = print x; print "\n" ; x
and r = read
in (p (p (p r + r) + r) + r)
