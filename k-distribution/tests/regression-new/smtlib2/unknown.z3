// Fermat's last theorem for n = 3
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
( assert ( > a 0 ))
( assert ( > b 0 ))
( assert ( > c 0 ))
( assert ( = ( * c c c)
             ( + (* a a a) (* b b b))))
