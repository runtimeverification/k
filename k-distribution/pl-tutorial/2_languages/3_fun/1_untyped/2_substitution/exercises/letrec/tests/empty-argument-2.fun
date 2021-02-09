// testing empty argument

datatype nothing = Nothing

let x = 7
in let f Nothing = x
   in f Nothing

// 7
