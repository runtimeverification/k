structure Test =
struct
fun f x = let
  fun f0 x y = x
  fun f1 x = f0 (f0 x)
  fun f2 x = f1 (f1 x)
  fun f3 x = f2 (f2 x)
  fun f4 x = f3 (f3 x)
  fun f5 x = f4 (f4 x)
  fun f6 x = f5 (f5 x)
  fun f7 x = f6 (f6 x)
  fun f8 x = f7 (f7 x)
  fun f9 x = f8 (f8 x)
  fun f10 x = f9 (f9 x)
  fun f11 x = f10 (f10 x)
  fun f12 x = f11 (f11 x)
  fun f13 x = f12 (f12 x)
in
  f13 x
end
end
