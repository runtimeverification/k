red rule #typeof(#undefined) ==Bool #s("undefined") .
red rule #typeof(#null) ==Bool #s("object")
rule #typeof(#b(true)) ==Bool #s("boolean")
rule #typeof(#b(false)) ==Bool #s("boolean")
rule #typeof(#n(123)) ==Bool #s("number")
rule #typeof(#n(-123.4)) ==Bool #s("number")
rule #typeof(#n(0)) ==Bool #s("number")
rule #typeof(#zero(0)) ==Bool #s("number")
rule #typeof(#zero(1)) ==Bool #s("number")
rule #typeof(#zero(-1)) ==Bool #s("number")
rule #typeof(#infinity(1)) ==Bool #s("number")
rule #typeof(#infinity(-1)) ==Bool #s("number")
rule #typeof(#s("Hello world")) ==Bool #s("string")
rule #typeof({}) ==Bool #s("object") .
rule #typeof({"s" : 123}) ==Bool #s("object") .
rule #typeof([]) ==Bool #s("object") .
rule #typeof([1, 2, 3]) ==Bool #s("object") .

---rule #typeof(#function(_)) ==Bool #s("function")
