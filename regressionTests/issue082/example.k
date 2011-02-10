// first line
// second line
// third line
//in previous bug if "in" was inside this would fail another in


in ../../k-prelude
kmod ISSUE082 is // another comment
	including K //
    configuration <T> <k> .K </k> /* multiline on single line */ </T>
    //"and another comment"
    // something like ---"something" would fail (maude bug)

/*
first line of multiline comment
second line of multiline comment
1 2*/  op test : /*3 4*/ -> String
    eq test = "<test>"
endkm
