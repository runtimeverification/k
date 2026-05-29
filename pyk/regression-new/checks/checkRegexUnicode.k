// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKREGEXUNICODE
syntax lexical Foo = r"[^a😊][😦-ab-🙁]"
syntax Bar ::= r"[^a😊][😦-ab-🙁]" [token]
endmodule
