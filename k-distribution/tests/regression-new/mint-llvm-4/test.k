module TEST

imports INT
imports MINT
imports BYTES
imports BOOL
imports LIST
imports K-EQUAL

    syntax MInt{64}
    syntax MInt{256}

    // Fixtures

    syntax Bytes ::= "bytesString1" [macro]
                   | "bytesString2" [macro]

    rule bytesString1 => // Bytes must be 256 bits (32 bytes) for some tests
        b"\x1d)0\xdd\xcc#\xeb\x14)Q\x8bAG\xcf\xd46\xa7\xdb\x8f\xc6&\xc1=N\xb6\xa4\x81%\xc2\xd2\xf4o"
    rule bytesString2 =>
        b"a\x00\x1b`\x00\x81`\x0b\x829\xf3`\x01`\x01Us\x8a\n\x19X\x951iBP\xd5p\x04"


    syntax List ::= "listOfMInt" [macro]
    rule listOfMInt => ListItem(2p64) (ListItem(3p64) (ListItem(4p64) .List))

    syntax MInt{256} ::= "mintValue" [function]
    rule mintValue => 13189850602041981829950296977395610463010118185856010131061817836684537164911p256

    syntax Int ::= "intValue" [function]
    rule intValue => 13189850602041981829950296977395610463010118185856010131061817836684537164911


    // Tests Syntax
    syntax Bool ::= "testBytes2MInt"      [function]
                  | "testMInt2Bytes"      [function]
                  | "testLengthBytes"     [function]
                  | "testBytesGet"        [function]
                  | "testBytesUpdate"     [function]
                  | "getMInt"             [function]
                  | "testListSize"        [function]
                  | "testListUpdate"      [function]
                  | "testMIntPow"         [function]
                  | "testMIntPowZero"     [function]
                  | "testMIntPowOne"      [function]
                  | "testMIntPowNegative" [function]
                  | "testMIntPowAll"      [function]
                  | "testPadLeftBytes"    [function]
                  | "testPadRightBytes"   [function]
                  | "testSubstrBytes"     [function]
                  | "testReplaceAtBytes"  [function]


    // Tests Rules
    rule testMInt2Bytes =>  // Only supporting 256-bit MInt for this test in Big Endian format
        MInt2Bytes(mintValue) ==K Int2Bytes(intValue, BE, Unsigned) andBool
        MInt2Bytes(mintValue) ==K bytesString1

    rule testBytes2MInt => // Only supporting 256-bit MInt for this test in Big Endian format
        Bytes2MInt(bytesString1)::MInt{256} ==MInt Int2MInt(Bytes2Int(bytesString1, BE, Unsigned))

    rule testLengthBytes =>
        lengthBytes(bytesString1):Int ==Int MInt2Unsigned(lengthBytes(bytesString1):MInt{64}) andBool
        lengthBytes(bytesString1):Int ==Int MInt2Unsigned(lengthBytes(bytesString1):MInt{256})

    rule testBytesGet =>
        {bytesString2[2p64]}:>MInt{64} ==MInt Int2MInt(bytesString2[2]) andBool
        {bytesString2[2p256]}:>MInt{256} ==MInt Int2MInt(bytesString2[2])

    rule testBytesUpdate =>
        bytesString2[2p64 <- 10p64] ==K bytesString2[2 <- 10] andBool
        bytesString2[2p256 <- 10p256] ==K bytesString2[2 <- 10]

    rule getMInt => listOfMInt[1]:KItem ==K listOfMInt[1p64]:KItem andBool
                    listOfMInt[1]:KItem ==K listOfMInt[1p256]:KItem

    rule testListSize =>
        size(listOfMInt) ==Int MInt2Unsigned(size(listOfMInt)::MInt{64}) andBool
        size(listOfMInt) ==Int MInt2Unsigned(size(listOfMInt)::MInt{256})

    // This function only support MInt{64} for now, use MInt{256} can cause undefined behavior
    rule testListUpdate => listOfMInt[2p64 <- 10p64] ==K listOfMInt[2 <- 10p64]

    rule testMIntPow =>
        MInt2Unsigned(2p256 ^MInt 255p256) ==Int 2 ^Int 255 andBool
        MInt2Unsigned(2p64 ^MInt 63p64) ==Int 2 ^Int 63

    rule testMIntPowZero =>
        MInt2Unsigned(2p256 ^MInt 0p256) ==Int 1 andBool
        MInt2Unsigned(2p64 ^MInt 0p64) ==Int 1

    rule testMIntPowOne =>
        MInt2Unsigned(2p256 ^MInt 1p256) ==Int 2 andBool
        MInt2Unsigned(2p64 ^MInt 1p64) ==Int 2

    rule testMIntPowNegative =>
        MInt2Signed(2p256 ^MInt -10p256) ==Int 0 andBool
        MInt2Signed(2p64 ^MInt -10p64) ==Int 0

    // MInt exponenciation always assume unsigned results, except for the
    // exponentiation by zero, which is always 1.
    rule testMIntPowAll =>
        testMIntPow andBool testMIntPowZero andBool
        testMIntPowOne andBool testMIntPowNegative

    rule testPadLeftBytes =>
        padLeftBytes(bytesString1, 50, 15) ==K padLeftBytes(bytesString1, 50p256, 15p256) andBool
        padLeftBytes(bytesString1, 50, 15) ==K padLeftBytes(bytesString1, 50p64, 15p64)

    rule testPadRightBytes =>
        padRightBytes(bytesString1, 50, 15) ==K padRightBytes(bytesString1, 50p256, 15p256) andBool
        padRightBytes(bytesString1, 50, 15) ==K padRightBytes(bytesString1, 50p64, 15p64)

    rule testSubstrBytes =>
        substrBytes(bytesString1, 0, 5) ==K substrBytes(bytesString1, 0p64, 5p64) andBool
        substrBytes(bytesString1, 0, 5) ==K substrBytes(bytesString1, 0p256, 5p256)

    rule testReplaceAtBytes =>
        replaceAtBytes(bytesString1, 2, String2Bytes("test")) ==K
        replaceAtBytes(bytesString1, 2p64, String2Bytes("test")) andBool
        replaceAtBytes(bytesString1, 2, String2Bytes("test")) ==K
        replaceAtBytes(bytesString1, 2p256, String2Bytes("test"))

endmodule