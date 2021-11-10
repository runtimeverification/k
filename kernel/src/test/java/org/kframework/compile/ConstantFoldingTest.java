// Copyright (c) 21 K Team. All Rights Reserved.
package org.kframework.compile;

import org.junit.Before;
import org.junit.Test;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;
import org.kframework.utils.errorsystem.KEMException;

import java.math.BigInteger;
import java.util.function.BiFunction;
import java.util.function.Function;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

public class ConstantFoldingTest {

  private ConstantFolding cf;

  @Before
  public void setUp() {
    cf = new ConstantFolding();
    cf.setLoc(KSequence());
  }

  @Test
  public void testNot() {
    assertEquals(true, cf.BOOL_not(false));
    assertEquals(false, cf.BOOL_not(true));
  }

  public void assertBinBoolOp(boolean a, boolean b, boolean c, boolean d, BiFunction<Boolean, Boolean, Boolean> f) {
    assertEquals(a, f.apply(false, false));
    assertEquals(b, f.apply(false, true));
    assertEquals(c, f.apply(true, false));
    assertEquals(d, f.apply(true, true));
  }

  @Test
  public void testAnd() {
    assertBinBoolOp(false, false, false, true, cf::BOOL_and);
  }

  @Test
  public void testAndThen() {
    assertBinBoolOp(false, false, false, true, cf::BOOL_andThen);
  }

  @Test
  public void testXor() {
    assertBinBoolOp(false, true, true, false, cf::BOOL_xor);
  }

  @Test
  public void testOr() {
    assertBinBoolOp(false, true, true, true, cf::BOOL_or);
  }

  @Test
  public void testOrElse() {
    assertBinBoolOp(false, true, true, true, cf::BOOL_or);
  }

  @Test
  public void testImplies() {
    assertBinBoolOp(true, true, false, true, cf::BOOL_implies);
  }

  @Test
  public void testBoolEq() {
    assertBinBoolOp(true, false, false, true, cf::BOOL_eq);
  }

  @Test
  public void testBoolNe() {
    assertBinBoolOp(false, true, true, false, cf::BOOL_ne);
  }

  @Test
  public void testConcat() {
    assertEquals("", cf.STRING_concat("", ""));
    assertEquals("foo", cf.STRING_concat("foo", ""));
    assertEquals("foo", cf.STRING_concat("", "foo"));
    assertEquals("foo", cf.STRING_concat("f", "oo"));
  }

  @Test
  public void testLength() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_length(""));
    assertEquals(BigInteger.valueOf(3), cf.STRING_length("foo"));
    assertEquals(BigInteger.valueOf(1), cf.STRING_length("\udbff\udfff"));
  }

  @Test
  public void testChr() {
    assertEquals("\u0000", cf.STRING_chr(BigInteger.valueOf(0)));
    assertEquals(" ", cf.STRING_chr(BigInteger.valueOf(32)));
    assertEquals("a", cf.STRING_chr(BigInteger.valueOf(97)));
    assertEquals("\u1234", cf.STRING_chr(BigInteger.valueOf(0x1234)));
    assertEquals("\udbff\udfff", cf.STRING_chr(BigInteger.valueOf(0x10ffff)));
  }

  @Test(expected=KEMException.class)
  public void testChrError1() {
    cf.STRING_chr(BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testChrError2() {
    cf.STRING_chr(BigInteger.valueOf(0x110000));
  }

  @Test
  public void testOrd() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_ord("\u0000"));
    assertEquals(BigInteger.valueOf(32), cf.STRING_ord(" "));
    assertEquals(BigInteger.valueOf(97), cf.STRING_ord("a"));
    assertEquals(BigInteger.valueOf(0x1234), cf.STRING_ord("\u1234"));
    assertEquals(BigInteger.valueOf(0x10ffff), cf.STRING_ord("\udbff\udfff"));
  }

  @Test(expected=KEMException.class)
  public void testOrdError1() {
    cf.STRING_ord("");
  }

  @Test(expected=KEMException.class)
  public void testOrdError2() {
    cf.STRING_ord("foo");
  }

  @Test
  public void testSubstr() {
    assertEquals("", cf.STRING_substr("foo", BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals("", cf.STRING_substr("foo", BigInteger.valueOf(1), BigInteger.valueOf(1)));
    assertEquals("", cf.STRING_substr("foo", BigInteger.valueOf(2), BigInteger.valueOf(2)));
    assertEquals("f", cf.STRING_substr("foo", BigInteger.valueOf(0), BigInteger.valueOf(1)));
    assertEquals("fo", cf.STRING_substr("foo", BigInteger.valueOf(0), BigInteger.valueOf(2)));
    assertEquals("foo", cf.STRING_substr("foo", BigInteger.valueOf(0), BigInteger.valueOf(3)));
    assertEquals("oo", cf.STRING_substr("foo", BigInteger.valueOf(1), BigInteger.valueOf(3)));
    assertEquals("o", cf.STRING_substr("foo", BigInteger.valueOf(2), BigInteger.valueOf(3)));
    assertEquals("o", cf.STRING_substr("foo", BigInteger.valueOf(1), BigInteger.valueOf(2)));
  }

  @Test(expected=KEMException.class)
  public void testSubstrError1() {
    cf.STRING_substr("foo", BigInteger.valueOf(1), BigInteger.valueOf(4));
  }

  @Test(expected=KEMException.class)
  public void testSubstrError2() {
    cf.STRING_substr("foo", BigInteger.valueOf(4), BigInteger.valueOf(5));
  }

  @Test(expected=KEMException.class)
  public void testSubstrError3() {
    cf.STRING_substr("foo", BigInteger.valueOf(3), BigInteger.valueOf(1));
  }

  @Test(expected=KEMException.class)
  public void testSubstError4() {
    cf.STRING_substr("foo", BigInteger.valueOf(-1), BigInteger.valueOf(1));
  }

  @Test
  public void testFind() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_find("foo", "f", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_find("foo", "f", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(1), cf.STRING_find("foo", "o", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(1), cf.STRING_find("foo", "o", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(2), cf.STRING_find("foo", "o", BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(1), cf.STRING_find("foo", "oo", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_find("foo", "oo", BigInteger.valueOf(2)));
  }

  @Test(expected=KEMException.class)
  public void testFindError1() {
    cf.STRING_find("foo", "f", BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testFindError2() {
    cf.STRING_find("foo", "f", BigInteger.valueOf(4));
  }

  @Test
  public void testRFind() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_rfind("foo", "f", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(0), cf.STRING_rfind("foo", "f", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_rfind("foo", "o", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(1), cf.STRING_rfind("foo", "o", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(2), cf.STRING_rfind("foo", "o", BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_rfind("foo", "oo", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(1), cf.STRING_rfind("foo", "oo", BigInteger.valueOf(2)));
  }

  @Test(expected=KEMException.class)
  public void testRFindError1() {
    cf.STRING_rfind("foo", "f", BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testRFindError2() {
    cf.STRING_rfind("foo", "f", BigInteger.valueOf(4));
  }

  @Test
  public void testFindChar() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_findChar("sandwich", "sw", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(4), cf.STRING_findChar("sandwich", "sw", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_findChar("sandwich", "s", BigInteger.valueOf(1)));
  }

  @Test(expected=KEMException.class)
  public void testFindCharError1() {
    cf.STRING_findChar("foo", "f", BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testFindCharError2() {
    cf.STRING_findChar("foo", "f", BigInteger.valueOf(4));
  }

  @Test
  public void testRFindChar() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_rfindChar("sandwich", "sw", BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(0), cf.STRING_rfindChar("sandwich", "sw", BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(4), cf.STRING_rfindChar("sandwich", "sw", BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_rfindChar("sandwich", "w", BigInteger.valueOf(1)));
  }

  @Test(expected=KEMException.class)
  public void testRFindCharError1() {
    cf.STRING_rfindChar("foo", "f", BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testRFindCharError2() {
    cf.STRING_rfindChar("foo", "f", BigInteger.valueOf(4));
  }

  @Test
  public void testFloat2String() {
    assertEquals("Infinityp53x11", cf.STRING_float2string(FloatBuiltin.of(BigFloat.positiveInfinity(53), 11)));
    assertEquals("NaNp53x11", cf.STRING_float2string(FloatBuiltin.of(BigFloat.NaN(53), 11)));
    assertEquals("0e+00p53x11", cf.STRING_float2string(FloatBuiltin.of(BigFloat.zero(53), 11)));
    assertEquals("-0e+00p53x11", cf.STRING_float2string(FloatBuiltin.of(BigFloat.negativeZero(53), 11)));
    assertEquals("-Infinityp53x11", cf.STRING_float2string(FloatBuiltin.of(BigFloat.negativeInfinity(53), 11)));
    assertEquals("1.0000000000000001e-01p53x11", cf.STRING_float2string(FloatBuiltin.of(new BigFloat(0.1, BinaryMathContext.BINARY64), 11)));
  }

  @Test
  public void testString2Float() {
    assertEquals(FloatBuiltin.of(BigFloat.positiveInfinity(53), 11), cf.STRING_string2float("Infinity"));
    assertEquals(FloatBuiltin.of(BigFloat.positiveInfinity(24), 8), cf.STRING_string2float("Infinityf"));
    assertEquals(FloatBuiltin.of(BigFloat.positiveInfinity(10), 10), cf.STRING_string2float("Infinityp10x10"));
    assertEquals(FloatBuiltin.of(BigFloat.NaN(53), 11), cf.STRING_string2float("NaN"));
    assertEquals(FloatBuiltin.of(BigFloat.zero(53), 11), cf.STRING_string2float("0.0"));
    assertEquals(FloatBuiltin.of(BigFloat.zero(53), 11), cf.STRING_string2float("0e+00"));
    assertEquals(FloatBuiltin.of(BigFloat.zero(53), 11), cf.STRING_string2float("0e-00"));
    assertEquals(FloatBuiltin.of(BigFloat.negativeZero(53), 11), cf.STRING_string2float("-0.0"));
    assertEquals(FloatBuiltin.of(BigFloat.negativeInfinity(53), 11), cf.STRING_string2float("-Infinity"));
    assertEquals(FloatBuiltin.of(new BigFloat(0.1, BinaryMathContext.BINARY64), 11), cf.STRING_string2float("0.1"));
    assertEquals(FloatBuiltin.of(new BigFloat(0.1f, BinaryMathContext.BINARY32), 8), cf.STRING_string2float("0.1f"));
  }

  @Test(expected=KEMException.class)
  public void testString2FloatError() {
    cf.STRING_string2float("0.0.0");
  }

  @Test
  public void testInt2String() {
    assertEquals("0", cf.STRING_int2string(BigInteger.valueOf(0)));
    assertEquals("1", cf.STRING_int2string(BigInteger.valueOf(1)));
    assertEquals("-1", cf.STRING_int2string(BigInteger.valueOf(-1)));
    assertEquals("100000000000000000000", cf.STRING_int2string(new BigInteger("100000000000000000000")));
  }

  @Test
  public void testString2Int() {
    assertEquals(BigInteger.valueOf(0), cf.STRING_string2int("0"));
    assertEquals(BigInteger.valueOf(1), cf.STRING_string2int("1"));
    assertEquals(BigInteger.valueOf(1), cf.STRING_string2int("+1"));
    assertEquals(BigInteger.valueOf(-1), cf.STRING_string2int("-1"));
    assertEquals(new BigInteger("100000000000000000000"), cf.STRING_string2int("100000000000000000000"));
  }

  @Test(expected=KEMException.class)
  public void testString2IntError() {
    cf.STRING_string2int("0.0");
  }

  @Test
  public void testBase2String() {
    assertEquals("1234", cf.STRING_base2string(BigInteger.valueOf(0x1234), BigInteger.valueOf(16)));
    assertEquals("1234", cf.STRING_base2string(BigInteger.valueOf(01234), BigInteger.valueOf(8)));
    assertEquals("1234", cf.STRING_base2string(BigInteger.valueOf(1234), BigInteger.valueOf(10)));
    assertEquals("110", cf.STRING_base2string(BigInteger.valueOf(6), BigInteger.valueOf(2)));
    assertEquals("-110", cf.STRING_base2string(BigInteger.valueOf(-6), BigInteger.valueOf(2)));
    assertEquals("10", cf.STRING_base2string(BigInteger.valueOf(36), BigInteger.valueOf(36)));
  }

  @Test(expected=KEMException.class)
  public void testBase2StringError1() {
    cf.STRING_base2string(BigInteger.valueOf(0), BigInteger.valueOf(1));
  }

  @Test(expected=KEMException.class)
  public void testBase2StringError2() {
    cf.STRING_base2string(BigInteger.valueOf(0), BigInteger.valueOf(37));
  }

  @Test
  public void testString2Base() {
    assertEquals(BigInteger.valueOf(0x1234), cf.STRING_string2base("1234", BigInteger.valueOf(16)));
    assertEquals(BigInteger.valueOf(01234), cf.STRING_string2base("1234", BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(1234), cf.STRING_string2base("1234", BigInteger.valueOf(10)));
    assertEquals(BigInteger.valueOf(6), cf.STRING_string2base("110", BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(6), cf.STRING_string2base("+110", BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(-6), cf.STRING_string2base("-110", BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(36), cf.STRING_string2base("10", BigInteger.valueOf(36)));
  }

  @Test(expected=KEMException.class)
  public void testString2BaseError1() {
    cf.STRING_string2base("0", BigInteger.valueOf(1));
  }

  @Test(expected=KEMException.class)
  public void testString2BaseError2() {
    cf.STRING_string2base("0", BigInteger.valueOf(37));
  }

  @Test(expected=KEMException.class)
  public void testString2BaseError3() {
    cf.STRING_string2base("8", BigInteger.valueOf(8));
  }

  @Test(expected=KEMException.class)
  public void testString2BaseError4() {
    cf.STRING_string2base("g", BigInteger.valueOf(16));
  }

  @Test(expected=KEMException.class)
  public void testString2BaseError5() {
    cf.STRING_string2base("0.0", BigInteger.valueOf(2));
  }

  @Test
  public void testReplaceAll() {
    assertEquals("far", cf.STRING_replaceAll("foo", "oo", "ar"));
    assertEquals("feeee", cf.STRING_replaceAll("foo", "o", "ee"));
    assertEquals("foo", cf.STRING_replaceAll("foo", "bar", "baz"));
  }

  @Test
  public void testReplace() {
    assertEquals("far", cf.STRING_replace("foo", "oo", "ar", BigInteger.valueOf(1)));
    assertEquals("feeo", cf.STRING_replace("foo", "o", "ee", BigInteger.valueOf(1)));
    assertEquals("feeeeo", cf.STRING_replace("fooo", "o", "ee", BigInteger.valueOf(2)));
    assertEquals("foo", cf.STRING_replace("foo", "o", "ee", BigInteger.valueOf(0)));
    assertEquals("foo", cf.STRING_replace("foo", "bar", "baz", BigInteger.valueOf(0)));
  }

  @Test(expected=KEMException.class)
  public void testReplaceError1() {
    cf.STRING_replace("foo", "oo", "ar", BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testReplaceError2() {
    cf.STRING_replace("foo", "oo", "ar", BigInteger.valueOf(Long.MAX_VALUE));
  }

  @Test
  public void testReplaceFirst() {
    assertEquals("far", cf.STRING_replaceFirst("foo", "oo", "ar"));
    assertEquals("feeo", cf.STRING_replaceFirst("foo", "o", "ee"));
    assertEquals("foo", cf.STRING_replaceFirst("foo", "bar", "baz"));
  }

  @Test
  public void testCountOccurrences() {
    assertEquals(BigInteger.valueOf(1), cf.STRING_countAllOccurrences("foo", "oo"));
    assertEquals(BigInteger.valueOf(2), cf.STRING_countAllOccurrences("foo", "o"));
    assertEquals(BigInteger.valueOf(0), cf.STRING_countAllOccurrences("foo", "bar"));
  }

  @Test
  public void testStringEq() {
    assertEquals(true, cf.STRING_eq("", ""));
    assertEquals(false, cf.STRING_eq("", "foo"));
    assertEquals(false, cf.STRING_eq("foo", ""));
    assertEquals(true, cf.STRING_eq("foo", "foo"));
  }

  @Test
  public void testStringNe() {
    assertEquals(false, cf.STRING_ne("", ""));
    assertEquals(true, cf.STRING_ne("", "foo"));
    assertEquals(true, cf.STRING_ne("foo", ""));
    assertEquals(false, cf.STRING_ne("foo", "foo"));
  }

  @Test
  public void testStringLt() {
    assertEquals(true, cf.STRING_lt("", "a"));
    assertEquals(true, cf.STRING_lt("a", "b"));
    assertEquals(true, cf.STRING_lt("a", "aa"));
    assertEquals(true, cf.STRING_lt("aa", "b"));
    assertEquals(false, cf.STRING_lt("", ""));
    assertEquals(false, cf.STRING_lt("a", ""));
    assertEquals(false, cf.STRING_lt("b", "a"));
    assertEquals(false, cf.STRING_lt("aa", "a"));
    assertEquals(false, cf.STRING_lt("b", "aa"));
  }

  @Test
  public void testStringLe() {
    assertEquals(true, cf.STRING_le("", "a"));
    assertEquals(true, cf.STRING_le("a", "b"));
    assertEquals(true, cf.STRING_le("a", "aa"));
    assertEquals(true, cf.STRING_le("aa", "b"));
    assertEquals(true, cf.STRING_le("", ""));
    assertEquals(false, cf.STRING_le("a", ""));
    assertEquals(false, cf.STRING_le("b", "a"));
    assertEquals(false, cf.STRING_le("aa", "a"));
    assertEquals(false, cf.STRING_le("b", "aa"));
  }

  @Test
  public void testStringGt() {
    assertEquals(false, cf.STRING_gt("", "a"));
    assertEquals(false, cf.STRING_gt("a", "b"));
    assertEquals(false, cf.STRING_gt("a", "aa"));
    assertEquals(false, cf.STRING_gt("aa", "b"));
    assertEquals(false, cf.STRING_gt("", ""));
    assertEquals(true, cf.STRING_gt("a", ""));
    assertEquals(true, cf.STRING_gt("b", "a"));
    assertEquals(true, cf.STRING_gt("aa", "a"));
    assertEquals(true, cf.STRING_gt("b", "aa"));
  }

  @Test
  public void testStringGe() {
    assertEquals(false, cf.STRING_ge("", "a"));
    assertEquals(false, cf.STRING_ge("a", "b"));
    assertEquals(false, cf.STRING_ge("a", "aa"));
    assertEquals(false, cf.STRING_ge("aa", "b"));
    assertEquals(true, cf.STRING_ge("", ""));
    assertEquals(true, cf.STRING_ge("a", ""));
    assertEquals(true, cf.STRING_ge("b", "a"));
    assertEquals(true, cf.STRING_ge("aa", "a"));
    assertEquals(true, cf.STRING_ge("b", "aa"));
  }

  @Test
  public void testIntNot() {
    assertEquals(BigInteger.valueOf(-19), cf.INT_not(BigInteger.valueOf(18)));
  }

  @Test
  public void testIntPow() {
    assertEquals(BigInteger.valueOf(1), cf.INT_pow(BigInteger.valueOf(10), BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(10), cf.INT_pow(BigInteger.valueOf(10), BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(100), cf.INT_pow(BigInteger.valueOf(10), BigInteger.valueOf(2)));
  }

  @Test(expected=KEMException.class)
  public void testIntPowError() {
    cf.INT_pow(BigInteger.valueOf(10), BigInteger.valueOf(-1));
  }

  @Test
  public void testIntPowMod() {
    assertEquals(BigInteger.valueOf(1), cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(0), BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(3), cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(1), BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(2), cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(2), BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(5), cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(-1), BigInteger.valueOf(7)));
  }

  @Test(expected=KEMException.class)
  public void testIntPowModError1() {
    cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(1), BigInteger.valueOf(0));
  }

  @Test(expected=KEMException.class)
  public void testIntPowModError2() {
    cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(1), BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testIntPowModError3() {
    cf.INT_powmod(BigInteger.valueOf(10), BigInteger.valueOf(-1), BigInteger.valueOf(5));
  }

  @Test
  public void testIntMul() {
    assertEquals(BigInteger.valueOf(10), cf.INT_mul(BigInteger.valueOf(5), BigInteger.valueOf(2)));
  }

  @Test
  public void testIntTDiv() {
    assertEquals(BigInteger.valueOf(2), cf.INT_tdiv(BigInteger.valueOf(10), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(2), cf.INT_tdiv(BigInteger.valueOf(7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(-2), cf.INT_tdiv(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(-2), cf.INT_tdiv(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(2), cf.INT_tdiv(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
  }

  @Test(expected=KEMException.class)
  public void testIntTDivError() {
    cf.INT_tdiv(BigInteger.valueOf(10), BigInteger.valueOf(0));
  }

  @Test
  public void testIntTMod() {
    assertEquals(BigInteger.valueOf(0), cf.INT_tmod(BigInteger.valueOf(10), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(1), cf.INT_tmod(BigInteger.valueOf(7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(-1), cf.INT_tmod(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(1), cf.INT_tmod(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(-1), cf.INT_tmod(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
  }

  @Test(expected=KEMException.class)
  public void testIntTModError() {
    cf.INT_tmod(BigInteger.valueOf(10), BigInteger.valueOf(0));
  }

  @Test
  public void testIntEDiv() {
    assertEquals(BigInteger.valueOf(2), cf.INT_ediv(BigInteger.valueOf(10), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(2), cf.INT_ediv(BigInteger.valueOf(7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(-2), cf.INT_ediv(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(-3), cf.INT_ediv(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(3), cf.INT_ediv(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
  }

  @Test(expected=KEMException.class)
  public void testIntEDivError() {
    cf.INT_ediv(BigInteger.valueOf(10), BigInteger.valueOf(0));
  }

  @Test
  public void testIntEMod() {
    assertEquals(BigInteger.valueOf(0), cf.INT_emod(BigInteger.valueOf(10), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(1), cf.INT_emod(BigInteger.valueOf(7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(2), cf.INT_emod(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(1), cf.INT_emod(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(2), cf.INT_emod(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
  }

  @Test(expected=KEMException.class)
  public void testIntEModError() {
    cf.INT_emod(BigInteger.valueOf(10), BigInteger.valueOf(0));
  }

  @Test
  public void testIntAdd() {
    assertEquals(BigInteger.valueOf(5), cf.INT_add(BigInteger.valueOf(2), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(7), cf.INT_add(BigInteger.valueOf(10), BigInteger.valueOf(-3)));
  }

  @Test
  public void testIntSub() {
    assertEquals(BigInteger.valueOf(5), cf.INT_sub(BigInteger.valueOf(2), BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(7), cf.INT_sub(BigInteger.valueOf(10), BigInteger.valueOf(3)));
  }

  @Test
  public void testShr() {
    assertEquals(BigInteger.valueOf(8), cf.INT_shr(BigInteger.valueOf(32), BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(8), cf.INT_shr(BigInteger.valueOf(8), BigInteger.valueOf(0)));
  }

  @Test(expected=KEMException.class)
  public void testShrError() {
    cf.INT_shr(BigInteger.valueOf(8), BigInteger.valueOf(-2));
  }

  @Test
  public void testShl() {
    assertEquals(BigInteger.valueOf(32), cf.INT_shl(BigInteger.valueOf(8), BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(8), cf.INT_shl(BigInteger.valueOf(8), BigInteger.valueOf(0)));
  }

  @Test(expected=KEMException.class)
  public void testShlError() {
    cf.INT_shl(BigInteger.valueOf(32), BigInteger.valueOf(-2));
  }

  @Test
  public void testIntAnd() {
    assertEquals(BigInteger.valueOf(1), cf.INT_and(BigInteger.valueOf(9), BigInteger.valueOf(3)));
  }

  @Test
  public void testIntXor() {
    assertEquals(BigInteger.valueOf(10), cf.INT_xor(BigInteger.valueOf(9), BigInteger.valueOf(3)));
  }

  @Test
  public void testIntOr() {
    assertEquals(BigInteger.valueOf(11), cf.INT_or(BigInteger.valueOf(9), BigInteger.valueOf(3)));
  }

  @Test
  public void testIntMin() {
    assertEquals(BigInteger.valueOf(1), cf.INT_min(BigInteger.valueOf(1), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(1), cf.INT_min(BigInteger.valueOf(1), BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(-1), cf.INT_min(BigInteger.valueOf(-1), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntMax() {
    assertEquals(BigInteger.valueOf(3), cf.INT_max(BigInteger.valueOf(1), BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(1), cf.INT_max(BigInteger.valueOf(1), BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(1), cf.INT_max(BigInteger.valueOf(-1), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntAbs() {
    assertEquals(BigInteger.valueOf(3), cf.INT_abs(BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(3), cf.INT_abs(BigInteger.valueOf(-3)));
    assertEquals(BigInteger.valueOf(0), cf.INT_abs(BigInteger.valueOf(0)));
  }

  @Test
  public void testIntLog2() {
    assertEquals(BigInteger.valueOf(0), cf.INT_log2(BigInteger.valueOf(1)));
    assertEquals(BigInteger.valueOf(1), cf.INT_log2(BigInteger.valueOf(2)));
    assertEquals(BigInteger.valueOf(1), cf.INT_log2(BigInteger.valueOf(3)));
    assertEquals(BigInteger.valueOf(2), cf.INT_log2(BigInteger.valueOf(4)));
    assertEquals(BigInteger.valueOf(2), cf.INT_log2(BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(2), cf.INT_log2(BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(3), cf.INT_log2(BigInteger.valueOf(8)));
  }

  @Test(expected=KEMException.class)
  public void testIntLog2Error1() {
    cf.INT_log2(BigInteger.valueOf(0));
  }

  @Test(expected=KEMException.class)
  public void testIntLog2Error2() {
    cf.INT_log2(BigInteger.valueOf(-1));
  }

  @Test
  public void testBitRange() {
    assertEquals(BigInteger.valueOf(127), cf.INT_bitRange(BigInteger.valueOf(127), BigInteger.valueOf(0), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(255), cf.INT_bitRange(BigInteger.valueOf(255), BigInteger.valueOf(0), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(64), cf.INT_bitRange(BigInteger.valueOf(128), BigInteger.valueOf(1), BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(0), cf.INT_bitRange(BigInteger.valueOf(129), BigInteger.valueOf(1), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(0), cf.INT_bitRange(BigInteger.valueOf(128), BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals(BigInteger.valueOf(0), cf.INT_bitRange(new BigInteger("8040201008040201", 16), BigInteger.valueOf(256), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(12), cf.INT_bitRange(new BigInteger("-710567042938717889665411037832208781722350888143921263584927239275773573551204588944105336352942349727184887589413944684473529682801526123805453895275517072855048781056"), BigInteger.valueOf(32), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(56), cf.INT_bitRange(new BigInteger("697754608693466068295273213726275558775348389513141500672185545754018175722916164768735179047222610843044264325669307777729891642448846794142000"), BigInteger.valueOf(64), BigInteger.valueOf(8)));
  }

  @Test(expected=KEMException.class)
  public void testBitRangeError1() {
    cf.INT_bitRange(BigInteger.valueOf(128), BigInteger.valueOf(0), BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testBitRangeError2() {
    cf.INT_bitRange(BigInteger.valueOf(128), BigInteger.valueOf(-1), BigInteger.valueOf(8));
  }

  @Test
  public void testSignExtendBitRange() {
    assertEquals(BigInteger.valueOf(-1), cf.INT_signExtendBitRange(BigInteger.valueOf(255), BigInteger.valueOf(0), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(127), cf.INT_signExtendBitRange(BigInteger.valueOf(127), BigInteger.valueOf(0), BigInteger.valueOf(8)));
    assertEquals(BigInteger.valueOf(-64), cf.INT_signExtendBitRange(BigInteger.valueOf(128), BigInteger.valueOf(1), BigInteger.valueOf(7)));
    assertEquals(BigInteger.valueOf(0), cf.INT_signExtendBitRange(BigInteger.valueOf(129), BigInteger.valueOf(1), BigInteger.valueOf(5)));
    assertEquals(BigInteger.valueOf(0), cf.INT_signExtendBitRange(BigInteger.valueOf(128), BigInteger.valueOf(0), BigInteger.valueOf(0)));
  }

  @Test(expected=KEMException.class)
  public void testSignExtendBitRangeError1() {
    cf.INT_signExtendBitRange(BigInteger.valueOf(128), BigInteger.valueOf(0), BigInteger.valueOf(-1));
  }

  @Test(expected=KEMException.class)
  public void testSignExtendBitRangeError2() {
    cf.INT_signExtendBitRange(BigInteger.valueOf(128), BigInteger.valueOf(-1), BigInteger.valueOf(8));
  }

  @Test
  public void testIntLt() {
    assertEquals(true, cf.INT_lt(BigInteger.valueOf(-100), BigInteger.valueOf(-1)));
    assertEquals(true, cf.INT_lt(BigInteger.valueOf(-1), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_lt(BigInteger.valueOf(0), BigInteger.valueOf(1)));
    assertEquals(true, cf.INT_lt(BigInteger.valueOf(1), BigInteger.valueOf(100)));
    assertEquals(false, cf.INT_lt(BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_lt(BigInteger.valueOf(-1), BigInteger.valueOf(-100)));
    assertEquals(false, cf.INT_lt(BigInteger.valueOf(0), BigInteger.valueOf(-1)));
    assertEquals(false, cf.INT_lt(BigInteger.valueOf(1), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_lt(BigInteger.valueOf(100), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntLe() {
    assertEquals(true, cf.INT_le(BigInteger.valueOf(-100), BigInteger.valueOf(-1)));
    assertEquals(true, cf.INT_le(BigInteger.valueOf(-1), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_le(BigInteger.valueOf(0), BigInteger.valueOf(1)));
    assertEquals(true, cf.INT_le(BigInteger.valueOf(1), BigInteger.valueOf(100)));
    assertEquals(true, cf.INT_le(BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_le(BigInteger.valueOf(-1), BigInteger.valueOf(-100)));
    assertEquals(false, cf.INT_le(BigInteger.valueOf(0), BigInteger.valueOf(-1)));
    assertEquals(false, cf.INT_le(BigInteger.valueOf(1), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_le(BigInteger.valueOf(100), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntGt() {
    assertEquals(false, cf.INT_gt(BigInteger.valueOf(-100), BigInteger.valueOf(-1)));
    assertEquals(false, cf.INT_gt(BigInteger.valueOf(-1), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_gt(BigInteger.valueOf(0), BigInteger.valueOf(1)));
    assertEquals(false, cf.INT_gt(BigInteger.valueOf(1), BigInteger.valueOf(100)));
    assertEquals(false, cf.INT_gt(BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_gt(BigInteger.valueOf(-1), BigInteger.valueOf(-100)));
    assertEquals(true, cf.INT_gt(BigInteger.valueOf(0), BigInteger.valueOf(-1)));
    assertEquals(true, cf.INT_gt(BigInteger.valueOf(1), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_gt(BigInteger.valueOf(100), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntGe() {
    assertEquals(false, cf.INT_ge(BigInteger.valueOf(-100), BigInteger.valueOf(-1)));
    assertEquals(false, cf.INT_ge(BigInteger.valueOf(-1), BigInteger.valueOf(0)));
    assertEquals(false, cf.INT_ge(BigInteger.valueOf(0), BigInteger.valueOf(1)));
    assertEquals(false, cf.INT_ge(BigInteger.valueOf(1), BigInteger.valueOf(100)));
    assertEquals(true, cf.INT_ge(BigInteger.valueOf(0), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_ge(BigInteger.valueOf(-1), BigInteger.valueOf(-100)));
    assertEquals(true, cf.INT_ge(BigInteger.valueOf(0), BigInteger.valueOf(-1)));
    assertEquals(true, cf.INT_ge(BigInteger.valueOf(1), BigInteger.valueOf(0)));
    assertEquals(true, cf.INT_ge(BigInteger.valueOf(100), BigInteger.valueOf(1)));
  }

  @Test
  public void testIntEq() {
    assertEquals(true, cf.INT_eq(BigInteger.valueOf(1), BigInteger.valueOf(1)));
    assertEquals(false, cf.INT_eq(BigInteger.valueOf(1), BigInteger.valueOf(0)));
  }

  @Test
  public void testIntNe() {
    assertEquals(false, cf.INT_ne(BigInteger.valueOf(1), BigInteger.valueOf(1)));
    assertEquals(true, cf.INT_ne(BigInteger.valueOf(1), BigInteger.valueOf(0)));
  }

  @Test
  public void testPrecision() {
    assertEquals(BigInteger.valueOf(2), cf.FLOAT_precision(FloatBuiltin.of(new BigFloat(1.0, new BinaryMathContext(2, 8)), 8)));
    assertEquals(BigInteger.valueOf(24), cf.FLOAT_precision(FloatBuiltin.of(new BigFloat(1.0, BinaryMathContext.BINARY32), 8)));
  }

  @Test
  public void testExponentBits() {
    assertEquals(BigInteger.valueOf(8), cf.FLOAT_exponentBits(FloatBuiltin.of(new BigFloat(1.0, new BinaryMathContext(2, 8)), 8)));
    assertEquals(BigInteger.valueOf(11), cf.FLOAT_exponentBits(FloatBuiltin.of(new BigFloat(1.0, BinaryMathContext.BINARY64), 11)));
  }

  @Test
  public void testExponent() {
    assertEquals(BigInteger.valueOf(-127), cf.FLOAT_exponent(FloatBuiltin.of(new BigFloat(0.0, BinaryMathContext.BINARY32), 8)));
    assertEquals(BigInteger.valueOf(-127), cf.FLOAT_exponent(FloatBuiltin.of(new BigFloat(-0.0, BinaryMathContext.BINARY32), 8)));
    assertEquals(BigInteger.valueOf(128), cf.FLOAT_exponent(FloatBuiltin.of(new BigFloat(1.0/0.0, BinaryMathContext.BINARY32), 8)));
    assertEquals(BigInteger.valueOf(128), cf.FLOAT_exponent(FloatBuiltin.of(new BigFloat(0.0/0.0, BinaryMathContext.BINARY32), 8)));
    assertEquals(BigInteger.valueOf(2), cf.FLOAT_exponent(FloatBuiltin.of(new BigFloat(4.0, BinaryMathContext.BINARY32), 8)));
    assertEquals(BigInteger.valueOf(-127), cf.FLOAT_exponent(FloatBuiltin.of(BigFloat.minValue(24, BinaryMathContext.BINARY32.minExponent), 8)));
    assertEquals(BigInteger.valueOf(-126), cf.FLOAT_exponent(FloatBuiltin.of(BigFloat.minNormal(24, BinaryMathContext.BINARY32.minExponent), 8)));
  }

  private FloatBuiltin _float(float f) {
    return FloatBuiltin.of(new BigFloat(f, BinaryMathContext.BINARY32), 8);
  }

  private FloatBuiltin _double(double f) {
    return FloatBuiltin.of(new BigFloat(f, BinaryMathContext.BINARY64), 11);
  }

  @Test
  public void testSign() {
    assertEquals(false, cf.FLOAT_sign(_float(0.0f)));
    assertEquals(true, cf.FLOAT_sign(_float(-0.0f)));
    assertEquals(false, cf.FLOAT_sign(_float(1.0f/0.0f)));
    assertEquals(true, cf.FLOAT_sign(_float(-1.0f/0.0f)));
    assertEquals(false, cf.FLOAT_sign(_float(1.0f)));
    assertEquals(true, cf.FLOAT_sign(_float(-1.0f)));
    assertEquals(false, cf.FLOAT_sign(_float(3.0f)));
    assertEquals(false, cf.FLOAT_sign(_float(0.5f)));
    assertEquals(false, cf.FLOAT_sign(_float(0.0f/0.0f)));
  }

  @Test
  public void testIsNaN() {
    assertEquals(false, cf.FLOAT_isNaN(_float(0.0f)));
    assertEquals(false, cf.FLOAT_isNaN(_float(-0.0f)));
    assertEquals(false, cf.FLOAT_isNaN(_float(1.0f/0.0f)));
    assertEquals(true, cf.FLOAT_isNaN(_float(0.0f/0.0f)));
  }

  @Test
  public void testFloatNeg() {
    testUnaryOp(cf::FLOAT_neg, a -> -a);
  }

  private double[] refs = new double[] {0.0, -0.0, 1.0/0.0, -1.0/0.0, 1.0, -1.0, 3.0, 0.5, 0.0/0.0};

  private void testUnaryOp(Function<FloatBuiltin, FloatBuiltin> op, Function<Double, Double> refOp) {
    for (int i = 0; i < refs.length; i++) {
      FloatBuiltin result = op.apply(_double(refs[i]));
      double ref = refOp.apply(refs[i]);
      assertEquals(ref, result.doubleValue(), Double.MIN_VALUE);
    }
  }

  private void testBinaryOp(String operator, BiFunction<FloatBuiltin, FloatBuiltin, FloatBuiltin> op, BiFunction<Double, Double, Double> refOp) {
    for (int i = 0; i < refs.length; i++) {
      for (int j = 0; j < refs.length; j++) {
        FloatBuiltin result = op.apply(_double(refs[i]), _double(refs[j]));
        double ref = refOp.apply(refs[i], refs[j]);
        assertEquals("Operator " + operator + "(" + refs[i] + "," + refs[j] + ") failed", ref, result.doubleValue(), Double.MIN_VALUE);
      }
    }
  }

  private double pow(double a, double b) {
    if (a == 1.0) {
      return 1.0;
    }
    if (a == -1.0 && Double.isInfinite(b)) {
      return 1.0;
    }
    return Math.pow(a, b);
  }

  @Test
  public void testFloatPow() {
    testBinaryOp("pow", cf::FLOAT_pow, this::pow);
  }

  @Test
  public void testFloatMul() {
    testBinaryOp("*", cf::FLOAT_mul, (a, b) -> a*b);
  }

  @Test
  public void testFloatDiv() {
    testBinaryOp("/", cf::FLOAT_div, (a, b) -> a/b);
  }

  @Test
  public void testFloatRem() {
    testBinaryOp("%", cf::FLOAT_rem, (a, b) -> a%b);
  }

  @Test
  public void testFloatAdd() {
    testBinaryOp("+", cf::FLOAT_add, (a, b) -> a+b);
  }

  @Test
  public void testFloatSub() {
    testBinaryOp("-", cf::FLOAT_sub, (a, b) -> a-b);
  }

  @Test
  public void testRoot() {
    testUnaryOp(f -> cf.FLOAT_root(f, BigInteger.valueOf(2)), Math::sqrt);
  }

  @Test
  public void testFloatAbs() {
    testUnaryOp(cf::FLOAT_abs, Math::abs);
  }

  @Test
  public void testRound() {
    assertEquals(12.0, cf.FLOAT_round(_double(10.5), BigInteger.valueOf(2), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
    assertEquals(8.0, cf.FLOAT_round(_double(9.5), BigInteger.valueOf(2), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
    assertEquals(10.5f, cf.FLOAT_round(_double(10.5), BigInteger.valueOf(24), BigInteger.valueOf(8)).floatValue(), Double.MIN_VALUE);
    assertEquals(9.5f, cf.FLOAT_round(_double(9.5), BigInteger.valueOf(24), BigInteger.valueOf(8)).floatValue(), Double.MIN_VALUE);
  }

  @Test
  public void testFloor() {
    assertEquals(10.0f, cf.FLOAT_floor(_float(10.5f)).floatValue(), Double.MIN_VALUE);
  }

  @Test
  public void testCeil() {
    assertEquals(11.0f, cf.FLOAT_ceil(_float(10.5f)).floatValue(), Double.MIN_VALUE);
  }

  @Test
  public void testExp() {
    // testUnaryOp(cf::FLOAT_exp, Math::exp);
  }

  @Test
  public void testLog() {
    // testUnaryOp(cf::FLOAT_log, Math::log);
  }

  @Test
  public void testSin() {
    testUnaryOp(cf::FLOAT_sin, Math::sin);
  }

  @Test
  public void testCos() {
    testUnaryOp(cf::FLOAT_cos, Math::cos);
  }

  @Test
  public void testTan() {
    testUnaryOp(cf::FLOAT_tan, Math::tan);
  }

  @Test
  public void testAsin() {
    testUnaryOp(cf::FLOAT_asin, Math::asin);
  }

  @Test
  public void testAcos() {
    testUnaryOp(cf::FLOAT_acos, Math::acos);
  }

  @Test
  public void testAtan() {
    testUnaryOp(cf::FLOAT_atan, Math::atan);
  }

  @Test
  public void testAtan2() {
    testBinaryOp("atan2", cf::FLOAT_atan2, Math::atan2);
  }

  @Test
  public void testMax() {
    testBinaryOp("max", cf::FLOAT_max, this::max);
  }

  @Test
  public void testMin() {
    testBinaryOp("min", cf::FLOAT_min, this::min);
  }

  private double min(double a, double b) {
    if (a != a) {
      return b;
    }
    if (b != b) {
      return a;
    }
    return Math.min(a, b);
  }

  private double max(double a, double b) {
    if (a != a) {
      return b;
    }
    if (b != b) {
      return a;
    }
    return Math.max(a, b);
  }


  @Test
  public void testMaxValue() {
    assertEquals(Float.MAX_VALUE, cf.FLOAT_maxValue(BigInteger.valueOf(24), BigInteger.valueOf(8)).floatValue(), Double.MIN_VALUE);
    assertEquals(Double.MAX_VALUE, cf.FLOAT_maxValue(BigInteger.valueOf(53), BigInteger.valueOf(11)).doubleValue(), Double.MIN_VALUE);
  }

  @Test
  public void testMinValue() {
    assertEquals(Float.MIN_VALUE, cf.FLOAT_minValue(BigInteger.valueOf(24), BigInteger.valueOf(8)).floatValue(), Double.MIN_VALUE);
    assertEquals(Double.MIN_VALUE, cf.FLOAT_minValue(BigInteger.valueOf(53), BigInteger.valueOf(11)).doubleValue(), Double.MIN_VALUE);
  }

  private void testComparisonOp(String operator, BiFunction<FloatBuiltin, FloatBuiltin, Boolean> op, BiFunction<Double, Double, Boolean> refOp) {
    for (int i = 0; i < refs.length; i++) {
      for (int j = 0; j < refs.length; j++) {
        boolean result = op.apply(_double(refs[i]), _double(refs[j]));
        boolean ref = refOp.apply(refs[i], refs[j]);
        assertEquals("Operator " + operator + "(" + refs[i] + "," + refs[j] + ") failed", ref, result);
      }
    }
  }

  @Test
  public void testFloatLt() {
    testComparisonOp("<", cf::FLOAT_lt, (a, b) -> a < b);
  }

  @Test
  public void testFloatGt() {
    testComparisonOp(">", cf::FLOAT_gt, (a, b) -> a > b);
  }

  @Test
  public void testFloatLe() {
    testComparisonOp("<=", cf::FLOAT_le, (a, b) -> a <= b);
  }

  @Test
  public void testFloatGe() {
    testComparisonOp(">=", cf::FLOAT_ge, (a, b) -> a >= b);
  }

  @Test
  public void testFloatEq() {
    testComparisonOp("==", cf::FLOAT_eq, (a, b) -> a.doubleValue() == b.doubleValue());
  }

  @Test
  public void testFloatNe() {
    testComparisonOp("!=", cf::FLOAT_ne, (a, b) -> a.doubleValue() != b.doubleValue());
  }

  @Test
  public void testInt2Float() {
    assertEquals(8.0, cf.FLOAT_int2float(BigInteger.valueOf(9), BigInteger.valueOf(2), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
    assertEquals(12.0, cf.FLOAT_int2float(BigInteger.valueOf(11), BigInteger.valueOf(2), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
    assertEquals(8.0, cf.FLOAT_int2float(BigInteger.valueOf(10), BigInteger.valueOf(2), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
    assertEquals(10.0, cf.FLOAT_int2float(BigInteger.valueOf(10), BigInteger.valueOf(24), BigInteger.valueOf(8)).doubleValue(), Double.MIN_VALUE);
  }

  @Test
  public void testFloat2Int() {
    assertEquals(BigInteger.valueOf(10), cf.FLOAT_float2int(_double(10.5)));
    assertEquals(BigInteger.valueOf(10), cf.FLOAT_float2int(_double(9.5)));
  }
}
