// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.outer;

import java.util.Arrays;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.definition.regex.Regex;
import org.kframework.definition.regex.RegexBody;
import org.kframework.definition.regex.RegexSyntax;
import org.kframework.utils.errorsystem.KEMException;

public class RegexTest {
  private static Regex raw(RegexBody reg) {
    return new Regex(false, reg, false);
  }

  private static Regex start(RegexBody reg) {
    return new Regex(true, reg, false);
  }

  private static Regex end(RegexBody reg) {
    return new Regex(false, reg, true);
  }

  private static Regex startEnd(RegexBody reg) {
    return new Regex(true, reg, true);
  }

  private static RegexBody.Char chr(char c) {
    return new RegexBody.Char(c);
  }

  private static RegexBody.Concat concat(RegexBody... regs) {
    return new RegexBody.Concat(Arrays.stream(regs).toList());
  }

  private static RegexBody.Union union(RegexBody reg1, RegexBody reg2) {
    return new RegexBody.Union(reg1, reg2);
  }

  private static void testParse(String text, Regex parsed) {
    Assert.assertEquals(parsed, ParseRegex.parse(text));
  }

  private static void testThrows(String text) {
    Assert.assertThrows(KEMException.class, () -> ParseRegex.parse(text));
  }

  private static void testRoundTrip(String text) {
    Regex parse1 = ParseRegex.parse(text);
    String out1 = RegexSyntax.K.print(parse1);
    Regex parse2 = ParseRegex.parse(out1);
    String out2 = RegexSyntax.K.print(parse2);
    Assert.assertEquals(parse1, parse2);
    Assert.assertEquals(out1, out2);
  }

  // Use this variable to avoid the eye-sore and confusion of double escaping
  private static final char slash = '\\';

  @Test
  public void testSimple() {
    testParse("a", raw(chr('a')));
    testParse("ab", raw(concat(chr('a'), chr('b'))));
  }

  @Test
  public void testStartLine() {
    testThrows("^");
    testThrows("a^b");
    testParse("^a", start(chr('a')));
    testParse("^ab", start(concat(chr('a'), chr('b'))));
    testParse(slash + "^ab", raw(concat(chr('^'), chr('a'), chr('b'))));
    testParse("a" + slash + "^b", raw(concat(chr('a'), chr('^'), chr('b'))));
  }

  @Test
  public void testEndLine() {
    testThrows("$");
    testThrows("a$b");
    testParse("a$", end(chr('a')));
    testParse("ab$", end(concat(chr('a'), chr('b'))));
    testParse("ab" + slash + "$", raw(concat(chr('a'), chr('b'), chr('$'))));
    testParse("a" + slash + "$b", raw(concat(chr('a'), chr('$'), chr('b'))));
    testParse("" + slash + slash + "$", end(chr(slash)));
  }

  @Test
  public void testStartEnd() {
    testThrows("^$");
    testThrows("$a^");
    testParse("^a$", startEnd(chr('a')));
  }

  @Test
  public void testUnion() {
    testThrows("|");
    testThrows("a|");
    testThrows("|a");
    testParse("a|b", raw(union(chr('a'), chr('b'))));
    testParse("ab|c", raw(union(concat(chr('a'), chr('b')), chr('c'))));
  }

  @Test
  public void roundTrip() {
    // Every regex terminal in our codebase at time of writing
    testRoundTrip("#([a-fA-F0-9][a-fA-F0-9])*");
    testRoundTrip("#\\(-*alloc[0-9]+(\\+0x[0-9a-fA-F]+)?-*\\)#");
    testRoundTrip("#exp");
    testRoundTrip("%(@|[_a-zA-Z][_0-9a-zA-Z\\.]*)?");
    testRoundTrip("(#.*)|[\\n \\t\\r]*");
    testRoundTrip(
        "(([1-9][0-9]*)|(0[0-7]*)|(0[xX][0-9a-fA-F]+))(([uU][lL]?)|([uU]((ll)|(LL)))|([lL][uU]?)|(((ll)|(LL))[uU]?))?");
    testRoundTrip("(;[^\\n\\r]*)");
    testRoundTrip("([\\ \\n\\r\\t])");
    testRoundTrip(
        "([\\+\\-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+\\-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?");
    testRoundTrip("([\\-+][<>]([\\-+][<>])*[\\-+]?)|[\\-+]|\\\\dot");
    testRoundTrip("([a-zA-Z0-9]|_)+");
    testRoundTrip("([a-z][a-z0-9\\-]*)|\\$");
    testRoundTrip("(\\!|\\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)");
    testRoundTrip("(\\$)([A-Z][A-Za-z0-9'_]*)");
    testRoundTrip("(\\$|\\!|\\?)?([A-Z][A-Za-z0-9']*|_)");
    testRoundTrip("(\\/\\*([^\\*]|(\\*+([^\\*\\/])))*\\*+\\/)");
    testRoundTrip("(\\/\\/[^\\n\\r]*)");
    testRoundTrip("({DecConstant}|{OctConstant}|{HexConstant})({IntSuffix}?)");
    testRoundTrip("-?[0-9]+(.[0-9]+)?((E|e)(\\+|-)?[0-9]+)?(f32|f64)");
    testRoundTrip("0?1");
    testRoundTrip("0x([0-9a-fA-F]{2})*");
    testRoundTrip("0x[0-9a-fA-F]+");
    testRoundTrip("0x{HexDigit}+");
    testRoundTrip("1");
    testRoundTrip(":([_a-zA-Z][_0-9a-zA-Z\\.]*)?");
    testRoundTrip(";;[^\\n\\r]*");
    testRoundTrip("@(%|%%|[_a-zA-Z][_0-9a-zA-Z\\.]*)?");
    testRoundTrip("@?[a-z]+");
    testRoundTrip("C[A,D]{2,}R");
    testRoundTrip("DII+P");
    testRoundTrip("DUU+P");
    testRoundTrip("MAP_C[AD]{2,}R");
    testRoundTrip("NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?");
    testRoundTrip("P[AIP]+R");
    testRoundTrip("SET_C[AD]{2,}R");
    testRoundTrip("UNP[AIP]+R");
    testRoundTrip("[#a-z][a-zA-Z0-9]*");
    testRoundTrip(
        "[']([^\\\"\\\\\\n\\r\\t]|\\\\[\\\"'nrt0\\\\]|\\\\x[0-7][0-9a-fA-F]|\\\\u\\{[0-9a-fA-F]+\\}|\\\\u[0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F][0-9a-fA-F]?)?)?)?)?|\\\\\\n)[']");
    testRoundTrip("['][a-z][_a-zA-Z0-9]*");
    testRoundTrip("[0-9A-Z]{58}");
    testRoundTrip("[0-9]+");
    testRoundTrip("[0-9]+(\\.[0-9]+)*");
    testRoundTrip("[0-9]+.[0-9]+.[0-9]+");
    testRoundTrip("[0-9]+:[0-9]+");
    testRoundTrip("[0-9]+_(usize|u8|u16|u32|u64|u128)");
    testRoundTrip("[0-9][a-fA-F]");
    testRoundTrip("[0-9a-zA-Z_]+");
    testRoundTrip("[A-Z2-7=]+");
    testRoundTrip("[A-Z][A-Z\\-]*");
    testRoundTrip("[A-Z][A-Za-z0-9]*");
    testRoundTrip("[A-Z][a-zA-Z0-9]*");
    testRoundTrip("[A-Z][a-zA-Z]*");
    testRoundTrip("[A-Z_][A-Za-z0-9_]*");
    testRoundTrip("[A-Za-z'\\-][A-Za-z'0-9\\-]*");
    testRoundTrip("[A-Za-z\\_][A-Za-z0-9\\_]*");
    testRoundTrip("[A-Za-z][A-Za-z0-9\\_\\']*");
    testRoundTrip("[A-Za-z_#][A-Za-z_0-9]*");
    testRoundTrip("[A-Za-z_][A-Za-z_0-9]*");
    testRoundTrip(
        "[LuU]?'(([^'\\n\\\\])|(\\\\['\\\"?\\\\abfnrtv])|(\\\\[0-7]{3})|(\\\\x[0-9a-fA-F]+)|(\\\\u[0-9a-fA-F]{4})|(\\\\U[0-9a-fA-F]{8}))+'");
    testRoundTrip("[LuU]?'{CCharSeq}'");
    testRoundTrip("[\\ \\n\\r\\t]");
    testRoundTrip("[\\+\\-]?0x[0-9a-fA-F]+(_[0-9a-fA-F]+)*");
    testRoundTrip("[\\+\\-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?");
    testRoundTrip("[\\+\\-]?[0-9]+");
    testRoundTrip("[\\+\\-]?[0-9]+(_[0-9]+)*");
    testRoundTrip("[\\+\\-]?[0-9]+[pP][0-9]+");
    testRoundTrip("[\\+\\-]?[0-9]+\\.[0-9]+");
    testRoundTrip("[\\-]?[0-9]+_(isize|i8|i16|i32|i64|i128)");
    testRoundTrip(
        "[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]");
    testRoundTrip(
        "[\\\"]([^\\\"\\\\\\n]|\\\\[\\\"'nrt0\\\\]|\\\\x[0-7][0-9a-fA-F]|\\\\u\\{[0-9a-fA-F]+\\}|\\\\u[0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F][0-9a-fA-F]?)?)?)?)?|\\\\\\n)*[\\\"]");
    testRoundTrip("[\\\"]([^\\\"\n\r\\\\]|[\\\\][nrtf\\\"\\\\])*[\\\"]");
    testRoundTrip("[_a-zA-Z][_a-zA-Z0-9]*");
    testRoundTrip("[a-fA-F][0-9a-fA-F]");
    testRoundTrip("[a-zA-Z0-9\\+\\/=]+");
    testRoundTrip("[a-zA-Z0-9_/\\-\\.]*\\.rs:[0-9]+:[0-9]+:");
    testRoundTrip("[a-zA-Z\\.\\_\\$][0-9a-zA-Z\\.\\_\\-\\$]*");
    testRoundTrip("[a-zA-Z]([0-9a-zA-Z])*");
    testRoundTrip("[a-zA-Z][A-Za-z0-9_#]*");
    testRoundTrip("[a-zA-Z][A-Za-z0-9_]*");
    testRoundTrip("[a-zA-Z][a-zA-Z0-9\\-]*");
    testRoundTrip("[a-zA-Z][a-zA-Z0-9_']*");
    testRoundTrip("[a-zA-Z]{Alphanum}*");
    testRoundTrip("[a-zA-Z_][a-zA-Z0-9_]*");
    testRoundTrip("[a-z][_a-zA-Z0-9]*");
    testRoundTrip("[a-z][a-zA-Z0-9]*");
    testRoundTrip("[a-z][a-zA-Z0-9_]*");
    testRoundTrip("[ab]#");
    testRoundTrip("[ab]\\*");
    testRoundTrip("\\#[a-fA-F0-9][a-fA-F0-9]*");
    testRoundTrip("\\$[0-9a-zA-Z!$%&'*+/<>?_`|~=:\\@\\^.\\-]+");
    testRoundTrip("\\$[A-Za-z_#][A-Za-z_0-9]*");
    testRoundTrip("\\$[_a-zA-Z][_0-9a-zA-Z]*");
    testRoundTrip("\\(;([^;]|(;+([^;\\)])))*;\\)");
    testRoundTrip("\\+[1-9][0-9]*");
    testRoundTrip("\\/\\/[^\\n\\r]*");
    testRoundTrip("\\\"(([^\\\"\\\\])|(\\\\[0-9a-fA-F]{2}))*\\\"");
    testRoundTrip(
        "\\\"(([^\\\"\\\\])|(\\\\[0-9a-fA-F]{2})|(\\\\t)|(\\\\n)|(\\\\r)|(\\\\\\\")|(\\\\')|(\\\\\\\\)|(\\\\u\\{[0-9a-fA-F]{1,6}\\}))*\\\"");
    testRoundTrip("\\^+[a-z][a-z0-9\\-]*");
    testRoundTrip("_");
    testRoundTrip("_[0-9]+");
    testRoundTrip("`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`");
    testRoundTrip("`(\\\\`|\\\\\\\\|[^`\\\\\n\r])+`");
    testRoundTrip(
        "b[']([^\\\"\\\\\\n\\r\\t]|\\\\[\\\"'nrt0\\\\]|\\\\x[0-7][0-9a-fA-F]|\\\\u[0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F]([0-9a-fA-F][0-9a-fA-F]?)?)?)?)?|\\\\\\n)[']");
    testRoundTrip(
        "b[\\\"](([\\x20\\x21\\x23-\\x5B\\x5D-\\x7E])|([\\\\][tnfr\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]");
    testRoundTrip(
        "b[\\\"]([^\\\"\\\\\\n\\r\\t]|\\\\[\\\"'nrt0\\\\]|\\\\x[0-9a-fA-F][0-9a-fA-F]|\\\\\\n)*[\\\"]");
    testRoundTrip("ba.");
    testRoundTrip("bb[0-9]+");
    testRoundTrip("c");
    testRoundTrip("d");
    testRoundTrip("e");
    testRoundTrip("forall.[ab][#*]");
    testRoundTrip("{DecFloatConstant}|{HexFloatConstant}");
    testRoundTrip("{EncodingPrefix}?\\\"{SCharSeq}?\\\"");
    testRoundTrip("{IdentifierNonDigit}(({IdentifierNonDigit}|{Digit})*)");
    testRoundTrip("{UD}");
    testRoundTrip("{UI}");
    testRoundTrip("🙁|🙂");
  }
}
