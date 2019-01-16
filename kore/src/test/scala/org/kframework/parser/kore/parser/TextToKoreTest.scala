package org.kframework.parser.kore.parser

import java.io.EOFException

import junit.framework.TestFailure
import org.apache.commons.io.FileUtils
import org.junit.Assert.assertEquals
import org.junit.Test
import org.kframework.parser.kore.Builders
import org.kframework.parser.kore.implementation.DefaultBuilders
import org.kframework.parser.kore.parser.{KoreToText, ParseError, TextToKore}

class TextToKoreTest {

  /**
    * Tests for parsing sorts.
    */
  @Test def test_sort_1(): Unit = {
    parseFromFile("test-sort-1.kore")
  }
  @Test def test_sort_2(): Unit = {
    parseFromFile("test-sort-2.kore")
  }
  @Test def test_sort_3(): Unit = {
    parseFromFile("test-sort-3.kore")
  }
  @Test def test_sort_4(): Unit = {
    parseFromFile("test-sort-4.kore")
  }


  /**
    * Tests for parsing symbols.
    */
  @Test def test_symbol_1(): Unit = {
    parseFromFile("test-symbol-1.kore")
  }
  @Test def test_symbol_2(): Unit = {
    parseFromFile("test-symbol-2.kore")
  }
  @Test def test_symbol_3(): Unit = {
    parseFromFile("test-symbol-3.kore")
  }
  @Test def test_symbol_4(): Unit = {
    parseFromFile("test-symbol-4.kore")
  }
  @Test def test_symbol_5(): Unit = {
    parseFromFile("test-symbol-5.kore")
  }
  @Test def test_symbol_6(): Unit = {
    parseFromFile("test-symbol-6.kore")
  }
  @Test def test_symbol_7(): Unit = {
    parseFromFile("test-symbol-7.kore")
  }
  @Test def test_symbol_8(): Unit = {
    parseFromFile("test-symbol-8.kore")
  }

  /**
    * Tests for hooks.
    */
  @Test def test_hooks_1(): Unit = {
    parseFromFile("test-hooks-1.kore")
  }

  @Test def test_hooks_2(): Unit = {
    parseFromFile("test-hooks-2.kore")
  }

  @Test def test_hooks_3(): Unit = {
    parseFromFile("test-hooks-3.kore")
  }

  /**
    * Tests for parsing aliases.
    */
  @Test def test_alias_1(): Unit = {
    parseFromFile("test-alias-1.kore")
  }
  @Test def test_alias_2(): Unit = {
    parseFromFile("test-alias-2.kore")
  }
  @Test def test_alias_3(): Unit = {
    parseFromFile("test-alias-3.kore")
  }
  @Test def test_alias_4(): Unit = {
    parseFromFile("test-alias-4.kore")
  }
  @Test def test_alias_5(): Unit = {
    parseFromFile("test-alias-5.kore")
  }
  @Test def test_alias_6(): Unit = {
    parseFromFile("test-alias-6.kore")
  }
  @Test def test_alias_7(): Unit = {
    parseFromFile("test-alias-7.kore")
  }
  @Test def test_alias_8(): Unit = {
    parseFromFile("test-alias-8.kore")
  }

  /**
    * Tests for parsing patterns.
    */
  @Test def test_pattern_1(): Unit = {
    parseFromFile("test-pattern-1.kore")
  }
  @Test def test_pattern_2(): Unit = {
    parseFromFile("test-pattern-2.kore")
  }
  @Test def test_pattern_3(): Unit = {
    parseFromFile("test-pattern-3.kore")
  }
  @Test def test_pattern_4(): Unit = {
    parseFromFile("test-pattern-4.kore")
  }
  @Test def test_pattern_5(): Unit = {
    parseFromFile("test-pattern-5.kore")
  }
  @Test def test_pattern_6(): Unit = {
    parseFromFile("test-pattern-6.kore")
  }
  @Test def test_pattern_7(): Unit = {
    parseFromFile("test-pattern-7.kore")
  }
  @Test def test_pattern_8(): Unit = {
    parseFromFile("test-pattern-8.kore")
  }
  @Test def test_pattern_9(): Unit = {
    parseFromFile("test-pattern-9.kore")
  }
  @Test def test_pattern_10(): Unit = {
    parseFromFile("test-pattern-10.kore")
  }
  @Test def test_pattern_11(): Unit = {
    parseFromFile("test-pattern-11.kore")
  }
  @Test def test_pattern_12(): Unit = {
    parseFromFile("test-pattern-12.kore")
  }
  @Test def test_pattern_13(): Unit = {
    parseFromFile("test-pattern-13.kore")
  }
  /**
    * Tests for parsing attributes.
    */
  @Test def test_attribute_1(): Unit = {
    parseFromFile("test-attribute-1.kore")
  }
  @Test def test_attribute_2(): Unit = {
    parseFromFile("test-attribute-2.kore")
  }

  /**
    * Tests for comments.
    */
  @Test def test_comment_1(): Unit = {
    parseFromFile("test-comment-1.kore")
  }
  @Test def test_comment_2(): Unit = {
    parseFromFile("test-comment-2.kore")
  }
  @Test def test_comment_3(): Unit = {
    parseFromFile("test-comment-3.kore")
  }
  @Test def test_comment_4(): Unit = {
    parseFromFile("test-comment-4.kore")
  }
  @Test def test_comment_5(): Unit = {
    parseFromFile("test-comment-5.kore")
  }
  @Test def test_comment_6(): Unit = {
    parseFromFile("test-comment-6.kore")
  }
  @Test def test_comment_7(): Unit = {
    parseFromFile("test-comment-7.kore")
  }

  /**
    * Tests for strings.
    */
  @Test def test_string_1(): Unit = {
    parseFromFile("test-string-1.kore")
  }
  @Test def test_string_2(): Unit = {
    parseFromFile("test-string-2.kore")
  }
  @Test def test_string_3(): Unit = {
    parseFromFile("test-string-3.kore")
  }
  @Test def test_string_4(): Unit = {
    parseFromFile("test-string-4.kore")
  }
  @Test def test_string_5(): Unit = {
    parseFromFile("test-string-5.kore")
  }
  @Test def test_string_6(): Unit = {
    parseFromFile("test-string-6.kore")
  }
  @Test def test_string_7(): Unit = {
    parseFromFile("test-string-7.kore")
  }


  /**
    * Tests for exception and error handling.
    */
  @Test def test_exception_1(): Unit = {
    parseFromFileExpectParseException("test-sort-5.kore")
  }
  @Test def test_exception_2(): Unit = {
    parseFromFileExpectParseException("test-exception-2.kore")
  }
  @Test def test_exception_3(): Unit = {
    parseFromFileExpectParseException("test-exception-3.kore")
  }
  @Test def test_exception_4(): Unit = {
    parseFromFileExpectParseException("test-exception-4.kore")
  }
  @Test def test_exception_5(): Unit = {
    parseFromFileExpectParseException("test-exception-5.kore")
  }
  @Test def test_exception_6(): Unit = {
    parseFromFileExpectParseException("test-exception-6.kore")
  }
  @Test def test_exception_7(): Unit = {
    parseFromFileExpectParseException("test-exception-7.kore")
  }
  @Test def test_exception_8(): Unit = {
    parseFromFileExpectParseException("test-exception-8.kore")
  }
  @Test def test_exception_9(): Unit = {
    parseFromFileExpectParseException("test-exception-9.kore")
  }
  @Test def test_exception_10(): Unit = {
    parseFromFileExpectParseException("test-exception-10.kore")
  }
  @Test def test_exception_11(): Unit = {
    parseFromFileExpectParseException("test-exception-11.kore")
  }
  @Test def test_exception_12(): Unit = {
    parseFromFileExpectParseException("test-exception-12.kore")
  }
  @Test def test_exception_13(): Unit = {
    parseFromFileExpectParseException("test-exception-13.kore")
  }
  @Test def test_exception_14(): Unit = {
    parseFromFileExpectParseException("test-exception-14.kore")
  }
  @Test def test_exception_15(): Unit = {
    parseFromFileExpectParseException("test-exception-15.kore")
  }
  @Test def test_exception_16(): Unit = {
    parseFromFileExpectParseException("test-exception-16.kore")
  }
  @Test def test_exception_17(): Unit = {
    parseFromFileExpectParseException("test-exception-17.kore")
  }
  @Test def test_exception_18(): Unit = {
    parseFromFileExpectParseException("test-exception-18.kore")
  }
  @Test def test_exception_19(): Unit = {
    parseFromFileExpectParseException("test-exception-19.kore")
  }
  @Test def test_exception_20(): Unit = {
    parseFromFileExpectParseException("test-exception-20.kore")
  }
  @Test def test_exception_21(): Unit = {
    parseFromFileExpectParseException("test-exception-21.kore")
  }
  @Test def test_exception_22(): Unit = {
    parseFromFileExpectParseException("test-sort-6.kore")
  }
  @Test def test_exception_23(): Unit = {
    parseFromFileExpectParseException("test-exception-23.kore")
  }
  @Test def test_exception_24(): Unit = {
    parseFromFileExpectParseException("test-exception-24.kore")
  }
  @Test def test_exception_25(): Unit = {
    parseFromFileExpectParseException("test-exception-25.kore")
  }
  @Test def test_exception_26(): Unit = {
    parseFromFileExpectParseException("test-exception-26.kore")
  }
  @Test def test_exception_27(): Unit = {
    parseFromFileExpectParseException("test-exception-27.kore")
  }

  /**
    * Tests for scanner
    */
  @Test def test_scanner_1(): Unit = {
    parseFromFile("test-scanner-1.kore")
  }

  /**
    * Comprehensive tests for parsing complete and meaningful modules.
    */


  @Test def test_bool(): Unit = {
    parseFromFile("bool.kore")
  }
  @Test def test_nat(): Unit = {
    parseFromFile("nat.kore")
  }
  @Test def test_list(): Unit = {
    parseFromFile("list.kore")
  }
  @Test def test_lambda(): Unit = {
    parseFromFile("lambda.kore")
  }
  @Test def test_imp(): Unit = {
    parseFromFile("imp.kore")
  }
  @Test def test_imp2(): Unit = {
    parseFromFile("imp2.kore")
  }


  def strip(s: String): String = {
    trim(s.stripMargin)
  }

  def trim(s: String): String = {
    s.replaceAll("^\\s+|\\s+$", "") // s.replaceAll("^\\s+", "").replaceAll("\\s+$", "")
  }

  def parseFromStringWithExpected(s: String, expected: String): Unit = {
    val src = io.Source.fromString(s)
    try {
      parseTest(SourceFOS(src), s)
    } finally {
      src.close()
    }
  }

  def parseFromString(s: String): Unit = {
    val src = io.Source.fromString(s)
    try {
      parseTest(SourceFOS(src), s)
    } finally {
      src.close()
    }
  }

  def parseFromFile(file: String): Unit = {
    val f = FileUtils.toFile(getClass.getResource("/" + file))
    parseTest(FileFOS(f), FileUtils.readFileToString(f))
  }

  def parseFromFileExpectParseException(file: String): Unit = {
    try {
      parseFromFile(file) // expect ParseError being thrown
      throw new Exception("Parse " + file + " succeeded while excepting ParseError.")
    }
    catch {
      case _ : ParseError => // Expected
    }
  }

  sealed trait FileOrSource
  case class FileFOS(x: java.io.File) extends FileOrSource
  case class SourceFOS(x: io.Source) extends FileOrSource

  /** Tests if parse is correct by checking if
    *   src ~~ unparse(parse(src))
    * where src is a kore definition source file and
    *       ~~ is the equiv relation modulo whitespaces & comments.
    * Property:
    *     src1 ~~ src2
    * iff canonicalString(src1) == canonicalString(src2)
    */
  def parseTest(src: FileOrSource, expected: String): Unit = {
    //TODO: Make test file parametric over builders.
    val builder: Builders = DefaultBuilders
    val begin = java.lang.System.nanoTime()
    val minikore = src match {
      case src: FileFOS => TextToKore(builder).parse(src.x)
      case src: SourceFOS => TextToKore(builder).parse(src.x)
    }
    val end = java.lang.System.nanoTime(); println(end - begin)
    val textOfMiniKore = KoreToText(minikore)

    val canonicalString = src match {
      case src: FileFOS => TextToKore(builder).canonicalString(src.x)
      case src: SourceFOS => TextToKore(builder).canonicalString(src.x)
    }

    val canonicalStringOfTextOfMiniKore = src match {
      case src: FileFOS => TextToKore(builder).canonicalString(textOfMiniKore)
      case src: SourceFOS => TextToKore(builder).canonicalString(textOfMiniKore)
    }
    println(canonicalString)
    println(canonicalStringOfTextOfMiniKore)
    assertEquals(canonicalString, canonicalStringOfTextOfMiniKore)

    // val outputfile = new java.io.File("/tmp/x")
    // FileUtils.writeStringToFile(outputfile, text)
    // if (expected == text) () // t == u(p(t))
    // else if (trim(expected) == trim(text)) () // t == u(p(t)) modulo leading/trailing whitespaces
    // else {
    // assertEquals(expected.replaceAll("\\s+", ""), text.replaceAll("\\s+", "")) //   t  ==   u(p(t))  modulo whitespaces
    // assertEquals(minikore, new TextToKore(builder).parse(io.Source.fromString(text))) // p(t) == p(u(p(t)))
    // }
  }

  //  @Test def errorTest(): Unit = {
  //    new TextToMini().error('a', "abc") match {
  //      case ParseError(msg) =>
  //        assertEquals(
  //          strip("""
  //            |ERROR: Line 0: Column 0: Expected 'a', but abc
  //            |null
  //            |^
  //            |"""),
  //          msg)
  //      case _ => assert(false)
  //    }
  //  }

}
