package org.kframework.unparser

import java.io.PrintStream

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.kore.Unapply._
import org.kframework.kore.{KLabel, InjectedKLabel, K, KApply}

import scala.collection.JavaConverters._

/**
 * Print terms according to the official KAST syntax.
 */
object ToKast {
  def apply(k: K): String = {
    val b = StringBuilder.newBuilder
    unparse(s => b ++= s, false, 0, k)
    b.toString()
  }
  def apply(k: K, out: PrintStream): Unit = {
    unparse(out.print, false, 0, k)
  }

  def apply(l: KLabel): String = unparse(false, l)

  def escape(s: String): String = StringEscapeUtils.escapeJava(s)

  def unparse(inParen: Boolean, l: KLabel) : String = {
    if (l.name.matches("[#a-z][a-zA-Z0-9]*")
        && l.name != "#token" && l.name != "#klabel") {
      l.name
    } else if (inParen) {
      " `"+ escapeBackTicksAndSlashes(l.name) +'`'
    } else {
      '`'+ escapeBackTicksAndSlashes(l.name) +'`'
    }
  }

  def escapeBackTicksAndSlashes(str: String) : String =
    str.foldRight[List[Char]] (Nil) { (c, r) => if (c == '`' || c == '\\') '\\' :: c :: r else c :: r }.mkString

  /**
   * Recursive worker function for printing KAST terms.
   * The extra arguments are needed to respect precedence and the lexical syntax.
   *
   * <ul>
   * <li>Precedence level 0 is for the top of a term or within an argument list.
   * <li>Precedence level 1 is for arguments of a KRewrite.
   * <li>Precedence level 2 is for entries in a KSequence,
   * </ul>
   * The only case where braces may be needed is around a KSequence which is
   * an argument of a KRewrite.
   *
   * When a label that requires quotes is the first item inside a backquote bracket
   * whitespace is required, as in {@code `` `_+_`(...} , to prevent the
   * label quote from combining with the bracket,
   * as in the incorrect {@code ```_+_`(...}
   *
   * @param accumulator The function that accumulates the string to date. ie, either a StringBuilder or
   *                    an output stream of some kind.
   * @param inParen True if this term is the leftmost within a set of brackets
   * @param prec The current precedence level
   * @param k The term to print
   */
  def unparse(accumulator:String=>Unit, inParen: Boolean, prec: Int, k: K): Unit = k match {
    case KToken(s, sort) => accumulator("#token(\"" + escape(s) + "\",\"" + escape(sort.name) + "\")")
    case InjectedKLabel(l) => accumulator("#klabel("+apply(l)+")")
    case KVariable(v) => accumulator(v.toString)
    case KApply(l, List()) => accumulator(unparse(inParen,l)+"(.KList)")
    case KApply(l, args) =>
      accumulator(unparse(inParen,l))
      accumulator("(")
      var first = true
      for (a <- args) {
        if (!first) {
          accumulator(",")
        } else {
          first = false
        }
        unparse(accumulator, false, 0, a)
      }
      accumulator(")")
    case KSequence(Seq()) => accumulator(".K")
    case KSequence(a +: items) =>
      unparse(accumulator, inParen, 2, a)
      for (i <- items) {
        accumulator("~>")
        unparse(accumulator, false, 2, i)
      }
    case KRewrite(l,r) =>
      val needParen = prec > 1
      if (needParen) accumulator("``")
      unparse(accumulator,needParen || inParen,1,l)
      accumulator("=>")
      unparse(accumulator,false,1,r)
      if (needParen) accumulator("``")
    case KAs(l,r) =>
      val needParen = prec > 1
      if (needParen) accumulator("``")
      unparse(accumulator,needParen || inParen,1,l)
      accumulator(" #as ")
      unparse(accumulator,false,1,r)
      if (needParen) accumulator("``")
  }
}
