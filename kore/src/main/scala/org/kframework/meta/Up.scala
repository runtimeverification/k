package org.kframework.meta

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.definition.Associativity
import org.kframework.kore._
import collection.JavaConverters._
import org.kframework.kore
import collection._

class Up[K <: kore.K](cons: Constructors[K] with ScalaSugared[K], imports: Set[String]) extends (Any => K) {

  import cons._

  //  implicit def symbolWithKApply(s: Symbol) = new {
  //    def apply(ks: K*): KApply = apply(ks.toList, Att())
  //    def apply(l: List[K], att: Att = Att()): KApply = {
  //      cons.KApply(cons.KLabel(s.name), cons.KList(l.asJava), att)
  //    }
  //  }

  def apply(o: Any): K = {
    o match {
      case o: List[_] => 'List(o map apply: _*)
      case o: Set[_] => 'Set(o map apply toList: _*)
      case att: Att => 'Att(att.att.toSeq.asInstanceOf[Seq[K]] :_*)

      // Primitives
      case o: Int => cons.KToken(o.toString, Sorts.Int, Att())
      case o: String => cons.KToken(o.toString, Sorts.KString, Att())
      case o: Boolean => cons.KToken(o.toString, Sorts.Bool, Att())

      case o: Associativity.Value => cons.KToken(o.toString, cons.Sort("Associativity"), Att())
      case o: java.io.File => cons.KToken(o.toString, cons.Sort("File"), Att())
        
      // Fallback to reflection
      case o: Product =>
        val elements = o.productIterator.toList
        val klist = cons.KList(elements map apply asJava)
        cons.KApply(cons.KLabel(processName(o.getClass().getName)), klist,
          Att() +(ClassFromUp.toString(), o.getClass().getName()))
    }
  }

  def processName(arg: String) = {
    imports.foldLeft(arg) { (klabel, theImport) => klabel.replaceAll(theImport + ".", "") }
    //    arg.replace("org.kframework.definition.", "").replace("org.kframework.koreimplementation.", "")
  }
}
