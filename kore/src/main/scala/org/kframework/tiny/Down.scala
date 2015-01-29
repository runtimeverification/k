// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import org.kframework._
import koreimplementation._
import org.kframework.builtin.Sorts
import scala.util.Try
import scala.util.Success

case class Down(imports: Set[String]) extends (K => Any) {
  import Sorts.KString

  def apply(o: K): Any = o match {
    case KToken(`KString`, v, att) => v
    //    case KApply(KLabel("List"), ks, att) => ks.delegate map apply
    //    case KApply(KLabel("Seq"), ks, att) => ks.delegate map apply
    //    case KApply(KLabel("Set"), ks, att) => ks.delegate map apply toSet
    case KApply(KLabel("Sort"), KList(KToken(Sorts.KString, s, _)), _) => Sort(s)
    case KApply(KLabel(l), ks, att) if att.contains(Attributes.classFromUp) =>
      val classNameRecoveredFromUp = att.getString(Attributes.classFromUp).get
      Reflection.construct(classNameRecoveredFromUp, ks map { apply _ })

    case KApply(KLabel(l), ks, att) =>
      val children = ks map { apply _ }

      val namespacesToTry = imports
      val matchingClasses = imports map { _ + "." + l }

      matchingClasses
        .view
        .flatMap { name => Try(Reflection.findObject(name)).toOption }
        .flatMap { o => Try(Reflection.invokeMethod(o, "apply", Seq(children))).toOption }
        .headOption.getOrElse {
          matchingClasses
            .view
            .flatMap { className => Try(Reflection.construct(className, ks map apply)).toOption }
            .headOption
            .getOrElse {
              throw new AssertionError("Could not find a proper constructor for " + l +
                "\n with arguments (" + children.mkString(",") +
                ")\n of types (" + children.map(_.getClass()).mkString(",") +
                ")\n Tried:\n    " +
                matchingClasses.mkString("\n    "))
            }
        }

  }
}
