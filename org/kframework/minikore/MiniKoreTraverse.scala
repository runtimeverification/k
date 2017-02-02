package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

/**
  * Created by daejunpark on 1/31/17.
  */
object MiniKoreTraverse {

  def size(p: i.Pattern): Int = p match {
    case p:i.Leaf        => 1
    case p:i.Node0[_]    => 1
    case p:i.Node1[_]    => size(p.p)
    case p:i.Node2[_]    => size(p.p) + size(p.q)
    case p:i.NodeV[_]    => size(p.p)
    case p:i.Application => p.args.map(size).sum
  }

  def iter(f: i.Pattern => Unit)(p: i.Pattern): Unit = p match {
    case p:i.Leaf        => f(p)
    case p:i.Node0[_]    => f(p)
    case p:i.Node1[_]    => f(p); iter(f)(p.p)
    case p:i.Node2[_]    => f(p); iter(f)(p.p); iter(f)(p.q)
    case p:i.NodeV[_]    => f(p); f(p.v); iter(f)(p.p)
    case p:i.Application => f(p); p.args.foreach(iter(f))
  }

  def map(f: i.Pattern => i.Pattern)(p: i.Pattern): i.Pattern = p match {
    case p:i.Variable    => f(p.constructor(p.name, p.sort))
    case p:i.Application => f(p.constructor(p.label, p.args.map(map(f))))
    case p:i.DomainValue => f(p.constructor(p.label, p.value))
    case p:i.Node0[_]    => f(p.constructor())
    case p:i.Node1[_]    => f(p.constructor(p.p))
    case p:i.Node2[_]    => f(p.constructor(p.p, p.q))
    case p:i.NodeV[_]    => f(p.constructor(p.v, p.p))
  }

//  def fold[P1 <: i.Pattern, P2 <: i.Pattern, V1 <: i.Variable, V2 <: i.Variable]
//      (f: P1 => P2, v: V1 => V2, name: String => String, sort: String => String, label: String => String, value: String => String)
//      (p: P1): P2 = p match {
//    case p:i.Variable    => f(p.constructor(name(p.name), sort(p.sort)))
//    case p:i.Application => f(p.constructor(p.label, p.args.map(map(f))))
//    case p:i.DomainValue => f(p.constructor(p.label, p.value))
//    case p:i.Node0[_]    => f(p.constructor())
//    case p:i.Node1[_]    => f(p.constructor(p.p))
//    case p:i.Node2[_]    => f(p.constructor(p.p, p.q))
//    case p:i.NodeV[_]    => f(p.constructor(p.v, p.p))
//  }

  def subst(m: Map[i.Variable, i.Pattern])(p: i.Pattern): i.Pattern = {
    def fresh(x: i.Variable): i.Variable = {
      x.constructor(x.name + "!new!", x.sort) // TODO: make it really fresh
    }
    p match {
      case v:i.Variable => if (m.contains(v)) m(v) else p
      case p:i.NodeV[_] =>
        val x = fresh(p.v)
        p.constructor(x, subst(m + (p.v -> x))(p.p))
      case _ => map(subst(m))(p)
    }
  }

  def test(): Unit = {
    val p = MiniKore.True()
    val x = MiniKore.Variable("x", "K")
    val v = MiniKore.False()
    val m = Map(x.asInstanceOf[i.Variable] -> v)
    subst(m)(p)
    ()
  }

}
