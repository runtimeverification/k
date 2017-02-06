package org.kframework.minikore

import org.kframework.minikore.TreeInterface._

import org.kframework.minikore.PatternInterface._

object MiniKoreTraverse {

  def size(p: Pattern): Int = p match {
    case p: Leaf[_] => 1
    case p: Node[_] => p.children map size sum
    case p: NodeApply[_] => if (p.children.isEmpty) 1 else p.children map size sum
  }

  //
  //    def iter(f: Pattern => Unit)(p: Pattern): Unit = p match {
  //      case p:Leaf[_, _]        => f(p)
  //      case p: Node[_, _, _]    => p.childrenAsSeq map(f)
  //    }
  //
  //    def map(f: Pattern => Pattern)(p: Pattern): Pattern = p match {
  //      case p: Leaf[_, _]        => f(p)
  //      case p: Node[_, _, _]     => p.construct
  //    }
  //
  //    def mapShallow(f: Pattern => Pattern)(p: Pattern): Pattern = p match {
  //      case p:Leaf        => p
  //      case p:Node0[_]    => p
  //      case p:Node1[_]    => p.constructor(f(p.p))
  //      case p:Node2[_]    => p.constructor(f(p.p), f(p.q))
  //      case p:NodeV[_]    => p.constructor(p.v, f(p.p))
  //      case p:Application => p.constructor(p.label, p.args.map(f))
  //    }
  //
  //    def fold
  //        (c: Constructor)
  //        (fp: Pattern => Pattern, fv: Variable => Variable,
  //         fn: String => String, fs: String => String, fl: String => String, fval: String => String)
  //        (p: Pattern): Pattern = {
  //      def loop(p: Pattern): Pattern = fold(c)(fp,fv,fn,fs,fl,fval)(p)
  //      p match {
  //        case p:Variable    => fv(c.Variable(fn(p.name), fs(p.sort)))
  //        case p:Application => fp(c.Application(fl(p.label), p.args.map(loop)))
  //        case p:DomainValue => fp(c.DomainValue(fl(p.label), fval(p.value)))
  //        case p:True        => fp(c.True())
  //        case p:False       => fp(c.False())
  //        case p:And         => fp(c.And(loop(p.p), loop(p.q)))
  //        case p:Or          => fp(c.Or(loop(p.p), loop(p.q)))
  //        case p:Not         => fp(c.Not(loop(p.p)))
  //        case p:Implies     => fp(c.Implies(loop(p.p), loop(p.q)))
  //        case p:Exists      => fp(c.Exists(fv(p.v), loop(p.p)))
  //        case p:ForAll      => fp(c.ForAll(fv(p.v), loop(p.p)))
  //        case p:Next        => fp(c.Next(loop(p.p)))
  //        case p:Rewrite     => fp(c.Rewrite(loop(p.p), loop(p.q)))
  //        case p:Equal       => fp(c.Equal(loop(p.p), loop(p.q)))
  //      }
  //    }
  //
  //    def subst(m: Map[Variable, Pattern])(p: Pattern): Pattern = {
  //      def fresh(x: Variable): Variable = {
  //        x.constructor(x.name + "!new!", x.sort) // TODO: make it really fresh
  //      }
  //      p match {
  //        case v:Variable => if (m.contains(v)) m(v) else p
  //        case p:NodeV[_] =>
  //          val x = fresh(p.v)
  //          p.constructor(x, subst(m + (p.v -> x))(p.p))
  //        case _ => mapShallow(subst(m))(p)
  //      }
  //    }
  //
  //  }
  //  object Main {
  //    val tree1 = MiniKore.And(MiniKore.DomainValue("String", "abc"), MiniKore.DomainValue("String", "X"))
  //    print(MiniKoreTraverse.size(tree1))
}
