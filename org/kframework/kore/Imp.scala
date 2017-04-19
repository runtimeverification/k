package org.kframework.kore

import org.kframework.kore
import org.kframework.kore.default.DefaultBuilders

import scala.collection.Iterable

object Imp {

  val m = DefaultBuilders

  import m._

  case class Symbol(str: String) extends kore.Symbol {
    def apply(children: Iterable[kore.Pattern]): kore.Pattern = {
      m.Application(m.Symbol(str), children.toSeq)
    }
    def apply(children: kore.Pattern*): kore.Pattern = {
      apply(children)
    }

    override def toString: String = {
      str.substring(0, str.indexOf(':'))
    }
  }

  // signature

  val AExpInt = Symbol("_:Int->AExp")
  val AExpId = Symbol("_:Id->AExp")
  val AExpDiv = Symbol("_/_:AExp*AExp->AExp")
  val AExpPlus = Symbol("_+_:AExp*AExp->AExp")

  val BExpBool = Symbol("_:Bool->BExp")
  val BExpLeq = Symbol("_<=_:AExp*AExp->BExp")
  val BExpNot = Symbol("!_:BExp->BExp")
  val BExpAnd = Symbol("_&&_:BExp*BExp->BExp")

  val BlockEmpty = Symbol("{}:->Block")
  val BlockStmt = Symbol("{_}:Stmt->Block")

  val StmtBlock = Symbol("_:Block->Stmt")
  val StmtAssign = Symbol("_=_;:Id*AExp->Stmt")
  val StmtIf = Symbol("if(_)_else_:BExp*Block*Block->Stmt")
  val StmtWhile = Symbol("while(_)_:BExp*Block->Stmt")
  val StmtSeq = Symbol("__:Stmt*Stmt->Stmt")

  val Pgm = Symbol("int_;_:List{Id}*Stmt->Pgm")

  val IdsCons = Symbol("_,_:Id*List{Id}->List{Id}")
  val IdsNil = Symbol(".List:->List{Id}")

  val KAExp = Symbol("_:AExp->K")
  val KBExp = Symbol("_:BExp->K")
  val KBlock = Symbol("_:Block->K")
  val KStmt = Symbol("_:Stmt->K")
  val KPgm = Symbol("_:Pgm->K")

  // configuration

  val T = Symbol("<T>:Cell*Cell->Cell")
  val k = Symbol("<k>:List{K}->Cell")
  val state = Symbol("<state>:Map{Id,Int}->Cell")

  val kCons = Symbol("_~>_:K*List{K}->List{K}")
  val kNil = Symbol(".K:->List{K}")

  val MapIdIntInsert = Symbol("_[_<-_]:Map{Id,Int}*Id*Int->Map{Id,Int}")
  val MapIdIntLookup = Symbol("_[_]:Map{Id,Int}*Id->Int")
  val MapIdEmpty = Symbol(".Map:->Map{Id,Int}") // TODO: forall i:Id. emp[i] == undef

  // rules

  val X = Variable(Name("X"), Sort("Id"))
  val Xs = Variable(Name("X"), Sort("List{Id}"))
  val M = Variable(Name("M"), Sort("Map{Id,Int}"))
  val I = Variable(Name("I"), Sort("Int"))
  val I1 = Variable(Name("I1"), Sort("Int"))
  val I2 = Variable(Name("I2"), Sort("Int"))
  val B = Variable(Name("B"), Sort("Bool"))
  val S = Variable(Name("S"), Sort("Stmt"))
  val S1 = Variable(Name("S1"), Sort("Stmt"))
  val S2 = Variable(Name("S2"), Sort("Stmt"))
  val Ks = Variable(Name("Ks"), Sort("List{K}"))
  val Be = Variable(Name("Be"), Sort("BExp"))
  val Blk = Variable(Name("Blk"), Sort("Block"))
  val Blk1 = Variable(Name("Blk1"), Sort("Block"))
  val Blk2 = Variable(Name("Blk2"), Sort("Block"))

  val IntDiv = Symbol("_/Int_:Int*Int->Int")
  val IntPlus = Symbol("_+Int_:Int*Int->Int")
  val IntNeq = Symbol("_=/=Int_:Int*Int->Bool")
  val IntEq = Symbol("_==Int_:Int*Int->Bool")
  val IntLeq = Symbol("_<=Int_:Int*Int->Bool")
  val IntUndef = Symbol("undef:->Int") // TODO: forall i:Int. i =/= undef  /\ undef == undef
  val BoolNot = Symbol("notBool_:Bool->Bool")
  val BoolTrue = Symbol("true:->Bool")
  val BoolFalse = Symbol("false:->Bool")

//  import scala.language.implicitConversions
//  implicit def intDomainValue(x: Int): DomainValue = DomainValue(Symbol("Int"), x.toString)
  def Int(x: Int) = DomainValue(Symbol("Int"), Value(x.toString))

  implicit class infixPattern(p: kore.Pattern) {
    def ->(q: kore.Pattern): kore.Pattern = Rewrite(p, q)
    def ~>(q: kore.Pattern): kore.Pattern = kCons(p, q)
    def /\(q: kore.Pattern): kore.Pattern = And(p, q)
  }

  val rules = Seq(
    // AExp
      T(k(KAExp(AExpId(X) -> AExpInt(MapIdIntLookup(M,X))) ~> Ks), state(M)) /\ IntNeq(MapIdIntLookup(M, X), IntUndef())
    , T(k(KAExp(AExpDiv(AExpInt(I1), AExpInt(I2)) -> AExpInt(IntDiv(I1, I2))) ~> Ks), state(M)) /\ IntNeq(I1, Int(0))
    , T(k(KAExp(AExpPlus(AExpInt(I1), AExpInt(I2)) -> AExpInt(IntPlus(I1, I2))) ~> Ks), state(M))
    // BExp
    , T(k(KBExp(BExpLeq(AExpInt(I1), AExpInt(I2)) -> BExpBool(IntLeq(I1, I2))) ~> Ks), state(M))
    , T(k(KBExp(BExpNot(BExpBool(B)) -> BExpBool(BoolNot(B))) ~> Ks), state(M))
    , T(k(KBExp(BExpAnd(BExpBool(BoolTrue()), BExpBool(B)) -> BExpBool(B)) ~> Ks), state(M))
    , T(k(KBExp(BExpAnd(BExpBool(BoolFalse()), BExpBool(B)) -> BExpBool(BoolFalse())) ~> Ks), state(M))
    // Block
    , T(k((KBlock(BlockEmpty()) ~> Ks) -> Ks), state(M))
    , T(k((KBlock(BlockStmt(S)) -> KStmt(S)) ~> Ks), state(M))
    // Stmt
    , T(k((KStmt(StmtAssign(X, AExpInt(I))) ~> Ks) -> Ks), state(M -> MapIdIntInsert(M,X,I))) /\ IntNeq(MapIdIntLookup(M, X), IntUndef())
    , T(k((KStmt(StmtSeq(S1,S2)) ~> Ks) -> (KStmt(S1) ~> (KStmt(S2) ~> Ks))), state(M))
    , T(k(KStmt(StmtIf(BExpBool(BoolTrue()), Blk1, Blk2) -> Blk1) ~> Ks), state(M))
    , T(k(KStmt(StmtIf(BExpBool(BoolFalse()), Blk1, Blk2) -> Blk2) ~> Ks), state(M))
    , T(k(KStmt(StmtWhile(Be, Blk) -> StmtIf(Be, BlockStmt(StmtSeq(StmtBlock(Blk), StmtWhile(Be, Blk))), BlockEmpty())) ~> Ks), state(M))
    // Pgm
    , T(k(KPgm(Pgm(IdsCons(X, Xs) -> Xs, S)) ~> Ks), state(M -> MapIdIntInsert(M, X, Int(0)))) /\ IntEq(MapIdIntLookup(M, X), IntUndef())
    , T(k(KPgm(Pgm(IdsNil(), S)) -> KStmt(S) ~> Ks), state(M))
  )

}
