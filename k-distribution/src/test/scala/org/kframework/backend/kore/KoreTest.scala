// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.kore

import org.kframework.kompile.Kompile
import org.kframework.kompile.KompileOptions
import org.kframework.main.GlobalOptions
import org.kframework.utils.errorsystem.KExceptionManager
import org.kframework.utils.file.FileUtil
import org.kframework.utils.options.OuterParsingOptions
import org.kframework.parser.kore._
import org.kframework.parser.kore.implementation.{DefaultBuilders => B}
import org.kframework.parser.kore.parser.TextToKore

import java.io.File
import java.nio.file.Files

class KoreTest {

  val global: GlobalOptions = new GlobalOptions()

  val files: FileUtil = {
    val tempRoot = Files.createTempDirectory("kore-test").toFile
    val tempDir = new File(tempRoot, "tmp")
    tempDir.mkdirs()
    val kompiledDir = new File(tempRoot, "kompiled")
    kompiledDir.mkdirs()
    new FileUtil(tempDir, tempRoot, tempRoot, kompiledDir, global, System.getenv)
  }

  val kem: KExceptionManager = new KExceptionManager(global)

  val options: KompileOptions = {
    val result = new KompileOptions()
    result.outerParsing = new OuterParsingOptions(files.resolveDefinitionDirectory("test.k"))
    result
  }

  def kompile(k: String): Definition = {
    val compiler = new Kompile(options, files, kem, false)
    val backend = new KoreBackend(options, files, kem)
    files.saveToDefinitionDirectory("test.k", k)
    val defn = compiler.run(files.resolveDefinitionDirectory("test.k"), "TEST", "TEST", backend.steps, backend.excludedModuleTags)
    backend.accept(defn)
    new TextToKore().parse(files.resolveDefinitionDirectory("test.kore"))
  }

  def axioms(defn: Definition): Seq[AxiomDeclaration] = {
    defn.modules.flatMap(_.decls.filter(_.isInstanceOf[AxiomDeclaration]).map(_.asInstanceOf[AxiomDeclaration]))
  }

  def axioms(k: String): Seq[AxiomDeclaration] = axioms(kompile(k))

  def claims(defn: Definition): Seq[ClaimDeclaration] = {
    defn.modules.flatMap(_.decls.filter(_.isInstanceOf[ClaimDeclaration]).map(_.asInstanceOf[ClaimDeclaration]))
  }

  def claims(k: String): Seq[ClaimDeclaration] = claims(kompile(k))

  def hasAttribute(attributes: Attributes, name : String) : Boolean = {
    attributes.patterns.exists { case p: Application => p.head.ctr == name }
  }

  def getRewrite(axiom: AxiomDeclaration): Option[GeneralizedRewrite] = {
    def go(pattern: Pattern): Option[GeneralizedRewrite] = {
      pattern match {
        case And(_, Equals(_, _, _, _), And(_, _, rw @ Rewrites(_, _, _))) => Some(rw)
        case And(_, Top(_), And(_, _, rw @ Rewrites(_, _, _))) => Some(rw)
        case Rewrites(s, And(_, Equals(_, _, _, _), l), And(_, _, r)) => Some(B.Rewrites(s, l, r))
        case Rewrites(s, And(_, Top(_), l), And(_, _, r)) => Some(B.Rewrites(s, l, r))
        case Implies(_, Bottom(_), p) => go(p)
        case Implies(_, Equals(_, _, _, _), And(_, eq @ Equals(_, _, Application(_, _), _), _)) => Some(eq)
        case Implies(_, Top(_), And(_, eq @ Equals(_, _, Application(_, _), _), _)) => Some(eq)
        case Implies(_, And(_, _, Equals(_, _, _, _)), And(_, eq @ Equals(_, _, Application(_, _), _), _)) => Some(eq)
        case Implies(_, And(_, _, Top(_)), And(_, eq @ Equals(_, _, Application(_, _), _), _)) => Some(eq)
        case eq @ Equals(_, _, Application(_, _), _) => Some(eq)
        case _ => None

      }
    }
    go(axiom.pattern)
  }

  private def isConcrete(symbol: SymbolOrAlias) : Boolean = {
    symbol.params.forall(_.isInstanceOf[CompoundSort])
  }

  def symbols(pat: Pattern): Seq[SymbolOrAlias] = {
    pat match {
      case And(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case Application(s, ps) => Seq(s).filter(isConcrete) ++ ps.flatMap(symbols)
      case Ceil(_, _, p) => symbols(p)
      case Equals(_, _, p1, p2) => symbols(p1) ++ symbols(p2)
      case Exists(_, _, p) => symbols(p)
      case Floor(_, _, p) => symbols(p)
      case Forall(_, _, p) => symbols(p)
      case Iff(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case Implies(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case Mem(_, _, p1, p2) => symbols(p1) ++ symbols(p2)
//      case Next(_, p) => symbols(p)
      case Not(_, p) => symbols(p)
      case Or(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case Rewrites(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case _ => Seq()
    }
  }


}
