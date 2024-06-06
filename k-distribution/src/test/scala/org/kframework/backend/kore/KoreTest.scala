// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.kore

import com.runtimeverification.k.kore._
import com.runtimeverification.k.kore.implementation.{ DefaultBuilders => B }
import com.runtimeverification.k.kore.parser.TextToKore
import java.io.File
import java.nio.file.Files
import org.kframework.compile.Backend
import org.kframework.kompile.Kompile
import org.kframework.kompile.KompileOptions
import org.kframework.main.GlobalOptions
import org.kframework.main.Tool
import org.kframework.utils.errorsystem.KExceptionManager
import org.kframework.utils.file.FileUtil
import org.kframework.utils.options.InnerParsingOptions
import org.kframework.utils.options.OuterParsingOptions
import org.kframework.utils.Stopwatch
import scala.collection.immutable

class KoreTest {

  val global: GlobalOptions = new GlobalOptions()

  val files: FileUtil = {
    val tempRoot = Files.createTempDirectory("kore-test").toFile
    val tempDir  = new File(tempRoot, "tmp")
    tempDir.mkdirs()
    val kompiledDir = new File(tempRoot, "kompiled")
    kompiledDir.mkdirs()
    new FileUtil(tempDir, tempRoot, kompiledDir, global, System.getenv)
  }

  val kem: KExceptionManager = new KExceptionManager(global)

  val options: KompileOptions = {
    val result = new KompileOptions()
    result.outerParsing = new OuterParsingOptions(files.resolveDefinitionDirectory("test.k"))
    result
  }

  def kompile(k: String): Definition = {
    val go = new GlobalOptions();
    val compiler = new Kompile(
      options,
      new OuterParsingOptions(),
      new InnerParsingOptions(),
      go,
      files,
      kem,
      new Stopwatch(go),
      false
    )
    val backend = new KoreBackend(options, files, kem, Tool.KOMPILE)
    files.saveToDefinitionDirectory("test.k", k)
    val defn = compiler.run(
      files.resolveDefinitionDirectory("test.k"),
      new KompileOptions.MainModule("TEST", KompileOptions.OptionType.USER_PROVIDED),
      new KompileOptions.SyntaxModule("TEST", KompileOptions.OptionType.USER_PROVIDED),
      backend.steps,
      backend.excludedModuleTags
    )
    backend.accept(new Backend.Holder(defn))
    new TextToKore().parse(files.resolveDefinitionDirectory("test.kore"))
  }

  def axioms(defn: Definition): immutable.Seq[AxiomDeclaration] =
    defn.modules.flatMap(
      _.decls.filter(_.isInstanceOf[AxiomDeclaration]).map(_.asInstanceOf[AxiomDeclaration])
    )

  def axioms(k: String): immutable.Seq[AxiomDeclaration] = axioms(kompile(k))

  def claims(defn: Definition): immutable.Seq[ClaimDeclaration] =
    defn.modules.flatMap(
      _.decls.filter(_.isInstanceOf[ClaimDeclaration]).map(_.asInstanceOf[ClaimDeclaration])
    )

  def claims(k: String): immutable.Seq[ClaimDeclaration] = claims(kompile(k))

  def hasAttribute(attributes: Attributes, name: String): Boolean =
    attributes.patterns.exists { case p: Application => p.head.ctr == name }

  // get the rewrite associated with a rule or equational axiom
  //
  // \and(\equals(requires, \dv("true")), \and(_, \rewrites(lhs, rhs)))
  // \and(\top(), \and(_, \rewrites(lhs, rhs)))
  // \rewrites(\and(\equals(requires, \dv("true")), lhs), \and(_, rhs))
  // \rewrites(\and(\top(), lhs), \and(_, rhs))
  // \implies(\equals(requires, \dv("true")), \and(\equals(lhs, rhs), _))
  // \implies(\top, \and(\equals(lhs, rhs), _))
  // \implies(\and(_, \equals(requires, \dv("true"))), \and(\equals(lhs, rhs), _))
  // \implies(\and(_, \top), \and(\equals(lhs, rhs), _))
  // \equals(lhs, rhs)
  def getRewrite(axiom: AxiomDeclaration): Option[GeneralizedRewrite] = {
    def go(pattern: Pattern): Option[GeneralizedRewrite] =
      pattern match {
        case And(
              _,
              Equals(_, _, _, _) +: And(
                _,
                _ +: (rw @ Rewrites(_, _, _)) +: immutable.Seq()
              ) +: immutable.Seq()
            ) =>
          Some(rw)
        case And(
              _,
              Top(_) +: And(_, _ +: (rw @ Rewrites(_, _, _)) +: immutable.Seq()) +: immutable.Seq()
            ) =>
          Some(rw)
        case Rewrites(
              s,
              And(_, Equals(_, _, _, _) +: l +: immutable.Seq()),
              And(_, _ +: r +: immutable.Seq())
            ) =>
          Some(B.Rewrites(s, l, r))
        case Rewrites(
              s,
              And(_, Top(_) +: l +: immutable.Seq()),
              And(_, _ +: r +: immutable.Seq())
            ) =>
          Some(B.Rewrites(s, l, r))
        case Implies(
              _,
              Equals(_, _, _, _),
              And(_, (eq @ Equals(_, _, Application(_, _), _)) +: _ +: immutable.Seq())
            ) =>
          Some(eq)
        case Implies(
              _,
              Top(_),
              And(_, (eq @ Equals(_, _, Application(_, _), _)) +: _ +: immutable.Seq())
            ) =>
          Some(eq)
        case Implies(
              _,
              And(_, _ +: Equals(_, _, _, _) +: immutable.Seq()),
              And(_, (eq @ Equals(_, _, Application(_, _), _)) +: _ +: immutable.Seq())
            ) =>
          Some(eq)
        case Implies(
              _,
              And(_, _ +: Top(_) +: immutable.Seq()),
              And(_, (eq @ Equals(_, _, Application(_, _), _)) +: _ +: immutable.Seq())
            ) =>
          Some(eq)
        case eq @ Equals(_, _, Application(_, _), _) => Some(eq)
        case _                                       => None

      }
    go(axiom.pattern)
  }

  private def isConcrete(symbol: SymbolOrAlias): Boolean =
    symbol.params.forall(_.isInstanceOf[CompoundSort])

  def symbols(pat: Pattern): immutable.Seq[SymbolOrAlias] =
    pat match {
      case And(_, ps)           => ps.flatMap(symbols)
      case Application(s, ps)   => immutable.Seq(s).filter(isConcrete) ++ ps.flatMap(symbols)
      case Ceil(_, _, p)        => symbols(p)
      case Equals(_, _, p1, p2) => symbols(p1) ++ symbols(p2)
      case Exists(_, _, p)      => symbols(p)
      case Floor(_, _, p)       => symbols(p)
      case Forall(_, _, p)      => symbols(p)
      case Iff(_, p1, p2)       => symbols(p1) ++ symbols(p2)
      case Implies(_, p1, p2)   => symbols(p1) ++ symbols(p2)
      case Mem(_, _, p1, p2)    => symbols(p1) ++ symbols(p2)
//      case Next(_, p) => symbols(p)
      case Not(_, p)           => symbols(p)
      case Or(_, ps)           => ps.flatMap(symbols)
      case Rewrites(_, p1, p2) => symbols(p1) ++ symbols(p2)
      case _                   => immutable.Seq()
    }

}
