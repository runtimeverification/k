package org.kframework.tiny

import com.google.common.cache.CacheBuilder
import org.kframework.definition._
import org.kframework.kore.{Unapply, KApply}

trait Theory {
  val cache = CacheBuilder.newBuilder().maximumSize(10000).build[K, K]()
  val module: Module

  def normalize(k: K): K

  val self = this
}


case class FreeTheory(val module: Module) extends Theory {
  override def normalize(k: K): K = k
}

class TheoryWithFunctions(val module: Module) extends Theory {
  val moduleWithOnlyFunctions = ModuleTransformer(m => Module(
    m.name, m.imports, m.localSentences.filter({
      case r: org.kframework.definition.Rule =>
        r.body match {
          case Unapply.KRewrite(app: KApply, _) => module.attributesFor(app.klabel).contains("function")
          case _ => false
        }
      case _ => true
    })), "CreateModuleForFunctions").apply(module)

//  println(moduleWithOnlyFunctions.allImports.mkString("\n\n"))

  val rewriterForFunctions = new Rewriter(moduleWithOnlyFunctions, SimpleIndex, FreeTheory(moduleWithOnlyFunctions))

  override def normalize(k: K): K =
    if (k.isNormalBy(this))
      k
    else
      rewriterForFunctions.execute(k)

}

//case class RewriteBasedTheory(rw: K => K) extends Theory {
//  def normalize(k: K): K = rw(k)
//}
