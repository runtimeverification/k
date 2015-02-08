package org.kframework.tiny

object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => left
    case KApp(l, c, att) => l(c map toLeft, att)
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => right
    case KApp(l, c, att) => l(c map toRight, att)
    case other => other
  }
}
