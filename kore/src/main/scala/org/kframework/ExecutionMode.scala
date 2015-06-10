package org.kframework

import org.kframework.kore.K

/**
 * Created by manasvi on 6/10/15.
 *
 * Different Execution Modes will implement this Interface.
 *
 */
trait ExecutionMode[T] {

  def execute(k: K, rewriter: Rewriter): T
}
