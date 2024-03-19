// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework

import org.apache.commons.lang3.tuple.Pair
import scala.annotation.tailrec
import scala.jdk.CollectionConverters._

/**
 * Created by dwightguth on 4/16/15.
 */
object TopologicalSort {
  def tsort[A](edges: Traversable[(A, A)]): Iterable[A] = {
    @tailrec
    def tsort(toPreds: Map[A, Set[A]], done: Iterable[A]): Iterable[A] = {
      val (noPreds, hasPreds) = toPreds.partition(_._2.isEmpty)
      if (noPreds.isEmpty) {
        if (hasPreds.isEmpty) done else sys.error(hasPreds.toString)
      } else {
        val found = noPreds.map(_._1)
        tsort(hasPreds.mapValues(_ -- found), done ++ found)
      }
    }

    val toPred = edges.foldLeft(Map[A, Set[A]]()) { (acc, e) =>
      acc + (e._1 -> acc.getOrElse(e._1, Set())) + (e._2 -> (acc.getOrElse(e._2, Set()) + e._1))
    }
    tsort(toPred, Seq())
  }

  def tsort[A](edges: java.lang.Iterable[Pair[A, A]]): java.lang.Iterable[A] =
    tsort(edges.asScala.toSet.map((p: Pair[A, A]) => Tuple2(p.getLeft, p.getRight))).asJava
}
