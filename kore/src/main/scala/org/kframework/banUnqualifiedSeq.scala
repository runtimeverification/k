// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework

import scala.annotation.compileTimeOnly

/**
 * In Scala 2.13, `scala.Seq` changed from aliasing `scala.collection.Seq` to aliasing
 * `scala.collection.immutable.Seq`. In this code base usage of unqualified `Seq` is banned: use
 * `immutable.Seq` or `collection.Seq` instead.
 *
 * import scala.collection import scala.collection.immutable
 *
 * This `Seq` trait is a dummy type to prevent the use of `Seq`.
 */
@compileTimeOnly("Use immutable.Seq or collection.Seq")
private[kframework] trait Seq[A1]

/**
 * In Scala 2.13, `scala.IndexedSeq` changed from aliasing `scala.collection.IndexedSeq` to aliasing
 * `scala.collection.immutable.IndexedSeq`. In this code base usage of unqualified `IndexedSeq` is
 * banned: use `immutable.IndexedSeq` or `collection.IndexedSeq`.
 *
 * import scala.collection import scala.collection.immutable
 *
 * This `IndexedSeq` trait is a dummy type to prevent the use of `IndexedSeq`.
 */
@compileTimeOnly("Use immutable.IndexedSeq or collection.IndexedSeq")
private[kframework] trait IndexedSeq[A1]
