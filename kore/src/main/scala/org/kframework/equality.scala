package org.kframework

trait HasTypedEquals[T] {
  def typedEquals(other : T) : Boolean
}

trait Equals[T] extends HasTypedEquals[T] {
  override def equals(other : Any) =
    other match {
      case other : AnyRef => (
        eq(other) 
        || getClass == other.getClass && typedEquals(other.asInstanceOf[T])
      )
      case _ => false
    }
}

trait EqualsCheckHashCode[T] extends Equals[T] {
  override def equals(other : Any) =
    hashCode == other.hashCode && super.equals(other)
}
