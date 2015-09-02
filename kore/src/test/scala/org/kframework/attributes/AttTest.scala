package org.kframework.attributes

import org.junit.{Assert, Test}

class AttTest {
  @Test def testLocation {
    import org.kframework.kore.KORE._
    val att = Att('Location(1, 2, 3, 4))
    Assert.assertEquals(Some(Location(1, 2, 3, 4)), att.get[Location]("Location"))
  }
}