// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore;

import java.util.Arrays;
import java.util.List;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import scala.Tuple2;
import scala.collection.Map;

/** Created by dwightguth on 6/17/15. */
public class AttCompare {
  private final K k;
  private final List<Att.Key> attNames;

  public AttCompare(K k, Att.Key... attNames) {
    this.k = k;
    this.attNames = Arrays.asList(attNames);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    AttCompare that = (AttCompare) o;

    return attEquals(this.k, that.k);
  }

  private boolean attEquals(K thisK, K thatK) {
    if (!filterAtt(thisK.att()).equals(filterAtt(thatK.att()))) {
      return false;
    }
    if ((thisK instanceof KToken && thatK instanceof KToken)
        || (thisK instanceof KVariable && thatK instanceof KVariable)
        || (thisK instanceof InjectedKLabel && thatK instanceof InjectedKLabel)) {
      return thisK.equals(thatK);
    } else if (thisK instanceof KApply thisKItem && thatK instanceof KApply thatKItem) {
      return thisKItem.klabel().equals(thatKItem.klabel())
          && attEquals(thisKItem.klist().items(), thatKItem.klist().items());
    } else if (thisK instanceof KSequence && thatK instanceof KSequence) {
      return attEquals(((KSequence) thisK).items(), ((KSequence) thatK).items());
    } else if (thisK instanceof KRewrite thisKR && thatK instanceof KRewrite thatKR) {
      return attEquals(thisKR.left(), thatKR.left()) && attEquals(thisKR.right(), thatKR.right());
    } else {
      return false;
    }
  }

  private boolean attEquals(List<K> thisK, List<K> thatK) {
    if (thisK.size() != thatK.size()) {
      return false;
    }
    for (int i = 0; i < thisK.size(); i++) {
      if (!attEquals(thisK.get(i), thatK.get(i))) {
        return false;
      }
    }
    return true;
  }

  private Map<Tuple2<Att.Key, String>, Object> filterAtt(Att att) {
    return Collections.mutable(att.att()).entrySet().stream()
        .filter(e -> attNames.contains(e.getKey()._1))
        .map(e -> Tuple2.apply(e.getKey(), e.getValue()))
        .collect(Collections.toMap());
  }

  @Override
  public String toString() {
    return k.toString();
  }

  @Override
  public int hashCode() {
    return k.hashCode();
  }
}
