// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.kore.KLabel;
import scala.Tuple2;

/**
 * Convert all operations involving associativity to use the standard data types List,Set,Map,Bag.
 * This algorithm is currently incomplete and may not correctly handle all cases. However, it should
 * be capable of handling most cases that were handleable in the old KIL framework, including
 * multiplicity * cells, although there may be some incorrect behaviors because it has not been
 * thoroughly tested and there are several known issues that will cause some patterns to behave
 * incorrectly. In some cases it may also be more inefficient than the old framework because it will
 * sometimes choose a backtracking choice operation instead of a set or map lookup.
 *
 * <p>In addition to standard maps, a filtered map is also available. A filtered map is meant to be
 * used for cases in which structural equality is too strong for checking key equality. The proposed
 * solution internally encodes a map with entries {@code K |-> V} as a "filtered" map whose entries
 * are of the form {@code FK |-> (K, V)}. The implementation of the standard map operations
 * (including computing FK) is left to the user. For example, {@code
 * $RV_MATCH/c-semantics/semantics/cpp14/language/common/map.k} defines a filtered map having {@code
 * CPPType} as a key, but filtered through the {@code stripType} function. This option is selected
 * by using {@code #filterMapChoice} as argument for the {@code choice} attribute. Then the {@code
 * filterElement} attribute is used to specify the actual map constructor (which takes as arguments
 * the filtered key and the pair), while the {@code element} attribute specifies the production that
 * will be used to match or construct an entry in terms of an unfiltered key and the value.
 * Currently for construction this production must be a function, which the user must define to
 * rewrite into a filtered entry. The compiler translates matching using this production, so in the
 * end construction and matching will be transparent to the user and allow syntax identical to an
 * ordinary map.
 */
public class ConvertDataStructureToLookup {
  public static Map<KLabel, KLabel> collectionFor(Module m) {
    return stream(m.productions())
        .filter(p -> p.att().contains(Att.ASSOC()) && p.att().contains(Att.ELEMENT()))
        .flatMap(
            p -> {
              Set<Tuple2<KLabel, KLabel>> set = new HashSet<>();
              set.add(Tuple2.apply(p.klabel().get(), p.klabel().get()));
              if (p.att().contains(Att.UNIT())) {
                set.add(Tuple2.apply(KLabel(p.att().get(Att.UNIT())), p.klabel().get()));
              }
              if (p.att().contains(Att.ELEMENT())) {
                set.add(Tuple2.apply(KLabel(p.att().get(Att.ELEMENT())), p.klabel().get()));
              }
              if (p.att().contains(Att.FILTER_ELEMENT())) {
                set.add(Tuple2.apply(KLabel(p.att().get(Att.FILTER_ELEMENT())), p.klabel().get()));
              }
              if (p.att().contains(Att.WRAP_ELEMENT())) {
                set.add(Tuple2.apply(KLabel(p.att().get(Att.WRAP_ELEMENT())), p.klabel().get()));
              }
              return set.stream();
            })
        .distinct()
        .collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));
  }
}
