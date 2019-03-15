// Copyright (c) 2016-2019 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Lists;
import com.google.common.collect.Multiset;
import org.kframework.TopologicalSort;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.Assoc;
import org.kframework.kore.FoldK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.compile.RewriteToTop;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Convert all operations involving associativity to use the standard data types
 * List,Set,Map,Bag. This algorithm is currently incomplete and may not correctly
 * handle all cases. However, it should be capable of handling most cases
 * that were handleable in the old KIL framework, including multiplicity * cells,
 * although there may be some incorrect behaviors because it has not been thoroughly
 * tested and there are several known issues that will cause some patterns to behave
 * incorrectly.
 * In some cases it may also be more inefficient than the old framework because
 * it will sometimes choose a backtracking choice operation instead of a set or map
 * lookup.
 *
 * In addition to standard maps, a filtered map is also available. A filtered
 * map is meant to be used for cases in which structural equality is too strong
 * for checking key equality.
 * The proposed solution internally encodes a map with entries {@code K |-> V}
 * as a "filtered" map whose entries are of the form {@code FK |-> (K, V)}.
 * The implementation of the standard map operations (including computing FK)
 * is left to the user. For example,
 * {@code $RV_MATCH/c-semantics/semantics/cpp14/language/common/map.k}
 * defines a filtered map having {@code CPPType} as a key, but filtered
 * through the {@code stripType} function.
 * This option is selected by using {@code #filterMapChoice} as argument for
 * the {@code choice} attribute. Then the {@code filterElement} attribute
 * is used to specify the actual map constructor (which takes as arguments
 * the filtered key and the pair), while the {@code element} attribute
 * specifies the production that will be used to match or construct an
 * entry in terms of an unfiltered key and the value.
 * Currently for construction this production must be a function, which
 * the user must define to rewrite into a filtered entry.
 * The compiler translates matching using this production, so in the
 * end construction and matching will be transparent to the user and
 * allow syntax identical to an ordinary map.
 */
public class ConvertDataStructureToLookup {


    private Set<KApply> state = new HashSet<>();
    private Multiset<KVariable> vars = HashMultiset.create();

    void reset() {
        state.clear();
        vars.clear();
        counter = 0;
    }

    private final Module m;
    private final Map<KLabel, KLabel> collectionFor;
    private final boolean matchOnConsList;

    public ConvertDataStructureToLookup(Module m, boolean matchOnConsList) {
        this.m = m;
        collectionFor = collectionFor(m);
        this.matchOnConsList = matchOnConsList;
    }

    public ConvertDataStructureToLookup(ConvertDataStructureToLookup copy) {
        this.m = copy.m;
        this.collectionFor = copy.collectionFor;
        this.matchOnConsList = copy.matchOnConsList;
    }

    public static Map<KLabel, KLabel> collectionFor(Module m) {
        return stream(m.productions())
                .filter(p -> p.att().contains(Attribute.ASSOCIATIVE_KEY) && p.att().contains("element"))
                .flatMap(p -> {
                    Set<Tuple2<KLabel, KLabel>> set = new HashSet<>();
                    set.add(Tuple2.apply(p.klabel().get(), p.klabel().get()));
                    if (p.att().contains(Attribute.UNIT_KEY)) {
                        set.add(Tuple2.apply(KLabel(p.att().get(Attribute.UNIT_KEY)), p.klabel().get()));
                    }
                    if (p.att().contains("element")) {
                        set.add(Tuple2.apply(KLabel(p.att().get("element")), p.klabel().get()));
                    }
                    if (p.att().contains("filterElement")) {
                        set.add(Tuple2.apply(KLabel(p.att().get("filterElement")), p.klabel().get()));
                    }
                    if (p.att().contains("wrapElement")) {
                        set.add(Tuple2.apply(KLabel(p.att().get("wrapElement")), p.klabel().get()));
                    }
                    return set.stream();
                }).distinct().collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));
    }

    public static Set<KLabel> filteredMapConstructors(Module m) {
        return stream(m.productions())
                .filter(p -> p.att().contains(Attribute.ASSOCIATIVE_KEY) && p.att().contains("filterElement"))
                .map(p -> p.klabel().get())
                .distinct()
                .collect(Collectors.toSet());
    }

    private Rule convert(Rule rule) {
        reset();
        gatherVars(rule.body(), vars);
        gatherVars(rule.requires(), vars);
        gatherVars(rule.ensures(), vars);
        K body = transform(rule.body());
        return Rule(
                body,
                addSideCondition(rule.requires()),
                rule.ensures(),
                rule.att());
    }

    private Context convert(Context context) {
        reset();
        gatherVars(context.body(), vars);
        gatherVars(context.requires(), vars);
        K body = transform(context.body());
        return new Context(
                body,
                addSideCondition(context.requires()),
                context.att());
    }


    /**
     * Collects all the variables in {@code term} into {@code vars}.
     */
    void gatherVars(K term, Multiset<KVariable> vars) {
        new VisitK() {
            @Override
            public void apply(KVariable v) {
                vars.add(v);
                super.apply(v);
            }
        }.apply(term);
    }

    /**
     * Adds lookups to the side condition in sorted order in which they must be performed.
     * Lookups are sorted based on dependencies between each other,
     * but non-lookup operations appear in no particular order with respect to the lookups.
     * @param requires Previous side condition, if any.
     * @return Side condition generated by this compiler pass + previous side condition.
     */
    K addSideCondition(K requires) {
        Optional<KApply> sideCondition = getSortedLookups().reduce(BooleanUtils::and);
        if (!sideCondition.isPresent()) {
            return requires;
        } else if (requires.equals(BooleanUtils.TRUE) && sideCondition.isPresent()) {
            return sideCondition.get();
        } else {
            // we order lookups before the requires clause so that the fresh constant
            // matching side condition remains last. This is necessary in order to
            // ensure that fresh constants in rule RHSs are consecutive
            return BooleanUtils.and(sideCondition.get(), requires);
        }
    }

    /**
     * Sorts lookups based on their dependencies with each other. Non-lookups (i.e.
     * everything except #match, #setChoice, and #mapChoice) are in no particular
     * order in this ordering, since they can always be inferred later to occur
     * at the final step after all other variables are bound.
     * @return
     */
    private Stream<KApply> getSortedLookups() {
        List<Tuple2<KApply, KApply>> edges = new ArrayList<>();
        for (KApply k1 : state) {
            Multiset<KVariable> rhsVars = HashMultiset.create();
            if (k1.klabel().name().equals("Set:in")) {
                continue;
            }
            gatherVars(k1.klist().items().get(1), rhsVars);
            for (KApply k2 : state) {
                Multiset<KVariable> lhsVars = HashMultiset.create();
                if (k2.klabel().name().equals("Set:in")) {
                    continue;
                }
                gatherVars(k2.klist().items().get(0), lhsVars);
                for (KVariable var : rhsVars) {
                    if (lhsVars.contains(var)) {
                        if (k1 != k2) {
                            edges.add(Tuple2.apply(k2, k1));
                            break;
                        }
                    }
                }
            }
        };
        List<KApply> topologicalSorted = mutable(TopologicalSort.tsort(immutable(edges)).toList());
        return state.stream().sorted((k1, k2) -> (topologicalSorted.indexOf(k1) - topologicalSorted.indexOf(k2)));
    }

    private int counter = 0;
    KVariable newDotVariable() {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

    /**
     * For the cell bag sorts with multiplicity *, add the single-element wrapper around individual cells.
     */
    private K infer(K term) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                for (KLabel collectionLabel : collectionFor.keySet()) {
                    Optional<String> wrapElement = m.attributesFor().apply(collectionLabel).getOptional("wrapElement");
                    if (wrapElement.isPresent()) {
                        KLabel wrappedLabel = KLabel(wrapElement.get());
                        KLabel elementLabel = KLabel(m.attributesFor().apply(collectionLabel).get("element"));
                        if (k.klabel().equals(elementLabel)) {
                            return k;
                        }
                        if (k.klabel().equals(wrappedLabel)) {
                            if (collectionIsMap(collectionLabel)) {
                                // Map
                                return KApply(elementLabel, super.apply(k.klist().items().get(0)), super.apply(k));
                            } else {
                                return KApply(elementLabel, super.apply(k));
                            }
                        }
                    }
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    public boolean collectionIsMap(KLabel collectionLabel) {
        return m.attributesFor().apply(collectionLabel).contains(Attribute.COMMUTATIVE_KEY)
                && !m.attributesFor().apply(collectionLabel).contains(Attribute.IDEMPOTENT_KEY)
                && !m.attributesFor().apply(collectionLabel).contains(Att.bag());
    }

    private boolean isThread = false;

    private K transform(K body) {
        if (body instanceof KRewrite && ((KRewrite) body).left() instanceof KApply && collectionFor.containsKey(((KApply) ((KRewrite) body).left()).klabel())) {
            // this is a rule intended to implement one of the collection operations; do not transform it.
            return body;
        }
        //maintain the list of variables in the term so that we can deduce that a particular variable is unconstrained
        Multiset<KVariable> varConstraints = HashMultiset.create();
        gatherVars(RewriteToTop.toLeft(body), varConstraints);
        return new TransformK() {
            public K apply(KApply k) {
                if (KLabels.KSEQ.equals(k.klabel()))
                    return super.apply(k);
                if (k.klabel().name().equals("#Thread")) {
                    K global = apply(k.klist().items().get(0));
                    K id = apply(k.klist().items().get(1));
                    isThread = true;
                    K thread = apply(k.klist().items().get(2));
                    isThread = false;
                    K otherThreads = apply(k.klist().items().get(3));
                    return KApply(k.klabel(), global, id, thread, otherThreads);
                }

                if (collectionFor.containsKey(k.klabel())) {
                    if (isThread) {
                        isThread = false;
                        K res = super.apply(k);
                        isThread = true;
                        return res;
                    } else {
                        KLabel collectionLabel = collectionFor.get(k.klabel());
                        Att att = m.attributesFor().apply(collectionLabel);
                        //assumed assoc
                        KApply left = (KApply) RewriteToTop.toLeft(k);
                        List<K> components = Assoc.flatten(collectionLabel, Collections.singletonList(left), m);
                        if (att.contains(Attribute.COMMUTATIVE_KEY)) {
                            if (att.contains(Attribute.IDEMPOTENT_KEY)) {
                                // Set
                                return convertSet(k, collectionLabel, components);
                            } else {
                                if (att.contains(Att.bag()))
                                    // Bag
                                    // TODO(dwightguth): handle bags
                                    return super.apply(k);
                                else
                                    // Map
                                    return convertMap(k, collectionLabel, components, varConstraints);
                            }
                        } else {
                            // List
                            return convertList(k, collectionLabel, components);
                        }
                    }
                } else {
                    return super.apply(k);
                }
            }

            /**
             * Convert a list pattern, requiring that there is at most one list variable component.
             * Individual items may appear before and after the frame variable, which can be
             * translated into efficient operatations at the beginning and end of the list.
             */
            private K convertList(KApply k, KLabel collectionLabel, List<K> components) {
                if (rhsOf == null) {
                    //left hand side
                    KVariable frame = null;
                    List<K> elementsLeft = new ArrayList<K>();
                    List<K> elementsRight = new ArrayList<K>();
                    KLabel elementLabel = KLabel(m.attributesFor().apply(collectionLabel).get("element"));
                    boolean isRight = false; // true for components later than the frame variable.
                    //build the components of the list from the flattened KApply.
                    for (K component : components) {
                        if (component instanceof KVariable) {
                            if (frame != null) {
                                throw KEMException.internalError("Unsupported associative matching on List. Found variables " + component + " and " + frame, k);
                            }
                            frame = (KVariable) component;
                            isRight = true;
                        } else if (component instanceof KApply) {
                            KApply kapp = (KApply) component;
                            boolean needsWrapper = false;
                            if (kapp.klabel().equals(elementLabel)
                                    || (needsWrapper = kapp.klabel().equals(getWrapElement(collectionLabel)))) {
                                if (kapp.klist().size() != 1 && !needsWrapper) {
                                    throw KEMException.internalError("Unexpected arity of list element: " + kapp.klist().size(), kapp);
                                }
                                K stack = lhsOf;
                                // setting lhsOf prevents inner lists from being translated to rewrites,
                                lhsOf = kapp;

                                // overloading means the following two apply functions are actually different methods
                                (isRight ? elementsRight : elementsLeft).add(needsWrapper ? super.apply(kapp) : super.apply(kapp.klist().items().get(0)));

                                lhsOf = stack;
                            } else {
                                throw KEMException.internalError("Unexpected term in list, not a list element.", kapp);
                            }
                        }
                    }
                    K list;
                    if (elementsRight.size() == 0 && matchOnConsList) {
                        K tail;
                        if (frame == null) {
                            tail = KApply(KLabel(m.attributesFor().apply(collectionLabel).get(Attribute.UNIT_KEY)));
                        } else {
                            tail = frame;
                        }
                        list = Lists.reverse(elementsLeft).stream().map(e -> (K)KApply(elementLabel, e)).reduce(tail, (res, el) -> KApply(collectionLabel, el, res));
                    } else {
                        list = newDotVariable();
                        // Ctx[ListItem(5) Frame ListItem(X) ListItem(foo(Y))] => Ctx [L]
                        // requires Frame := range(L, 1, 2)
                        // andBool 5 := L[0]
                        // andBool X := L[-2]
                        // andBool foo(Y) := L[-1]
                        if (frame != null) {
                            state.add(KApply(KLabel("#match"), frame, KApply(KLabel("List:range"), list,
                                    KToken(Integer.toString(elementsLeft.size()), Sorts.Int()),
                                    KToken(Integer.toString(elementsRight.size()), Sorts.Int()))));
                        } else {
                            KLabel unit = KLabel(m.attributesFor().apply(collectionLabel).get("unit"));
                            // Ctx[.List] => Ctx[L] requires L ==K range(L, 0, 0)
                            state.add(KApply(KLabel("_==K_"), KApply(unit), KApply(KLabel("List:range"), list,
                                    KToken(Integer.toString(elementsLeft.size()), Sorts.Int()),
                                    KToken(Integer.toString(elementsRight.size()), Sorts.Int()))));
                        }
                        for (int i = 0; i < elementsLeft.size(); i++) {
                            K element = elementsLeft.get(i);
                            state.add(KApply(KLabel("#match"), element, KApply(KLabel("List:get"), list, KToken(Integer.toString(i), Sorts.Int()))));
                        }
                        for (int i = 0; i < elementsRight.size(); i++) {
                            K element = elementsRight.get(i);
                            state.add(KApply(KLabel("#match"), element, KApply(KLabel("List:get"), list, KToken(Integer.toString(i - elementsRight.size()), Sorts.Int()))));
                        }
                    }
                    if (lhsOf == null) {
                        if (!hasRewrite(k)) {
                            return list;
                        }
                        // An outermost list may contain nested rewrites, so the term
                        // is translated into a rewrite from compiled match into the original right-hand side.
                        return KRewrite(list, infer(RewriteToTop.toRight(k)));
                    } else {
                        return list;
                    }
                } else {
                    return infer(super.apply(k));
                }
            }


            /**
             * Convert a map pattern, requiring that there is at most one map variable component.
             * Map keys must either be a variable, or bound elsewhere in the rule.
             * Map value patterns become additional matching constraints on lookups in the map.
             */
            private K convertMap(KApply k, KLabel collectionLabel, List<K> components, Multiset<KVariable> varConstraints) {
                if (rhsOf == null) {
                    //left hand side
                    KVariable frame = null;
                    Map<K, K> elements = new LinkedHashMap<>();
                    //build the components of the map from the flattened KApply.
                    for (K component : components) {
                        if (component instanceof KVariable) {
                            if (frame != null) {
                                throw KEMException.internalError("Unsupported associative matching on Map. Found variables " + component + " and " + frame, k);
                            }
                            frame = (KVariable) component;
                        } else if (component instanceof KApply) {

                            boolean needsWrapper = false;
                            KApply kapp = (KApply) component;
                            if (kapp.klabel().equals(KLabel(m.attributesFor().apply(collectionLabel).get("element")))
                                    || (needsWrapper = kapp.klabel().equals(getWrapElement(collectionLabel)))) {
                                if (kapp.klist().size() != 2 && !needsWrapper) {
                                    throw KEMException.internalError("Unexpected arity of map element: " + kapp.klist().size(), kapp);
                                }
                                K stack = lhsOf;
                                // setting lhsOf prevents inner lists from being translated to rewrites,
                                lhsOf = kapp;

                                elements.put(super.apply(kapp.klist().items().get(0)),
                                        needsWrapper ? super.apply(kapp) : super.apply(kapp.klist().items().get(1)));

                                lhsOf = stack;
                            } else {
                                throw KEMException.internalError("Unexpected term in map, not a map element.", kapp);
                            }
                        }
                    }
                    KVariable map = newDotVariable();
                    // K1,Ctx[K1 |-> K2 K3] => K1,Ctx[M] requires K3 := M[K1<-undef] andBool K1 := choice(M) andBool K2 := M[K1]
                    KLabel remove = KLabel(m.attributesFor().apply(collectionLabel).getOptional("remove").orElse("_[_<-undef]"));
                    if (frame != null) {
                        state.add(KApply(KLabel("#match"), frame, elements.keySet().stream().reduce(map, (a1, a2) -> KApply(remove, a1, a2))));
                    } else {
                        KLabel unit = KLabel(m.attributesFor().apply(collectionLabel).get("unit"));
                        state.add(KApply(KLabel("_==K_"), KApply(unit), elements.keySet().stream().reduce(map, (a1, a2) -> KApply(remove, a1, a2))));
                    }
                    for (Map.Entry<K, K> element : elements.entrySet()) {
                        // TODO(dwightguth): choose better between lookup and choice.
                        if (element.getKey() instanceof KVariable && varConstraints.count(element.getKey()) == 1) {
                            KLabel choice = KLabel(m.attributesFor().apply(collectionLabel).getOptional("choice").orElse("#mapChoice"));
                            state.add(KApply(choice, element.getKey(), map));
                        }
                        KLabel lookup = KLabel(m.attributesFor().apply(collectionLabel).getOptional("lookup").orElse("Map:lookup"));
                        state.add(KApply(KLabel("#match"), element.getValue(), KApply(lookup, map, element.getKey())));
                    }
                    if (lhsOf == null) {
                        if (!hasRewrite(k)) {
                            return map;
                        }
                        // An outermost map may contain nested rewrites, so the term
                        // is translated into a rewrite from compiled match into the original right-hand side.
                        return KRewrite(map, infer(RewriteToTop.toRight(k)));
                    } else {
                        return map;
                    }
                } else {
                    return infer(super.apply(k));
                }
            }

            private KLabel getWrapElement(KLabel collectionLabel) {
                return KLabel(m.attributesFor().apply(collectionLabel).get("wrapElement"));
            }


            /**
             * Convert a set pattern, requiring that there is at most one set variable component.
             * Set elements without variables become membership checks in the map, whereas Set elements
             * with variables trigger iteration over the set with matching on each element.
             */
            private K convertSet(KApply k, KLabel collectionLabel, List<K> components) {
                if (rhsOf == null) {
                    //left hand side
                    KVariable frame = null;
                    Set<K> elements = new LinkedHashSet<>();
                    KLabel elementLabel = KLabel(m.attributesFor().apply(collectionLabel).get("element"));
                    //build the components of the set from the flattened KApply.
                    for (K component : components) {
                        if (component instanceof KVariable) {
                            if (frame != null) {
                                throw KEMException.internalError("Unsupported associative matching on Set. Found variables " + component + " and " + frame, k);
                            }
                            frame = (KVariable) component;
                        } else if (component instanceof KApply) {
                            KApply kapp = (KApply) component;

                            boolean needsWrapper = false;
                            if (kapp.klabel().equals(elementLabel)
                                    || (needsWrapper = kapp.klabel().equals(getWrapElement(collectionLabel)))) {
                                if (kapp.klist().size() != 1 && !needsWrapper) {
                                    throw KEMException.internalError("Unexpected arity of set element: " + kapp.klist().size(), kapp);
                                }
                                K stack = lhsOf;
                                // setting lhsOf prevents inner lists from being translated to rewrites,
                                lhsOf = kapp;

                                // overloading means the following two apply functions are actually different methods
                                elements.add(needsWrapper ? super.apply(kapp) : super.apply(kapp.klist().items().get(0)));

                                lhsOf = stack;
                            } else {
                                throw KEMException.internalError("Unexpected term in set, not a set element.", kapp);
                            }
                        }
                    }
                    KVariable set = newDotVariable();
                    K accum = set;
                    // Ctx[SetItem(K1) K2] => Ctx[S] requires K1 := choice(S) andBool K2 := S -Set SetItem(K1)
                    // Ctx[SetItem(5) SetItem(6) K] => Ctx[S] requires 5 in S andBool 6 in S andBool K := S -Set SetItem(5) SetItem(6)
                    for (K element : elements) {
                        // TODO(dwightguth): choose better between lookup and choice.
                        Multiset<KVariable> vars = HashMultiset.create();
                        gatherVars(element, vars);
                        if (vars.isEmpty()) {
                            state.add(KApply(KLabel("Set:in"), element, accum));
                        } else {
                            //set choice
                            state.add(KApply(KLabel("#setChoice"), element, accum));
                        }
                        accum = KApply(KLabel("Set:difference"), accum, KApply(elementLabel, element));
                    }
                    KLabel unit = KLabel(m.attributesFor().apply(collectionLabel).get("unit"));
                    if (frame != null) {
                        state.add(KApply(KLabel("#match"), frame, accum));
                    } else {
                        state.add(KApply(KLabel("_==K_"), KApply(unit), accum));
                    }
                    if (lhsOf == null) {
                        if (!hasRewrite(k)) {
                            return set;
                        }
                        // An outermost set may contain nested rewrites, so the term
                        // is translated into a rewrite from compiled match into the original right-hand side.
                        return KRewrite(set, infer(RewriteToTop.toRight(k)));
                    } else {
                        return set;
                    }
                } else {
                    return infer(super.apply(k));
                }
            }

            private K lhsOf;
            private K rhsOf;

            @Override
            public K apply(KRewrite k) {
                lhsOf = k;
                K l = apply(k.left());
                lhsOf = null;
                rhsOf = k;
                K r = apply(k.right());
                rhsOf = null;
                if (l != k.left() || r != k.right()) {
                    return KRewrite(l, r, k.att());
                } else {
                    return k;
                }
            }
        }.apply(body);
    }

    private Boolean hasRewrite(KApply k) {
        return new FoldK<Boolean>() {
            public Boolean unit() {
                return false;
            }

            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }

            public Boolean apply(KRewrite rew) {
                return true;
            }
        }.apply(k);
    }


    public Sentence convert(Sentence s) {
        if (s.att().contains(Attribute.LEMMA_KEY)
                || s.att().contains(Attribute.SMT_LEMMA_KEY)
                || s.att().contains(Attribute.PATTERN_FOLDING_KEY)) {
            return s;
        } else if (s instanceof Rule) {
            return convert((Rule) s);
        } else if (s instanceof Context) {
            return convert((Context) s);
        } else {
          return s;
        }
    }

    public static boolean isLookupKLabel(KLabel k) {
        return k.name().equals("#match") || k.name().equals("#mapChoice") || k.name().equals("#filterMapChoice") || k.name().equals("#setChoice");
    }

    public static boolean isLookupKLabel(KApply k) {
        return isLookupKLabel(k.klabel());
    }

}
