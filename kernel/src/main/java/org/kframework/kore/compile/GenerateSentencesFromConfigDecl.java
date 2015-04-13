// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Lists;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.definition.Module;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.Sort;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.Option;
import scala.Tuple2;
import scala.collection.immutable.Set;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.Seq;
import static org.kframework.Collections.Set;
import static org.kframework.definition.Constructors.NonTerminal;
import static org.kframework.definition.Constructors.Production;
import static org.kframework.definition.Constructors.Terminal;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 3/27/15.
 */
public class GenerateSentencesFromConfigDecl {

    public static Tuple2<Set<Sentence>, List<Sort>> gen(K body, K ensures, Att att, Module m) {
        if (body instanceof KApply) {
            KApply kapp = (KApply) body;
            if (kapp.klabel().name().equals("#configCell")) {
                if (kapp.klist().size() == 4) {
                    K startLabel = kapp.klist().items().get(0);
                    K endLabel = kapp.klist().items().get(3);
                    if (startLabel.equals(endLabel)) {
                        if (startLabel instanceof KToken) {
                            KToken label = (KToken) startLabel;
                            if (label.sort().equals(Sort("#CellName"))) {
                                String cellName = label.s();
                                String sortName = getSortOfCell(cellName);
                                Sort sort = Sort(sortName);
                                Att cellProperties = getCellPropertiesAsAtt(kapp.klist().items().get(1), cellName, ensures);
                                ConfigurationInfo.Multiplicity multiplicity = convertStringMultiplicity(
                                        cellProperties.<String>get("multiplicity"), body);
                                Tuple2<Set<Sentence>, List<Sort>> childResult = gen(
                                        kapp.klist().items().get(2), null, att, m);
                                Sentence initializer = Production(sort, Seq(Terminal("init" + sort)), Att().add("initializer"));
                                List<ProductionItem> items = Stream.concat(Stream.concat(Stream.of(
                                        Terminal("<" + cellName + ">")), childResult._2().stream()
                                        .map(s -> NonTerminal(s))), Stream.of(Terminal("</" + cellName + ">")))
                                        .collect(Collectors.toList());
                                Sentence cellProduction = Production(sort, items.stream().collect(Collections.toList()),
                                        cellProperties);
                                if (multiplicity == ConfigurationInfo.Multiplicity.STAR) {
                                    Sort bagSort = Sort(sortName + "Bag");
                                    Sentence bagSubsort = Production(bagSort, Seq(NonTerminal(sort)));
                                    Sentence bagUnit = Production(bagSort, Seq(Terminal("." + bagSort.name())));
                                    Sentence bag = Production(bagSort, Seq(NonTerminal(bagSort), NonTerminal(bagSort)),
                                            Att().add("assoc").add("unit", "." + bagSort.name()));
                                    return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction,
                                            bagSubsort, bagUnit, bag)), Lists.newArrayList(bagSort));
                                } else if (multiplicity == ConfigurationInfo.Multiplicity.OPTIONAL) {
                                    Sentence cellUnit = Production(sort, Seq(Terminal("." + sortName)));
                                    return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction, cellUnit)),
                                            Lists.newArrayList(sort));
                                } else {
                                    return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction)),
                                            Lists.newArrayList(sort));
                                }
                            }
                        }
                    }
                }
                throw KExceptionManager.compilerError("Malformed cell in configuration declaration.", body);
            } else if (kapp.klabel().name().equals("#cells")) {
                if (ensures != null) {
                    KToken cellLabel = KToken(Sort("#CellName"), "generatedTop");
                    K generatedTop = KApply(KLabel("#configCell"), cellLabel, KApply(KLabel("#cellPropertyListTerminator")), body, cellLabel);
                    return gen(generatedTop, ensures, att, m);
                }
                List<K> cells = Assoc.flatten(kapp.klabel(), kapp.klist().items(), m);
                Set<Sentence> accumSentences = Set();
                List<Sort> sorts = Lists.newArrayList();
                for (K cell : cells) {
                    Tuple2<Set<Sentence>, List<Sort>> childResult = gen(cell, null, att, m);
                    accumSentences = (Set<Sentence>)accumSentences.$bar(childResult._1());
                    sorts.addAll(childResult._2());
                }
                return Tuple2.apply(accumSentences, sorts);
            }
            //TODO: call generic getSort method of some kind
            return Tuple2.apply(Set(), Lists.newArrayList(m.sortFor().get(kapp.klabel()).get()));
        } else if (body instanceof KToken) {
            KToken ktoken = (KToken) body;
            return Tuple2.apply(Set(), Lists.newArrayList(ktoken.sort()));
        } else if (body instanceof KSequence) {
            return Tuple2.apply(Set(), Lists.newArrayList(Sorts.K()));
        } else {
            throw KExceptionManager.compilerError("Unexpected value found in configuration declaration, expected KToken or KApply", body);
        }
    }

    private static Att getCellPropertiesAsAtt(K k, String cellName, K ensures) {
        Att att = Att();
        if (cellName.equals("k")) {
            att = att.add("maincell");
        }
        if (ensures != null) {
            att = att.add("topcell");
        }
        att = att.add("cell").add("#klabel", "<" + cellName + ">");
        return att.addAll(getCellPropertiesAsAtt(k));
    }

    private static Att getCellPropertiesAsAtt(K k) {
        if (k instanceof KApply) {
            KApply kapp = (KApply) k;
            if (kapp.klabel().name().equals("#cellPropertyListTerminator")) {
                return Att();
            } else if (kapp.klabel().name().equals("#cellPropertyList")) {
                if (kapp.klist().size() == 2) {
                    Tuple2<String, String> attribute = getCellProperty(kapp.klist().items().get(0));
                    return Att().add(attribute._1(), attribute._2()).addAll(getCellPropertiesAsAtt(kapp.klist().items().get(1)));
                }
            }
        }
        throw KExceptionManager.compilerError("Malformed cell properties", k);
    }

    private static Tuple2<String, String> getCellProperty(K k) {
        if (k instanceof KApply) {
            KApply kapp = (KApply) k;
            if (kapp.klabel().name().equals("#cellProperty")) {
                if (kapp.klist().size() == 2) {
                    if (kapp.klist().items().get(0) instanceof KToken) {
                        KToken keyToken = (KToken) kapp.klist().items().get(0);
                        if (keyToken.sort().equals(Sort("#CellName"))) {
                            String key = keyToken.s();
                            if (kapp.klist().items().get(0) instanceof KToken) {
                                KToken valueToken = (KToken) kapp.klist().items().get(1);
                                if (valueToken.sort().equals(Sort("KString"))) {
                                    String value = StringUtil.unquoteKString(valueToken.s());
                                    return Tuple2.apply(key, value);
                                }
                            }
                        }
                    }
                }
            }
        }
        throw KExceptionManager.compilerError("Malformed cell property", k);
    }

    private static String getSortOfCell(String cellName) {
        char[] chars = cellName.toCharArray();
        StringBuilder sb = new StringBuilder();
        sb.append(Character.toUpperCase(chars[0]));
        for (int i = 1; i < chars.length; i++) {
            if (chars[i] == '-' && i + 1 < chars.length && Character.isLowerCase(chars[i+1])) {
                chars[i+1] = Character.toUpperCase(chars[i+1]);
            } else if (chars[i] != '-') {
                sb.append(chars[i]);
            }
        }
        sb.append("Cell");
        return sb.toString();
    }

    private static ConfigurationInfo.Multiplicity convertStringMultiplicity(Option<String> multiplicity, K body) {
        if (multiplicity.isEmpty())
            return ConfigurationInfo.Multiplicity.ONE;
        switch(multiplicity.get()) {
        case "1":
            return ConfigurationInfo.Multiplicity.ONE;
        case "*":
            return ConfigurationInfo.Multiplicity.STAR;
        case "?":
            return ConfigurationInfo.Multiplicity.OPTIONAL;
        default:
            throw KExceptionManager.compilerError("Invalid multiplicity found in cell: " + multiplicity.get(), body);
        }
    }
}
