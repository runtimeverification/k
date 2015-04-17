// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Lists;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.definition.Constructors;
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

    /**
     * Takes a configuration declaration and returns the sentences that it desugars into.
     *
     * Cells of multiplicity 1 desugar into an initializer production, an initializer rule, and a cell production.
     * Cells of multiplicity * desugar into an initializer production, an initializer rule, a cell production, and a bag
     * sort to represent a bag of those cells.
     * Cells of multiplicity ? desugar into an initializer production, an initializer rule, a cell production, and an
     * empty production indicating the absence of that cell.
     *
     * Currently the implementation does not handle initializer rules; we will address this eventually.
     * @param body The body of the configuration declaration.
     * @param ensures The ensures clause of the configuration declaration.
     * @param att The attributes of the configuration declaration.
     * @param m The module the configuration declaration exists in.
     * @return A set of sentences representing the configuration declaration.
     */
    public static Set<Sentence> gen(K body, K ensures, Att att, Module m) {
        return genInternal(body, ensures, att, m)._1();
    }

    /**
     * Recurses over a cell and computes all the sentences corresponding to its children, and then generates
     * the sentences for itself.
     * @param term The term to be processed. Can be either a cell, in which case it processes that cell,
     *             a list of cells, in which case it processes each of those cells, or a noncell, in which case
     *             its parent is treated as a leaf cell.
     * @param ensures The ensures clause from the configuration declaration. This is appended to the initializer of
     *                the top cell, but not any other cells. The algorithm assumes this will be null if and only if
     *                it is not the top cell of a configuration declaration.
     * @param att The attributes of the configuration declaration. Appended to all cell productions generated.
     * @param m The module the configuration declaration is in. Used to get the sort of leaf cells.
     * @return A tuple of the sentences generated and a list of the sorts of the children of the cell.
     */
    private static Tuple2<Set<Sentence>, List<Sort>> genInternal(K term, K ensures, Att att, Module m) {
        if (term instanceof KApply) {
            KApply kapp = (KApply) term;
            if (kapp.klabel().name().equals("#configCell")) {
                // is a single cell
                if (kapp.klist().size() == 4) {
                    K startLabel = kapp.klist().items().get(0);
                    K endLabel = kapp.klist().items().get(3);
                    if (startLabel.equals(endLabel)) {
                        if (startLabel instanceof KToken) {
                            KToken label = (KToken) startLabel;
                            if (label.sort().equals(Sort("#CellName"))) {
                                String cellName = label.s();
                                K cellPropertiesTerm = kapp.klist().items().get(1);
                                K cellContents = kapp.klist().items().get(2);
                                return computeSentencesOfWellFormedCell(term, att, m, cellName,
                                        getCellPropertiesAsAtt(cellPropertiesTerm, cellName, ensures),
                                        cellContents);
                            }
                        }
                    }
                }
                throw KExceptionManager.compilerError("Malformed cell in configuration declaration.", term);
            } else if (kapp.klabel().name().equals("#cells")) {
                //is a cell bag, and thus represents the multiple children of its parent cell
                if (ensures != null) {
                    //top level cell, therefore, should be the children of the generatedTop cell
                    KToken cellLabel = KToken(Sort("#CellName"), "generatedTop");
                    K generatedTop = KApply(KLabel("#configCell"), cellLabel, KApply(KLabel("#cellPropertyListTerminator")), term, cellLabel);
                    return genInternal(generatedTop, ensures, att, m);
                }
                List<K> cells = Assoc.flatten(kapp.klabel(), kapp.klist().items(), m);
                Set<Sentence> accumSentences = Set();
                List<Sort> sorts = Lists.newArrayList();
                for (K cell : cells) {
                    //for each cell, generate the child and inform the parent of the children it contains
                    Tuple2<Set<Sentence>, List<Sort>> childResult = genInternal(cell, null, att, m);
                    accumSentences = (Set<Sentence>)accumSentences.$bar(childResult._1());
                    sorts.addAll(childResult._2());
                }
                return Tuple2.apply(accumSentences, sorts);
            }
            //TODO: call generic getSort method of some kind
            // child of a leaf cell. Generate no productions, but inform parent that it has a child of a particular sort.
            return Tuple2.apply(Set(), Lists.newArrayList(m.sortFor().get(kapp.klabel()).get()));
        } else if (term instanceof KToken) {
            // child of a leaf cell. Generate no productions, but inform parent that it has a child of a particular sort.
            KToken ktoken = (KToken) term;
            return Tuple2.apply(Set(), Lists.newArrayList(ktoken.sort()));
        } else if (term instanceof KSequence) {
            // child of a leaf cell. Generate no productions, but inform parent that it has a child of a particular sort.
            return Tuple2.apply(Set(), Lists.newArrayList(Sorts.K()));
        } else {
            throw KExceptionManager.compilerError("Unexpected value found in configuration declaration, expected KToken or KApply", term);
        }
    }

    private static Tuple2<Set<Sentence>, List<Sort>> computeSentencesOfWellFormedCell(K cell, Att configAtt, Module m, String cellName, Att cellProperties, K cellContents) {
        String sortName = getSortOfCell(cellName);
        Sort sort = Sort(sortName);
        ConfigurationInfo.Multiplicity multiplicity = convertStringMultiplicity(
                cellProperties.<String>get("multiplicity"), cell);

        Tuple2<Set<Sentence>, List<Sort>> childResult = genInternal(
                cellContents, null, configAtt, m);
        List<ProductionItem> items = Stream.concat(Stream.concat(Stream.of(
                Terminal("<" + cellName + ">")), childResult._2().stream()
                .map(Constructors::NonTerminal)), Stream.of(Terminal("</" + cellName + ">")))
                .collect(Collectors.toList());

        // syntax Cell ::= "initCell" [initializer]
        // syntax Cell ::= "<cell>" Children... "</cell>" [cell, cellProperties, configDeclAttributes]
        Sentence initializer = Production("init" + sort.name(), sort, Seq(Terminal("init" + sort.name())), Att().add("initializer"));
        Sentence cellProduction = Production("<" + cellName + ">", sort, items.stream().collect(Collections.toList()),
                cellProperties.addAll(configAtt));

        if (multiplicity == ConfigurationInfo.Multiplicity.STAR) {
            // syntax CellBag ::= Cell [cellbag]
            // syntax CellBag ::= ".CellBag"
            // syntax CellBag  ::= CellBag CellBag [assoc, unit(.CellBag)]
            Sort bagSort = Sort(sortName + "Bag");
            Sentence bagSubsort = Production(bagSort, Seq(NonTerminal(sort)), Att().add("cellbag"));
            Sentence bagUnit = Production("." + bagSort.name(), bagSort, Seq(Terminal("." + bagSort.name())));
            Sentence bag = Production("_" + bagSort + "_", bagSort, Seq(NonTerminal(bagSort), NonTerminal(bagSort)),
                    Att().add("assoc").add("unit", "." + bagSort.name()));

            return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction,
                    bagSubsort, bagUnit, bag)), Lists.newArrayList(bagSort));
        } else if (multiplicity == ConfigurationInfo.Multiplicity.OPTIONAL) {
            // syntax Cell ::= ".Cell"
            Sentence cellUnit = Production("." + sortName, sort, Seq(Terminal("." + sortName)));

            return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction, cellUnit)),
                    Lists.newArrayList(sort));
        } else {
            return Tuple2.apply((Set<Sentence>)childResult._1().$bar(Set(initializer, cellProduction)),
                    Lists.newArrayList(sort));
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
