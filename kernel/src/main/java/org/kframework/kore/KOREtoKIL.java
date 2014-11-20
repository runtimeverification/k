// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.kframework.kore.outer.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.kframework.kore.outer.Constructors.*;

public class KOREtoKIL {

    class ListProductionCollector {
        private Map<KString, List<SyntaxProduction>> listProds;
        private List<org.kframework.kil.Syntax> userLists;

        public List<org.kframework.kil.Syntax> getResults() {
            return userLists;
        }

        public List<Sentence> collectAndRemoveListProds(List<Sentence> sentences) {
            listProds = new HashMap<>();
            List<Sentence> ret = new ArrayList<>(sentences);
            Iterator<Sentence> iter = ret.iterator();
            while (iter.hasNext()) {
                Sentence sentence = iter.next();
                if (sentence instanceof SyntaxProduction) {
                    SyntaxProduction prod = (SyntaxProduction) sentence;
                    List<K> attrs = prod.att().stream().collect(Collectors.toList());
                    if (attrs.size() == 2
                            && attrs.get(0) instanceof KToken
                            && ((KToken) attrs.get(0)).sort().name().equals("userList")) {
                        // TODO: Handle ZERO_OR_MORE/ONE_OR_MORE attributes
                        KString listType = ((KToken) attrs.get(1)).s();
                        List<SyntaxProduction> prods = listProds.get(listType);
                        if (prods == null) {
                            prods = new ArrayList<>(3);
                            listProds.put(listType, prods);
                        }
                        prods.add(prod);
                        iter.remove();
                    }
                }
            }
            generateUserLists();
            return ret;
        }

        private void generateUserLists() {
            userLists = new ArrayList<>();
            for (Map.Entry<KString, List<SyntaxProduction>> entry : listProds.entrySet()) {
                KString listType = entry.getKey();
                List<SyntaxProduction> prods = entry.getValue();
                if (prods.size() != 3) {
                    throw new RuntimeException("Found list with " + prods.size() + " elements.");
                }
                List<ProductionItem> prod1Items = stream(prods.get(0).items()).collect(Collectors.toList());
                List<ProductionItem> prod2Items = stream(prods.get(1).items()).collect(Collectors.toList());
                List<ProductionItem> prod3Items = stream(prods.get(2).items()).collect(Collectors.toList());

                Terminal sep;
                NonTerminal elem;

                if (prod1Items.size() == 3) {
                    sep = (Terminal) prod1Items.get(1);
                } else if (prod2Items.size() == 3) {
                    sep = (Terminal) prod2Items.get(1);
                } else {
                    sep = (Terminal) prod3Items.get(1);
                }

                if (prod1Items.size() == 1 && prod1Items.get(0) instanceof NonTerminal) {
                    elem = (NonTerminal) prod1Items.get(0);
                } else if (prod2Items.get(0) instanceof NonTerminal) {
                    elem = (NonTerminal) prod2Items.get(0);
                } else {
                    elem = (NonTerminal) prod3Items.get(0);
                }

                userLists.add(makeUserList(listType.s(), elem, sep));
            }
        }

        private org.kframework.kil.Syntax makeUserList(String listType, NonTerminal elem, Terminal sep) {
            org.kframework.kil.Sort listSort = org.kframework.kil.Sort.of(listType);

            org.kframework.kil.UserList userList = new org.kframework.kil.UserList(
                    org.kframework.kil.Sort.of(elem.sort().name()),
                    sep.value(),
                    elem.sort().name());

            List<org.kframework.kil.ProductionItem> prodItems = new ArrayList<>(1);
            prodItems.add(userList);

            org.kframework.kil.Production prod = new org.kframework.kil.Production(
                    new org.kframework.kil.NonTerminal(listSort), prodItems);

            org.kframework.kil.PriorityBlock pb = new org.kframework.kil.PriorityBlock("", prod);
            return new org.kframework.kil.Syntax(new org.kframework.kil.NonTerminal(listSort), pb);
        }
    }

    public org.kframework.kil.Definition convertDefinition(Definition definition) {
        List<org.kframework.kil.DefinitionItem> items = new ArrayList<>();

        for (Require r : iterable(definition.requires())) {
            items.add(convertRequire(r));
        }

        for (Module m : iterable(definition.modules())) {
            items.add(convertModule(m));
        }

        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        def.setItems(items);
        return def;
    }

    public org.kframework.kil.Require convertRequire(Require require) {
        return new org.kframework.kil.Require(require.file().getPath());
    }

    public org.kframework.kil.Module convertModule(Module module) {
        org.kframework.kil.Module mod = new org.kframework.kil.Module(module.name());

        List<Sentence> sentences = scala.collection.JavaConversions
                .seqAsJavaList(module.sentences().toList());
        mod = mod.setModuleItems(convertSentences(sentences));

        mod.setAttributes(convertAttributes(module.att()));
        return mod;
    }

    public List<org.kframework.kil.ModuleItem> convertSentences(List<Sentence> sentences) {
        List<org.kframework.kil.ModuleItem> ret = new ArrayList<>();
        ListProductionCollector listCollector = new ListProductionCollector();
        sentences = listCollector.collectAndRemoveListProds(sentences);
        ret.addAll(listCollector.getResults());
        return ret;
    }

    public org.kframework.kil.Sort convertSort(Sort sort) {
        return org.kframework.kil.Sort.of(sort.name());
    }

    public org.kframework.kil.Attributes convertAttributes(Attributes attrs) {
        org.kframework.kil.Attributes ret = new org.kframework.kil.Attributes();
        KList attrsKList = attrs.klist();
        while (attrsKList.size() != 0) {
            ConsKList cons = (ConsKList) attrsKList;
            KApply attr = (KApply) cons.head();
            KLabel key = attr.klabel();
            String value = ((KString) ((ConsKList) ((ConsKList) attr.klist())
                    .tail()).head()).s();
            // TODO: I think it's not possible to translate attributes back,
            // we lose a lot of information while translating.
            attrsKList = cons.tail();
        }
        return ret;
    }
}
