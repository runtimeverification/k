// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.kframework.kil.Attribute;
import org.kframework.kore.*;
import org.kframework.kore.outer.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.kframework.kore.Collections.*;

public class KOREtoKIL {

    private static RuntimeException NOT_IMPLEMENTED() {
        return NOT_IMPLEMENTED("Not implemented");
    }

    private static RuntimeException NOT_IMPLEMENTED(String s) {
        return new RuntimeException(s);
    }

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
                    List<K> attrs = stream(prod.att().att()).collect(Collectors.toList());
                    if (attrs.size() == 2 && attrs.get(0) instanceof KToken
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
                List<ProductionItem> prod1Items = stream(prods.get(0).items()).collect(
                        Collectors.toList());
                List<ProductionItem> prod2Items = stream(prods.get(1).items()).collect(
                        Collectors.toList());
                List<ProductionItem> prod3Items = stream(prods.get(2).items()).collect(
                        Collectors.toList());

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

                userLists.add(makeUserList(listType.s(), elem, sep,
                        prods.get(0).att().getString(KILtoInnerKORE.PRODUCTION_ID).get()));
            }
        }

        private org.kframework.kil.Syntax makeUserList(String listType, NonTerminal elem,
                Terminal sep, String kilProductionId) {
            org.kframework.kil.Sort listSort = org.kframework.kil.Sort.of(listType);

            org.kframework.kil.UserList userList = new org.kframework.kil.UserList(
                    org.kframework.kil.Sort.of(elem.sort().name()), sep.value(), elem.sort()
                            .name());

            List<org.kframework.kil.ProductionItem> prodItems = new ArrayList<>(1);
            prodItems.add(userList);

            org.kframework.kil.Production prod = new org.kframework.kil.Production(
                    new org.kframework.kil.NonTerminal(listSort), prodItems);

            kilProductionIdToProductionInstance.put(kilProductionId, prod);

            org.kframework.kil.PriorityBlock pb = new org.kframework.kil.PriorityBlock("", prod);
            return new org.kframework.kil.Syntax(new org.kframework.kil.NonTerminal(listSort), pb);
        }
    }

    private org.kframework.kil.loader.Context dummyContext = new org.kframework.kil.loader.Context();

    Map<String, org.kframework.kil.Production> kilProductionIdToProductionInstance = new HashMap<>();

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

        List<Sentence> sentences = scala.collection.JavaConversions.seqAsJavaList(module
                .sentences().toList());
        mod = mod.addModuleItems(convertSentences(sentences));

        mod.setAttributes(convertAttributes(module.att()));
        return mod;
    }

    public List<org.kframework.kil.ModuleItem> convertSentences(List<Sentence> sentences) {
        List<org.kframework.kil.ModuleItem> ret = new ArrayList<>();
        ListProductionCollector listCollector = new ListProductionCollector();
        sentences = listCollector.collectAndRemoveListProds(sentences);
        ret.addAll(listCollector.getResults());

        for (Sentence sentence : sentences) {
            if (sentence instanceof Import) {
                Import anImport = (Import) sentence;
                org.kframework.kil.Import kilImport = new org.kframework.kil.Import(
                        anImport.what());
                kilImport.setAttributes(convertAttributes(anImport.att()));
                ret.add(kilImport);
            } else if (sentence instanceof Bubble) {
                Bubble bubble = (Bubble) sentence;
                org.kframework.kil.StringSentence kilBubble = new org.kframework.kil.StringSentence(
                        bubble.contents(), null, bubble.sentenceType(), null);
                kilBubble.setAttributes(convertAttributes(bubble.att()));
                ret.add(kilBubble);
            } else if (sentence instanceof ModuleComment) {
                ModuleComment moduleComment = (ModuleComment) sentence;
                org.kframework.kil.LiterateModuleComment kilComment =
                // TODO: we lost type information
                new org.kframework.kil.LiterateModuleComment(moduleComment.comment(), null);
                kilComment.setAttributes(convertAttributes(moduleComment.att()));
                ret.add(kilComment);
            } else if (sentence instanceof Configuration) {
                Configuration conf = (Configuration) sentence;
                org.kframework.kil.Configuration kilConf = new org.kframework.kil.Configuration();
                kilConf.setBody(convertConfBody(conf.body()));
                kilConf.setEnsures(convertKBool(conf.ensures()));
                kilConf.setAttributes(convertAttributes(conf.att()));
                ret.add(kilConf);
            } else if (sentence instanceof SyntaxProduction) {
                SyntaxProduction syntaxProduction = (SyntaxProduction) sentence;
                List<org.kframework.kil.ProductionItem> kilProdItems = new ArrayList<>();
                for (ProductionItem it : scala.collection.JavaConversions
                        .seqAsJavaList(syntaxProduction.items())) {
                    kilProdItems.add(convertProdItem(it));
                }
                org.kframework.kil.NonTerminal lhs = new org.kframework.kil.NonTerminal(
                        convertSort(syntaxProduction.sort()));
                org.kframework.kil.Production kilProd = new org.kframework.kil.Production(lhs,
                        kilProdItems);

                kilProductionIdToProductionInstance.put(
                        sentence.att().getString(KILtoInnerKORE.PRODUCTION_ID).get(), kilProd);

                org.kframework.kil.PriorityBlock kilPB = new org.kframework.kil.PriorityBlock("",
                        kilProd);
                ret.add(new org.kframework.kil.Syntax(lhs, kilPB));
            } else if (sentence instanceof SyntaxSort) {
                SyntaxSort syntaxSort = (SyntaxSort) sentence;
                ret.add(new org.kframework.kil.Syntax(new org.kframework.kil.NonTerminal(
                        org.kframework.kil.Sort.of(syntaxSort.sort().name())), new ArrayList<>(0)));
            } else if (sentence instanceof Rule) {
                Rule rule = (Rule) sentence;
                if (rule.body() instanceof KRewrite) {
                    KRewrite body = (KRewrite) rule.body();
                    ret.add(new org.kframework.kil.Rule(convertK(body.left()), convertK(body
                            .right()), convertKBool(rule.requires()),
                            convertKBool(rule.ensures()), dummyContext));
                }
            } else if (sentence instanceof Context) {
                Context context = (Context) sentence;
                org.kframework.kil.Context kilContext = new org.kframework.kil.Context();
                kilContext.setBody(convertK(context.body()));
                kilContext.setRequires(convertKBool(context.requires()));
                ret.add(kilContext);
            } else {
                throw NOT_IMPLEMENTED("Not implemented: KORE.Sentence("
                        + sentence.getClass().getName() + ") -> KIL.Sentence");
            }
        }

        return ret;
    }

    public org.kframework.kil.ProductionItem convertProdItem(ProductionItem prodItem) {
        if (prodItem instanceof NonTerminal) {
            NonTerminal item = (NonTerminal) prodItem;
            return new org.kframework.kil.NonTerminal(convertSort(item.sort()));
        } else if (prodItem instanceof Terminal) {
            Terminal item = (Terminal) prodItem;
            return new org.kframework.kil.Terminal(item.value());
        } else if (prodItem instanceof RegexTerminal) {
            RegexTerminal item = (RegexTerminal) prodItem;
            return new org.kframework.kil.Lexical(item.regex(), null);
        } else {
            throw NOT_IMPLEMENTED();
        }
    }

    public org.kframework.kil.Sort convertSort(Sort sort) {
        return org.kframework.kil.Sort.of(sort.name());
    }

    public org.kframework.kil.Attributes convertAttributes(Attributes koreAttributes) {
        org.kframework.kil.Attributes kilAttributes = new org.kframework.kil.Attributes();
        koreAttributes.stream().forEach(a -> {
            if (a instanceof KApply) {
                KApply attr = (KApply) a;
                KLabel key = attr.klabel();
                KList klist = attr.klist();
                if (klist.size() == 1 && klist.get(0) instanceof KToken) {
                    String value = ((KToken) klist.get(0)).s().s();
                    kilAttributes.add(Attribute.of(key.name(), value));
                } else {
                    throw NOT_IMPLEMENTED();
                }
            } else if (a instanceof KToken) {
                KToken attr = (KToken) a;
                String stringValue = attr.s().s();
                kilAttributes.add(Attribute.of(stringValue, stringValue));
            } else {
                throw NOT_IMPLEMENTED();
            }
        });
        return kilAttributes;
    }

    public org.kframework.kil.Term convertConfBody(K k) {
        if (k instanceof KApply) {
            KApply kApply = (KApply) k;
            KLabel confLabel = kApply.klabel();
            org.kframework.kil.Cell kilCell = new org.kframework.kil.Cell();
            kilCell.setLabel(confLabel.name());
            List<K> args = kApply.list();
            if (args.size() == 1) {
                kilCell.setContents(convertK(args.get(0)));
            } else {
                kilCell.setContents(new org.kframework.kil.Bag(args.stream()
                        .map(kk -> convertK(kk)).collect(Collectors.toList())));
            }
            return kilCell;
        }
        throw new RuntimeException("Unexpected conf body found.");
    }

    public org.kframework.kil.Term convertK(K k) {
        if (k instanceof KSequence) {
            KSequence kSequence = (KSequence) k;
            return new org.kframework.kil.KSequence(kSequence.stream().map(this::convertK)
                    .collect(Collectors.toList()));
        } else if (k instanceof KApply) {
            KApply kApply = (KApply) k;
            // FIXME: a lot of things that are not a KApply are translated to
            // KORE KApply, we need to figure out every one of them and handle
            // here
            return convertKApply(kApply);
        } else if (k instanceof KBag) {
            KBag kBag = (KBag) k;
            List<K> bagItems = kBag.list();
            org.kframework.kil.Bag kilBag = new org.kframework.kil.Bag();
            List<org.kframework.kil.Term> kilBagItems = new ArrayList<>();
            for (K bagItem : bagItems) {
                if (bagItem instanceof KBag) {
                    KBag item = (KBag) bagItem;
                    List<K> kbagItems = item.list();
                    kilBagItems.addAll(kbagItems.stream().map(this::convertK)
                            .collect(Collectors.toList()));
                } else {
                    kilBagItems.add(convertK(bagItem));
                }
            }
            kilBag.setContents(kilBagItems);
            return kilBag;
        } else if (k instanceof KVariable) {
            return convertKVariable((KVariable) k);
        }
        System.out.println(Arrays.toString(Thread.currentThread().getStackTrace()));
        throw NOT_IMPLEMENTED("Not implemented: KORE.K(" + k.getClass().getName()
                + ") -> KIL.Term");
    }

    public org.kframework.kil.Variable convertKVariable(KVariable var) {
        List<K> attrs = stream(var.att().att()).collect(Collectors.toList());
        org.kframework.kil.Sort sort = null;
        for (K k : attrs) {
            if (k instanceof KApply) {
                KApply kApply = (KApply) k;
                if (kApply.klabel().equals(new ConcreteKLabel("sort"))) {
                    List<K> args = kApply.list();
                    if (args.size() == 1 && args.get(0) instanceof KToken) {
                        KToken tok = (KToken) args.get(0);
                        sort = org.kframework.kil.Sort.of(tok.s().s());
                        break;
                    }
                }
            }
        }
        if (sort == null) {
            throw new RuntimeException("Can't figure sort of KVariable");
        }
        return new org.kframework.kil.Variable(var.name(), sort);
    }

    public org.kframework.kil.Term convertKBool(K k) {
        if (k instanceof KBoolean) {
            return null; // FIXME
        }
        return convertK(k);
    }

    public org.kframework.kil.Term convertKApply(KApply kApply) {
        KLabel label = kApply.klabel();
        List<K> contents = kApply.list();
        if (label == Hole$.MODULE$) {
            Sort sort = ((KToken) contents.get(0)).sort();
            return new org.kframework.kil.Hole(org.kframework.kil.Sort.of(sort.name()));
        } else {
            List<K> args = stream(kApply.klist().iterable()).collect(Collectors.toList());
            List<org.kframework.kil.Term> kilTerms = new ArrayList<>();
            for (K arg : args) {
                kilTerms.add(convertK(arg));
            }
            return new org.kframework.kil.TermCons(org.kframework.kil.Sort.of(label.name()),
                    kilTerms, null);
        }
    }
}
