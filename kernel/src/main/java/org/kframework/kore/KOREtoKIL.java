// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.kframework.kore.outer.*;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import static org.kframework.kore.outer.Constructors.iterable;

public class KOREtoKIL {

    public static org.kframework.kil.Definition convert(Definition definition) {
        List<org.kframework.kil.DefinitionItem> items = new ArrayList<>();

        for (Require r : iterable(definition.requires())) {
            items.add(convert(r));
        }

        for (Module m : iterable(definition.modules())) {
            items.add(convert(m));
        }

        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        def.setItems(items);
        return def;
    }

    public static org.kframework.kil.Require convert(Require require) {
        return new org.kframework.kil.Require(require.file().getPath());
    }

    public static org.kframework.kil.Module convert(Module module) {
        org.kframework.kil.Module mod = new org.kframework.kil.Module(
                module.name());

        List<Sentence> sentences = scala.collection.JavaConversions
                .seqAsJavaList(module.sentences().toList());
        mod = mod.setModuleItems(convert(sentences));

        mod.setAttributes(convert(module.att()));
        return mod;
    }

    public static List<org.kframework.kil.ModuleItem> convert(
            List<Sentence> sentences) {
        List<org.kframework.kil.ModuleItem> ret = new ArrayList<>();
        Iterator<Sentence> iter = sentences.iterator();

        while (iter.hasNext()) {
            Sentence sentence = iter.next();
            if (sentence instanceof Context) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof Rule) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof ModuleComment) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof Import) {
                Import i = (Import) sentence;
                org.kframework.kil.ModuleItem item = new org.kframework.kil.Import(
                        i.what());
                item.setAttributes(convert(i.att()));
                ret.add(item);
            } else if (sentence instanceof SyntaxPriority) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof SyntaxSort) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof SyntaxProduction) {
                SyntaxProduction prod = (SyntaxProduction) sentence;
                KList attrs = prod.att().klist();
                if (attrs.size() != 0
                        && ((ConsKList) attrs).head() instanceof KToken
                        && ((KToken) ((ConsKList) attrs).head()).sort().name()
                                .equals("userList")) {
                    // Found a userlist translation. Next 3 rules should be
                    // describing the UserList
                    String listType = ((KToken) ((ConsKList) attrs).head()).s()
                            .s();
                    Sentence sentence2 = iter.next();
                    Sentence sentence3 = iter.next(); // consume last sentence
                    // FIXME: rules are getting reordered
                    ret.add(makeUserList(listType, sentence3, sentence));
                } else {
                    throw new RuntimeException("Unhandled case");
                }
            } else if (sentence instanceof Configuration) {
                throw new RuntimeException("Unhandled case");
            } else if (sentence instanceof Bubble) {
                Bubble bubble = (Bubble) sentence;
                org.kframework.kil.ModuleItem item = new org.kframework.kil.StringSentence(
                        bubble.contents(), null, bubble.ty(), null);
                item.setAttributes(convert(sentence.att()));
                ret.add(item);
            } else {
                throw new RuntimeException("Unhandled case");
            }
        }

        return ret;
    }

    public static org.kframework.kil.Syntax makeUserList(String listType,
            Sentence s1, Sentence s2) {
        SyntaxProduction prod1 = (SyntaxProduction) s1;
        List<ProductionItem> prod1Items = scala.collection.JavaConversions
                .seqAsJavaList(prod1.items());

        SyntaxProduction prod2 = (SyntaxProduction) s2;
        List<ProductionItem> prod2Items = scala.collection.JavaConversions
                .seqAsJavaList(prod2.items());

        org.kframework.kil.Sort listSort = convert(prod1.sort());
        org.kframework.kil.Sort elementSort = org.kframework.kil.Sort
                .of(((NonTerminal) prod2Items.get(0)).sort().name());
        String sep = ((Terminal) prod1Items.get(1)).value();

        List<org.kframework.kil.PriorityBlock> pbs = new ArrayList<>();
        org.kframework.kil.PriorityBlock pb = new org.kframework.kil.PriorityBlock();
        pbs.add(pb);
        List<org.kframework.kil.Production> prods = new ArrayList<>();
        pb.setProductions(prods);

        org.kframework.kil.UserList userList = new org.kframework.kil.UserList(
                elementSort, sep, listType);

        List<org.kframework.kil.ProductionItem> prodItems = new ArrayList<>();

        org.kframework.kil.Production prod = new org.kframework.kil.Production(
                new org.kframework.kil.NonTerminal(listSort), prodItems);
        prods.add(prod);

        prodItems.add(userList);

        return new org.kframework.kil.Syntax(
                new org.kframework.kil.NonTerminal(listSort), pbs);
    }

    public static org.kframework.kil.Sort convert(Sort sort) {
        return org.kframework.kil.Sort.of(sort.name());
    }

    public static org.kframework.kil.Attributes convert(Attributes attrs) {
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
