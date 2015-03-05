// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.kframework.Collections;
import org.kframework.builtin.Sorts;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Lexical;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.Require;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.attributes.Att;
import org.kframework.definition.*;

import org.kframework.kore.AbstractKORETransformer;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KCollection;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import scala.Enumeration.Value;
import scala.Tuple2;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

public class KILtoKORE extends KILTransformation<Object> {

    private org.kframework.kil.loader.Context context;
    private KILtoInnerKORE inner;

    public KILtoKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
        inner = new KILtoInnerKORE(context);
    }

    public org.kframework.definition.Definition apply(Definition d) {
        Set<org.kframework.definition.Require> requires = d.getItems().stream()
                .filter(i -> i instanceof Require).map(i -> apply((Require) i))
                .collect(Collectors.toSet());

        Set<Module> kilModules = d.getItems().stream().filter(i -> i instanceof Module)
                .map(mod -> (Module) mod).collect(Collectors.toSet());

        Module mainModule = kilModules.stream()
                .filter(mod -> mod.getName().equals(d.getMainModule())).findFirst().get();

        HashMap<String, org.kframework.definition.Module> koreModules = new HashMap<>();
        apply(mainModule, kilModules, koreModules);

        // Set<org.kframework.definition.Module> modules = kilModules.map(i ->
        // apply((Module) i))
        // .collect(Collectors.toSet());

        // TODO: handle LiterateDefinitionComments

        return Definition(immutable(requires), immutable(new HashSet<>(koreModules.values())));
    }

    public org.kframework.definition.Require apply(Require i) {
        return Require(new File(i.getValue()));
    }

    public org.kframework.definition.Module apply(Module i, Set<Module> allKilModules,
                                                  Map<String, org.kframework.definition.Module> koreModules) {
        Set<org.kframework.definition.Sentence> items = i.getItems().stream()
                .flatMap(j -> apply(j).stream()).collect(Collectors.toSet());

        Set<String> importedModuleNames = items.stream()
                .filter(imp -> imp instanceof org.kframework.definition.Import)
                .map(imp -> ((org.kframework.definition.Import) imp).moduleName())
                .collect(Collectors.toSet());

        Set<org.kframework.definition.Module> importedModules = allKilModules.stream()
                .filter(mod -> importedModuleNames.contains(mod.getName())).map(mod -> {
                    org.kframework.definition.Module result = koreModules.get(mod.getName());
                    if (result == null) {
                        result = apply(mod, allKilModules, koreModules);
                    }
                    return result;
                }).collect(Collectors.toSet());

        org.kframework.definition.Module newModule = Module(i.getName(), immutable(importedModules), immutable(items),
                inner.convertAttributes(i));
        koreModules.put(newModule.name(), newModule);
        return newModule;
    }

    @SuppressWarnings("unchecked")
    public Set<org.kframework.definition.Sentence> apply(ModuleItem i) {
        if (i instanceof Syntax || i instanceof PriorityExtended) {
            return (Set<org.kframework.definition.Sentence>) apply((ASTNode) i);
        } else {
            return Sets.newHashSet((org.kframework.definition.Sentence) apply((ASTNode) i));
        }
    }

    public org.kframework.definition.Bubble apply(StringSentence sentence) {
        return Bubble(sentence.getType(), sentence.getContent(), inner.convertAttributes(sentence));
    }

    public Context apply(org.kframework.kil.Context c) {
        return Context(inner.apply(c.getBody()), inner.applyOrTrue(c.getRequires()));
    }

    public ModuleComment apply(LiterateModuleComment m) {
        return new org.kframework.definition.ModuleComment(m.getValue(),
                inner.convertAttributes(m));
    }

    public org.kframework.definition.Configuration apply(Configuration kilConfiguration) {
        Cell body = (Cell) kilConfiguration.getBody();
        return Configuration(inner.apply(body), inner.applyOrTrue(kilConfiguration.getEnsures()),
                inner.convertAttributes(kilConfiguration));
    }

    public Rule apply(org.kframework.kil.Rule r) {
        K body = inner.apply(r.getBody());

        AbstractKORETransformer<Set<Tuple2<K, Sort>>> gatherSorts = new AbstractKORETransformer<Set<Tuple2<K, Sort>>>() {
            @Override
            public Set<Tuple2<K, Sort>> apply(KApply k) {
                return processChildren(k.klist());
            }

            @Override
            public Set<Tuple2<K, Sort>> apply(KRewrite k) {
                return Sets.union(apply(k.left()), apply(k.right()));
            }

            @Override
            public Set<Tuple2<K, Sort>> apply(KToken k) {
                return Sets.newHashSet();
            }

            @Override
            public Set<Tuple2<K, Sort>> apply(KVariable k) {
                return (Set<Tuple2<K, Sort>>) k.att().<String>getOptional("sort")
                        .map(x -> Sets.<Tuple2<K, Sort>>newHashSet(new Tuple2((K) k, Sort(x))))
                        .orElseGet(() -> Sets.<Tuple2<K, Sort>>newHashSet());
            }

            @Override
            public Set<Tuple2<K, Sort>> apply(KSequence k) {
                return processChildren(k);
            }

            private Set<Tuple2<K, Sort>> processChildren(KCollection k) {
                return k.stream().map(this::apply).reduce(Sets::union).orElseGet(() -> Sets.newHashSet());
            }

        };

        Set<Tuple2<K, Sort>> expSorts = gatherSorts.apply(body);
        System.out.println("gatherSorts = " + expSorts);

        BinaryOperator<K> makeAnd = (a, b) -> KApply(KLabel("'_andBool_"), KList(a, b));
        K sortPredicates = expSorts
                .stream()
                .map(t -> (K) KApply(KLabel("is" + t._2().name()), KList(t._1())))
                .reduce(makeAnd)
                .orElseGet(() -> KToken(Sorts.Bool(), "true"));


        return Rule(body, makeAnd.apply(inner.applyOrTrue(r.getRequires()), sortPredicates),
                inner.applyOrTrue(r.getEnsures()), inner.convertAttributes(r));
    }

    public org.kframework.definition.SyntaxAssociativity apply(PriorityExtendedAssoc ii) {
        scala.collection.immutable.Set<Tag> tags = toTags(ii.getTags());
        String assocOrig = ii.getAssoc();
        Value assoc = applyAssoc(assocOrig);
        return SyntaxAssociativity(assoc, tags);
    }

    public Value applyAssoc(String assocOrig) {
        // "left", "right", "non-assoc"
        switch (assocOrig) {
        case "left":
            return Associativity.Left();
        case "right":
            return Associativity.Right();
        case "non-assoc":
            return Associativity.NonAssoc();
        default:
            throw new AssertionError("Incorrect assoc string: " + assocOrig);
        }
    }

    public Set<org.kframework.definition.Sentence> apply(PriorityExtended pe) {
        Seq<scala.collection.immutable.Set<Tag>> seqOfSetOfTags = immutable(pe.getPriorityBlocks()
                .stream().map(block -> toTags(block.getProductions()))
                .collect(Collectors.toList()));

        return Sets.newHashSet(SyntaxPriority(seqOfSetOfTags));
    }

    public scala.collection.immutable.Set<Tag> toTags(List<KLabelConstant> labels) {
        return immutable(labels.stream().map(l -> Tag(l.getLabel())).collect(Collectors.toSet()));
    }

    public org.kframework.definition.Sentence apply(Import s) {
        return new org.kframework.definition.Import(s.getName(), inner.convertAttributes(s));
    }

    public Set<org.kframework.definition.Sentence> apply(Syntax s) {
        Set<org.kframework.definition.Sentence> res = new HashSet<>();

        org.kframework.kore.Sort sort = apply(s.getDeclaredSort().getSort());

        // just a sort declaration
        if (s.getPriorityBlocks().size() == 0) {
            res.add(SyntaxSort(sort, inner.convertAttributes(s)));
            return res;
        }

        Function<PriorityBlock, scala.collection.immutable.Set<Tag>> applyToTags = (PriorityBlock b) -> immutable(b
                .getProductions().stream().filter(p -> p.getKLabel() != null).map(p -> Tag(p.getKLabel()))
                .collect(Collectors.toSet()));

        if (s.getPriorityBlocks().size() > 1) {
            res.add(SyntaxPriority(immutable(s.getPriorityBlocks().stream().map(applyToTags)
                    .collect(Collectors.toList()))));
        }

        // there are some productions
        for (PriorityBlock b : s.getPriorityBlocks()) {
            if (!b.getAssoc().equals("")) {
                Value assoc = applyAssoc(b.getAssoc());
                res.add(SyntaxAssociativity(assoc, applyToTags.apply(b)));
            }

            for (Production p : b.getProductions()) {
                // Handle a special case first: List productions have only
                // one item.
                if (p.getItems().size() == 1 && p.getItems().get(0) instanceof UserList) {
                    applyUserList(res, sort, p, (UserList) p.getItems().get(0));
                } else {
                    List<ProductionItem> items = new ArrayList<>();
                    // TODO: when to use RegexTerminal?
                    for (org.kframework.kil.ProductionItem it : p.getItems()) {
                        if (it instanceof NonTerminal) {
                            items.add(NonTerminal(apply(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            throw new AssertionError("Lists should have applyed before.");
                        } else if (it instanceof Lexical) {
                            items.add(RegexTerminal(((Lexical) it).getLexicalRule()));
                        } else if (it instanceof Terminal) {
                            items.add(Terminal(((Terminal) it).getTerminal()));
                        } else {
                            throw new AssertionError("Unhandled case");
                        }
                    }

                    org.kframework.attributes.Att attrs = inner.convertAttributes(p);

                    org.kframework.definition.Production prod = Production(
                            sort,
                            immutable(items),
                            attrs.add(KILtoInnerKORE.PRODUCTION_ID,
                                    "" + System.identityHashCode(p)));

                    res.add(prod);
                }
            }
        }
        return res;
    }

    public void applyUserList(Set<org.kframework.definition.Sentence> res,
                              org.kframework.kore.Sort sort, Production p, UserList userList) {
        boolean nonEmpty = userList.getListType().equals(UserList.ONE_OR_MORE);

        org.kframework.kore.Sort elementSort = apply(userList.getSort());

        // TODO: we're splitting one syntax declaration into three, where to put
        // attributes
        // of original declaration?

        // Using attributes to mark these three rules
        // (to be used when translating those back to single KIL declaration)
        org.kframework.attributes.Att attrs = inner.convertAttributes(p).add(KOREtoKIL.USER_LIST_ATTRIBUTE, p.getSort().getName());

        org.kframework.definition.Production prod1, prod2, prod3;

        String kilProductionId = "" + System.identityHashCode(p);

        // lst ::= lst sep lst
        Att attrsWithKilProductionId = attrs.add(KILtoInnerKORE.PRODUCTION_ID,
                kilProductionId);
        prod1 = Production(sort,
                Seq(NonTerminal(sort), Terminal(userList.getSeparator()), NonTerminal(sort)),
                attrsWithKilProductionId.add("#klabel", p.getKLabel()));

        // lst ::= elem
        prod2 = Production(sort, Seq(NonTerminal(elementSort)), attrsWithKilProductionId);

        // lst ::= .UserList
        prod3 = Production(sort, Seq(Terminal("." + sort.toString())),
                attrsWithKilProductionId.add("#klabel", p.getTerminatorKLabel()));

        res.add(prod1);
        res.add(prod2);
        if (!nonEmpty) {
            res.add(prod3);
        }
    }

    public org.kframework.kore.Sort apply(org.kframework.kil.Sort sort) {
        return Sort(sort.getName());
    }
}
