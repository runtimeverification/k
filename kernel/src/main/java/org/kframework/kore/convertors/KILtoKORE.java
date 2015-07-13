// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Associativity;
import org.kframework.definition.Context;
import org.kframework.definition.ModuleComment;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Rule;
import org.kframework.definition.Tag;
import org.kframework.kil.*;
import org.kframework.kore.AbstractKORETransformer;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KCollection;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.generator.SDFHelper;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.Enumeration.Value;
import scala.Tuple2;
import scala.collection.Seq;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.Seq;
import static org.kframework.Collections.Set;
import static org.kframework.Collections.immutable;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class KILtoKORE extends KILTransformation<Object> {

    private org.kframework.kil.loader.Context context;
    private final boolean doDropQuote;
    private KILtoInnerKORE inner;
    private final boolean syntactic;

    public KILtoKORE(org.kframework.kil.loader.Context context, boolean syntactic, boolean doDropQuote) {
        this.context = context;
        this.doDropQuote = doDropQuote;
        inner = new KILtoInnerKORE(context, doDropQuote);
        this.syntactic = syntactic;
    }

    public KILtoKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
        this.doDropQuote = true;
        inner = new KILtoInnerKORE(context, doDropQuote);
        this.syntactic = false;
    }

    public org.kframework.definition.Definition apply(Definition d) {
//        Set<org.kframework.definition.Require> requires = d.getItems().stream()
//                .filter(i -> i instanceof Require).map(i -> apply((Require) i))
//                .collect(Collectors.toSet());

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

        return Definition(
                koreModules.get(mainModule.getName()),
                koreModules.get(mainModule.getName()),
                immutable(new HashSet<>(koreModules.values())));
    }

    public org.kframework.definition.Module apply(Module mainModule, Set<Module> allKilModules,
                                                  Map<String, org.kframework.definition.Module> koreModules) {
        Set<org.kframework.definition.Sentence> items = mainModule.getItems().stream()
                .filter(j -> !(j instanceof org.kframework.kil.Import))
                .flatMap(j -> apply(j).stream()).collect(Collectors.toSet());

        Set<Import> importedModuleNames = mainModule.getItems().stream()
                .filter(imp -> imp instanceof Import)
                .map(imp -> (Import) imp)
                .collect(Collectors.toSet());

        Set<org.kframework.definition.Module> importedModules = importedModuleNames.stream()
                .map(imp -> {
                    Optional<Module> theModule = allKilModules.stream()
                            .filter(m -> m.getName().equals(imp.getName()))
                            .findFirst();
                    if (theModule.isPresent())
                        return theModule.get();
                    else
                        throw KExceptionManager.compilerError("Could not find module: " + imp.getName(), imp);
                })
                .map(mod -> {
                    org.kframework.definition.Module result = koreModules.get(mod.getName());
                    if (result == null) {
                        result = apply(mod, allKilModules, koreModules);
                    }
                    return result;
                }).collect(Collectors.toSet());


        org.kframework.definition.Module newModule = Module(mainModule.getName(), immutable(importedModules), immutable(items),
                inner.convertAttributes(mainModule));
        koreModules.put(newModule.name(), newModule);
        return newModule;
    }

    @SuppressWarnings("unchecked")
    public Set<org.kframework.definition.Sentence> apply(ModuleItem i) {
        if (i instanceof Syntax || i instanceof PriorityExtended) {
            return (Set<org.kframework.definition.Sentence>) apply((ASTNode) i);
        } else if (i instanceof Restrictions) {
            return Sets.newHashSet();
        } else {
            return Sets.newHashSet((org.kframework.definition.Sentence) apply((ASTNode) i));
        }
    }

    public org.kframework.definition.Bubble apply(StringSentence sentence) {
        return Bubble(sentence.getType(), sentence.getContent(), inner.convertAttributes(sentence)
                .add("contentStartLine", sentence.getContentStartLine())
                .add("contentStartColumn", sentence.getContentStartColumn()));
    }

    public Context apply(org.kframework.kil.Context c) {
        if (syntactic)
            return Context(KApply(KLabel("'context")), KToken("true", Sorts.Bool()),
                    inner.convertAttributes(c));
        return Context(inner.apply(c.getBody()), inner.applyOrTrue(c.getRequires()));
    }

    public ModuleComment apply(LiterateModuleComment m) {
        return new org.kframework.definition.ModuleComment(m.getValue(),
                inner.convertAttributes(m));
    }

    public org.kframework.definition.Configuration apply(Configuration kilConfiguration) {
        if (syntactic)
            return Configuration(KApply(KLabel("'configuration")), KToken("true", Sorts.Bool()),
                    inner.convertAttributes(kilConfiguration));
        Cell body = (Cell) kilConfiguration.getBody();
        return Configuration(inner.apply(body), inner.applyOrTrue(kilConfiguration.getEnsures()),
                inner.convertAttributes(kilConfiguration));
    }

    public Rule apply(org.kframework.kil.Rule r) {
        if (syntactic)
            return Rule(KApply(KLabel("'rule")), KToken("true", Sorts.Bool()),
                    KToken("true", Sorts.Bool()), inner.convertAttributes(r));
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
            public Set<Tuple2<K, Sort>> apply(InjectedKLabel k) {
                return Sets.newHashSet();
            }

            @Override
            public Set<Tuple2<K, Sort>> apply(KVariable k) {
                return (Set<Tuple2<K, Sort>>) k.att().<String>getOptional(Attribute.SORT_KEY)
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
        //System.out.println("gatherSorts = " + expSorts);

        BinaryOperator<K> makeAnd = (a, b) -> KApply(KLabel(dropQuote("'_andBool_")), KList(a, b));
        K sortPredicates = expSorts
                .stream()
                .map(t -> (K) KApply(KLabel("is" + t._2().name()), KList(t._1())))
                .reduce(makeAnd)
                .orElseGet(() -> KToken("true", Sorts.Bool()));


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
        return immutable(labels.stream().flatMap(l ->
                SDFHelper.getProductionsForTag(l.getLabel(), context).stream().map(p -> Tag(dropQuote(p.getKLabel())))).collect(Collectors.toSet()));
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
                .getProductions().stream().filter(p -> p.getKLabel() != null).map(p -> Tag(dropQuote(p.getKLabel())))
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
                if (p.containsAttribute("reject")) // skip productions of the old reject type
                    continue;
                // Handle a special case first: List productions have only
                // one item.
                if (p.getItems().size() == 1 && p.getItems().get(0) instanceof UserList) {
                    applyUserList(res, sort, p, (UserList) p.getItems().get(0));
                } else {
                    List<ProductionItem> items = new ArrayList<>();
                    for (org.kframework.kil.ProductionItem it : p.getItems()) {
                        if (it instanceof NonTerminal) {
                            items.add(NonTerminal(apply(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            throw new AssertionError("Lists should have applied before.");
                        } else if (it instanceof Lexical) {
                            String regex;
                            if (p.containsAttribute("regex"))
                                regex = p.getAttribute("regex");
                            else
                                regex = ((Lexical) it).getLexicalRule();
                            RegexTerminal regexTerminal = getRegexTerminal(regex);

                            items.add(regexTerminal);
                        } else if (it instanceof Terminal) {
                            items.add(Terminal(((Terminal) it).getTerminal()));
                        } else {
                            throw new AssertionError("Unhandled case");
                        }
                    }

                    org.kframework.attributes.Att attrs = inner.convertAttributes(p);

                    org.kframework.definition.Production prod;
                    if (p.getKLabel() == null)
                        prod = Production(
                                sort,
                                immutable(items),
                                attrs.add(KILtoInnerKORE.PRODUCTION_ID,
                                        "" + System.identityHashCode(p)));
                    else
                        prod = Production(
                                dropQuote(p.getKLabel()),
                                sort,
                                immutable(items),
                                attrs.add(KILtoInnerKORE.PRODUCTION_ID,
                                        "" + System.identityHashCode(p)));

                    res.add(prod);
                    // handle associativity for the production
                    if (p.containsAttribute("left"))
                        res.add(SyntaxAssociativity(applyAssoc("left"), Set(Tag(dropQuote(p.getKLabel())))));
                    else if (p.containsAttribute("right"))
                        res.add(SyntaxAssociativity(applyAssoc("right"), Set(Tag(dropQuote(p.getKLabel())))));
                    else if (p.containsAttribute("non-assoc"))
                        res.add(SyntaxAssociativity(applyAssoc("non-assoc"), Set(Tag(dropQuote(p.getKLabel())))));
                }
            }
        }
        return res;
    }

    public static RegexTerminal getRegexTerminal(String regex) {
        String precede = "#";
        if (regex.startsWith("(?<!")) { // find the precede pattern in the beginning: (?<!X)
            int depth = 1;
            for (int i = 1; i < regex.length(); i++) {
                if (regex.charAt(i) == '\\') {
                    i++;
                    continue;
                }
                if (regex.charAt(i) == '(') depth++;
                if (regex.charAt(i) == ')') depth--;
                if (depth == 0) {
                    precede = regex.substring("(?<!".length(), i);
                    regex = regex.substring(i + 1);
                    break;
                }
            }
        }
        String follow = "#";
        int followIndex = regex.lastIndexOf("(?!");
        if (followIndex != -1 && regex.endsWith(")")) { // find the follow pattern at the end: (?!X)
            if (!(followIndex > 0 && regex.charAt(followIndex-1) == '\\')) {
                follow = regex.substring(followIndex + "(?!".length(), regex.length() - 1);
                regex = regex.substring(0, followIndex);
            }
        }
        return RegexTerminal(precede, regex, follow);
    }

    public void applyUserList(Set<org.kframework.definition.Sentence> res,
                              org.kframework.kore.Sort sort, Production p, UserList userList) {

        // Transform list declarations of the form Es ::= List{E, ","} into something representable in kore
        org.kframework.kore.Sort elementSort = apply(userList.getSort());

        org.kframework.attributes.Att attrs = inner.convertAttributes(p).add(KOREtoKIL.USER_LIST_ATTRIBUTE, userList.getListType());
        String kilProductionId = "" + System.identityHashCode(p);
        Att attrsWithKilProductionId = attrs.add(KILtoInnerKORE.PRODUCTION_ID, kilProductionId);
        org.kframework.definition.Production prod1, prod3;

        // Es ::= E "," Es
        prod1 = Production(sort,
                Seq(NonTerminal(elementSort), Terminal(userList.getSeparator()), NonTerminal(sort)),
                attrsWithKilProductionId.add("klabel", dropQuote(p.getKLabel())).add("right"));


        // Es ::= ".Es"
        prod3 = Production(sort, Seq(Terminal("." + sort.toString())),
                attrsWithKilProductionId.remove("strict").add("klabel", dropQuote(p.getTerminatorKLabel())));

        res.add(prod1);
        res.add(prod3);
    }

    public String dropQuote(String s) {
        if (doDropQuote) {
            if (s.startsWith("'"))
                return s.substring(1);
            else
                return s;
        } else {
            return s;
        }
    }

    public org.kframework.kore.Sort apply(org.kframework.kil.Sort sort) {
        return Sort(sort.getName());
    }
}
