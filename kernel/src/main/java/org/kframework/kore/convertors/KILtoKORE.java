// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.compile.checks.CheckListDecl;
import org.kframework.definition.Associativity;
import org.kframework.definition.FlatModule;
import org.kframework.definition.ModuleComment;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Tag;
import org.kframework.kil.*;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.utils.errorsystem.KEMException;
import scala.Enumeration.Value;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class KILtoKORE extends KILTransformation<Object> {

    private org.kframework.kil.loader.Context context;
    private final boolean syntactic;
    private final boolean kore;
    private String moduleName;

    public KILtoKORE(org.kframework.kil.loader.Context context, boolean syntactic, boolean kore) {
        this.context = context;
        this.syntactic = syntactic;
        this.kore = kore;
    }

    public KILtoKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
        this.syntactic = false;
        kore = false;
    }

    public FlatModule toFlatModule(Module m) {
        CheckListDecl.check(m);
        moduleName = m.getName();

        Set<org.kframework.definition.Sentence> items = m.getItems().stream()
                .filter(j -> !(j instanceof org.kframework.kil.Import))
                .flatMap(j -> apply(j).stream()).collect(Collectors.toSet());

        Set<String> importedModuleNames = m.getItems().stream()
                .filter(imp -> imp instanceof Import)
                .map(imp -> ((Import) imp).getName())
                .collect(Collectors.toSet());

        Att att = convertAttributes(m);

        return new FlatModule(moduleName, immutable(importedModuleNames), immutable(items), att);
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
                immutable(new HashSet<>(koreModules.values())), Att());
    }

    public org.kframework.definition.Module apply(Module mainModule, Set<Module> allKilModules,
                                                  Map<String, org.kframework.definition.Module> koreModules) {
        FlatModule mainFlatModule = toFlatModule(mainModule);
        Set<FlatModule> flatModules = allKilModules.stream().map(m -> toFlatModule(m)).collect(Collectors.toSet());
        org.kframework.definition.Module result = mainFlatModule.toModule(immutable(flatModules), JavaConverters.mapAsScalaMapConverter(koreModules).asScala(), Seq());
        return result;
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

    public org.kframework.definition.Sentence apply(SortSynonym synonym) {
      return new org.kframework.definition.SortSynonym(synonym.newSort, synonym.oldSort, convertAttributes(synonym));
    }

    public org.kframework.definition.Bubble apply(StringSentence sentence) {
        org.kframework.attributes.Att attrs =
            convertAttributes(sentence)
            .add("contentStartLine", Integer.class, sentence.getContentStartLine())
            .add("contentStartColumn", Integer.class, sentence.getContentStartColumn());

        String label = sentence.getLabel();
        if (!label.isEmpty()) {
            attrs = attrs.add("label", sentence.getType().equals("alias") ? label : moduleName + "." + label);
        }

        return Bubble(sentence.getType(), sentence.getContent(), attrs);
    }


    public ModuleComment apply(LiterateModuleComment m) {
        return new org.kframework.definition.ModuleComment(m.getValue(),
                convertAttributes(m));
    }

    public org.kframework.definition.SyntaxAssociativity apply(PriorityExtendedAssoc ii) {
        scala.collection.Set<Tag> tags = toTags(ii.getTags(), ii);
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
        Seq<scala.collection.Set<Tag>> seqOfSetOfTags = immutable(pe.getPriorityBlocks()
                .stream().map(block -> toTags(block.getProductions(), pe))
                .collect(Collectors.toList()));

        return Sets.newHashSet(SyntaxPriority(seqOfSetOfTags));
    }

    public scala.collection.Set<Tag> toTags(List<Tag> labels, ASTNode loc) {
        return immutable(labels.stream().flatMap(l -> {
            java.util.Set<Production> productions = context.tags.get(l.name());
            if (productions.isEmpty())
                throw KEMException.outerParserError("Could not find any productions for tag: " + l.name(), loc.getSource(), loc.getLocation());
            return productions.stream().map(p -> Tag(p.getKLabel(kore)));
        }).collect(Collectors.toSet()));
    }

    public Set<org.kframework.definition.Sentence> apply(Syntax s) {
        Set<org.kframework.definition.Sentence> res = new HashSet<>();

        org.kframework.kore.Sort sort = s.getDeclaredSort().getSort();

        // just a sort declaration
        if (s.getPriorityBlocks().size() == 0) {
            res.add(SyntaxSort(sort, convertAttributes(s)));
            return res;
        }

        Function<PriorityBlock, scala.collection.Set<Tag>> applyToTags = (PriorityBlock b) -> immutable(b
                .getProductions().stream().filter(p -> p.getKLabel(kore) != null).map(p -> Tag(p.getKLabel(kore)))
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
                            NonTerminal nt = (NonTerminal)it;
                            items.add(NonTerminal(nt.getSort(), nt.getName()));
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

                    org.kframework.attributes.Att attrs = convertAttributes(p);

                    org.kframework.definition.Production prod;
                    if (p.getKLabel(kore) == null)
                        prod = Production(
                                immutable(p.getParams()),
                                sort,
                                immutable(items),
                                attrs);
                    else
                        prod = Production(
                                KLabel(p.getKLabel(kore), immutable(p.getParams())),
                                sort,
                                immutable(items),
                                attrs);

                    res.add(prod);
                    // handle associativity for the production
                    if (p.containsAttribute("left"))
                        res.add(SyntaxAssociativity(applyAssoc("left"), Set(Tag(p.getKLabel(kore)))));
                    else if (p.containsAttribute("right"))
                        res.add(SyntaxAssociativity(applyAssoc("right"), Set(Tag(p.getKLabel(kore)))));
                    else if (p.containsAttribute("non-assoc"))
                        res.add(SyntaxAssociativity(applyAssoc("non-assoc"), Set(Tag(p.getKLabel(kore)))));
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
            if (!(followIndex > 0 && regex.charAt(followIndex - 1) == '\\')) {
                follow = regex.substring(followIndex + "(?!".length(), regex.length() - 1);
                regex = regex.substring(0, followIndex);
            }
        }
        return RegexTerminal(precede, regex, follow);
    }

    public void applyUserList(Set<org.kframework.definition.Sentence> res,
                              org.kframework.kore.Sort sort, Production p, UserList userList) {

        // Transform list declarations of the form Es ::= List{E, ","} into something representable in kore
        org.kframework.kore.Sort elementSort = userList.getSort();

        org.kframework.attributes.Att attrs = convertAttributes(p).add(Att.userList(), userList.getListType());
        String kilProductionId = "" + System.identityHashCode(p);
        org.kframework.definition.Production prod1, prod3;

        // Es ::= E "," Es
        prod1 = Production(KLabel(p.getKLabel(kore), immutable(p.getParams())), sort,
                Seq(NonTerminal(elementSort), Terminal(userList.getSeparator()), NonTerminal(sort)),
                attrs.add("right"));


        // Es ::= ".Es"
        prod3 = Production(KLabel(p.getTerminatorKLabel(kore), immutable(p.getParams())), sort, Seq(Terminal("." + sort.toString())),
                attrs.remove("format").remove("strict").add("klabel", p.getTerminatorKLabel(false)));

        res.add(prod1);
        res.add(prod3);
    }

    public static org.kframework.attributes.Att convertAttributes(ASTNode t) {
        Attributes attributes = t.getAttributes();

        Map<String, String> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue().toString();
                    if (keyString.equals("klabel")) {
                        return Tuple2.apply("klabel", valueString);
                    } else {
                        return Tuple2.apply(keyString, valueString);
                    }

                }).collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));

        return Att.from(attributesSet)
                .addAll(attributesFromLocation(t.getLocation()))
                .addAll(attributesFromSource(t.getSource()));
    }

    private static Att attributesFromSource(Source source) {
        if (source != null) {
            return Att().add(Source.class, source);
        }
        return Att();
    }

    private static org.kframework.attributes.Att attributesFromLocation(Location location) {
        if (location != null) {
            return Att().add(Location.class, location);
        } else
            return Att();
    }

}
