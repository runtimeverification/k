package org.kframework.kore;

import static org.kframework.kore.Constructors.Seq;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
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
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kore.outer.ProductionItem;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;

class KILtoKORE {
    public org.kframework.kore.outer.Definition convert(Definition d) {
        Set<org.kframework.kore.outer.Require> requires = d.getItems().stream()
                .filter(i -> i instanceof Require)
                .map(i -> convert((Require) i)).collect(Collectors.toSet());

        Set<org.kframework.kore.outer.Module> modules = d.getItems().stream()
                .filter(i -> i instanceof Module).map(i -> convert((Module) i))
                .collect(Collectors.toSet());

        return Definition(immutable(requires), immutable(modules));
    }

    private org.kframework.kore.outer.Require convert(Require i) {
        return Require(new File(i.getValue()));
    }

    private org.kframework.kore.outer.Module convert(Module i) {
        Set<org.kframework.kore.outer.Sentence> items = i.getItems().stream()
                .flatMap(j -> convert(j).stream()).collect(Collectors.toSet());
        return Module(i.getName(), immutable(items), convert(i.getAttributes()));
    }

    private Set<org.kframework.kore.outer.Sentence> convert(ModuleItem i) {
        if (i instanceof Import) {
            return Sets.newHashSet(convert((Import) i));
        } else if (i instanceof Syntax) {
            return convert((Syntax) i);
        } else if (i instanceof StringSentence) {
            // need a bubble here
            throw new RuntimeException("Not implemented");
        } else if (i instanceof LiterateModuleComment) {
            return Sets.newHashSet(new org.kframework.kore.outer.ModuleComment(
                    ((LiterateModuleComment) i).getValue(), convert(i
                            .getAttributes())));
        } else if (i instanceof Sentence) {
            // I think this should have left as a bubble...
            throw new RuntimeException("Found a sentence while translating KIL");
        } else if (i instanceof PriorityExtended) {
            throw new RuntimeException("Not implemented");
        } else if (i instanceof PriorityExtendedAssoc) {
            throw new RuntimeException("Not implemented");
        } else if (i instanceof Restrictions) {
            throw new RuntimeException("Not implemented");
        } else {
            throw new RuntimeException("Unhandled case");
        }
    }

    private org.kframework.kore.outer.Sentence convert(Import s) {
        return new org.kframework.kore.outer.Import(s.getName(),
                convert(s.getAttributes()));
    }

    private Set<org.kframework.kore.outer.Sentence> convert(Syntax s) {
        Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();

        org.kframework.kore.Sort sort = convert(s.getDeclaredSort().getSort());

        // just a sort declaration
        if (s.getPriorityBlocks().size() == 0) {
            res.add(SyntaxSort(sort, convert(s.getAttributes())));
            return res;
        }

        // there are some productions
        for (PriorityBlock b : s.getPriorityBlocks()) {
            for (Production p : b.getProductions()) {
                // Handle a special case first: List productions have only
                // one item.
                if (p.getItems().size() == 1
                        && p.getItems().get(0) instanceof UserList) {
                    convertUserList(res, sort, p, (UserList) p.getItems()
                            .get(0));
                } else {
                    List<ProductionItem> items = new ArrayList<>();
                    // TODO: when to use RegexTerminal?
                    for (org.kframework.kil.ProductionItem it : p.getItems()) {
                        if (it instanceof NonTerminal) {
                            items.add(new org.kframework.kore.outer.NonTerminal(
                                    convert(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            throw new RuntimeException(
                                    "Lists should have converted before.");
                        } else if (it instanceof Lexical) {
                            // TODO: not sure what to do
                        } else if (it instanceof Terminal) {
                            items.add(Terminal(((Terminal) it).getTerminal()));
                        } else {
                            throw new RuntimeException("Unhandled case");
                        }
                    }

                    org.kframework.kore.outer.SyntaxProduction prod = SyntaxProduction(
                            sort, immutable(items), convert(p.getAttributes()));

                    res.add(prod);
                }
            }
        }
        return res;
    }

    private void convertUserList(Set<org.kframework.kore.outer.Sentence> res,
            org.kframework.kore.Sort sort, Production p, UserList userList) {
        org.kframework.kore.Sort elementSort = convert(userList.getSort());

        // TODO: attributes are probably wrong

        org.kframework.kore.outer.SyntaxProduction prod1, prod2, prod3;

        // lst ::= lst sep lst
        prod1 = SyntaxProduction(
                sort,
                Seq(NonTerminal(sort), Terminal(userList.getSeparator()),
                        NonTerminal(sort)), convert(p.getAttributes()));

        // lst ::= elem
        prod2 = SyntaxProduction(sort, Seq(NonTerminal(elementSort)),
                convert(p.getAttributes()));

        // lst ::= .UserList
        prod3 = SyntaxProduction(sort, Seq(Terminal("." + sort.toString())),
                convert(p.getAttributes()));

        res.add(prod1);
        res.add(prod2);
        res.add(prod3);
    }

    private org.kframework.kore.Sort convert(org.kframework.kil.Sort sort) {
        return Sort(sort.getName());
    }

    private org.kframework.kore.Attributes convert(Attributes attributes) {
        Set<K> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue()
                            .toString();

                    return (K) KApply(
                            KLabel(keyString),
                            KList(KToken(Sort("AttributeValue"),
                                    KString(valueString))));
                }).collect(Collectors.toSet());

        return Attributes(KList(attributesSet));
    }
}