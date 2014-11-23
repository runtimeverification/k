// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
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
import org.kframework.kil.Term;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kore.outer.*;

import scala.Enumeration.Value;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;

public class KILtoKORE extends KILTransformation<Object> {

    public KILtoInnerKORE inner = new KILtoInnerKORE();

    public org.kframework.kore.outer.Definition apply(Definition d) {
        Set<org.kframework.kore.outer.Require> requires = d.getItems().stream()
                .filter(i -> i instanceof Require).map(i -> apply((Require) i))
                .collect(Collectors.toSet());

        Set<org.kframework.kore.outer.Module> modules = d.getItems().stream()
                .filter(i -> i instanceof Module).map(i -> apply((Module) i))
                .collect(Collectors.toSet());

        // TODO: handle LiterateDefinitionComments

        return Definition(immutable(requires), immutable(modules));
    }

    public org.kframework.kore.outer.Require apply(Require i) {
        return Require(new File(i.getValue()));
    }

    public org.kframework.kore.outer.Module apply(Module i) {
        Set<org.kframework.kore.outer.Sentence> items = i.getItems().stream()
                .flatMap(j -> apply(j).stream()).collect(Collectors.toSet());
        return Module(i.getName(), immutable(items), inner.apply(i.getAttributes()));
    }

    public Set<org.kframework.kore.outer.Sentence> apply(ModuleItem i) {
        if (i instanceof Import) {
            return Sets.newHashSet(apply((Import) i));
        } else if (i instanceof Syntax) {
            return apply((Syntax) i);
        } else if (i instanceof StringSentence) {
            StringSentence sentence = (StringSentence) i;
            return Sets.newHashSet(new org.kframework.kore.outer.Bubble(sentence.getType(),
                    sentence.getContent(), inner.apply(sentence.getAttributes())));
        } else if (i instanceof LiterateModuleComment) {
            return Sets.newHashSet(new org.kframework.kore.outer.ModuleComment(
                    ((LiterateModuleComment) i).getValue(), inner.apply(i.getAttributes())));
        } else if (i instanceof org.kframework.kil.Configuration) {
            Configuration kilConfiguration = (org.kframework.kil.Configuration) i;
            Cell body = (Cell) kilConfiguration.getBody();
            Term kilEnsures = kilConfiguration.getEnsures();

            return Sets.newHashSet(Configuration(inner.apply(body),
                    inner.applyOrTrue(kilConfiguration.getEnsures()),
                    inner.apply(kilConfiguration.getAttributes())));
        } else if (i instanceof PriorityExtended) {
            return apply((PriorityExtended) i);
        } else if (i instanceof PriorityExtendedAssoc) {
            return apply((PriorityExtendedAssoc) i);
        } else if (i instanceof Restrictions) {
            throw new RuntimeException("Not implemented");
        } else if (i instanceof org.kframework.kil.Context) {
            org.kframework.kil.Context c = (org.kframework.kil.Context) i;

            return Sets.newHashSet(Context(inner.apply(c.getBody()),
                    inner.applyOrTrue(c.getRequires())));
        } else if (i instanceof org.kframework.kil.Rule) {
            return Sets.newHashSet(apply((org.kframework.kil.Rule) i));
        } else {
            throw new RuntimeException("Unhandled case:" + i.getClass());
        }
    }

    public Rule apply(org.kframework.kil.Rule r) {
        return Rule(inner.apply(r.getBody()), inner.applyOrTrue(r.getRequires()),
                inner.applyOrTrue(r.getEnsures()), inner.apply(r.getAttributes()));
    }

    public Set<org.kframework.kore.outer.Sentence> apply(PriorityExtendedAssoc ii) {
        scala.collection.immutable.Set<Tag> tags = toTags(ii.getTags());
        String assocOrig = ii.getAssoc();
        Value assoc = applyAssoc(assocOrig);
        return Sets.newHashSet(SyntaxAssociativity(assoc, tags));
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
            throw new RuntimeException("Incorrect assoc string: " + assocOrig);
        }
    }

    public Set<org.kframework.kore.outer.Sentence> apply(PriorityExtended pe) {
        Seq<scala.collection.immutable.Set<Tag>> seqOfSetOfTags = immutable(pe.getPriorityBlocks()
                .stream().map((block) -> {
                    return toTags(block.getProductions());
                }).collect(Collectors.toList()));

        return Sets.newHashSet(SyntaxPriority(seqOfSetOfTags));
    }

    public scala.collection.immutable.Set<Tag> toTags(List<KLabelConstant> labels) {
        return immutable(labels.stream().map(l -> Tag(l.getLabel())).collect(Collectors.toSet()));
    }

    public org.kframework.kore.outer.Sentence apply(Import s) {
        return new org.kframework.kore.outer.Import(s.getName(), inner.apply(s.getAttributes()));
    }

    public Set<org.kframework.kore.outer.Sentence> apply(Syntax s) {
        Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();

        org.kframework.kore.Sort sort = apply(s.getDeclaredSort().getSort());

        // just a sort declaration
        if (s.getPriorityBlocks().size() == 0) {
            res.add(SyntaxSort(sort, inner.apply(s.getAttributes())));
            return res;
        }

        Function<PriorityBlock, scala.collection.immutable.Set<Tag>> applyToTags = (PriorityBlock b) -> immutable(b
                .getProductions().stream().map(p -> Tag(p.getKLabel()))
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
                            items.add(new org.kframework.kore.outer.NonTerminal(
                                    apply(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            throw new RuntimeException("Lists should have applyed before.");
                        } else if (it instanceof Lexical) {
                            // TODO: not sure what to do
                        } else if (it instanceof Terminal) {
                            items.add(Terminal(((Terminal) it).getTerminal()));
                        } else {
                            throw new RuntimeException("Unhandled case");
                        }
                    }

                    org.kframework.kore.outer.SyntaxProduction prod = SyntaxProduction(sort,
                            immutable(items), inner.apply(p.getAttributes()));

                    res.add(prod);
                }
            }
        }
        return res;
    }

    public void applyUserList(Set<org.kframework.kore.outer.Sentence> res,
            org.kframework.kore.Sort sort, Production p, UserList userList) {
        org.kframework.kore.Sort elementSort = apply(userList.getSort());

        // TODO: we're splitting one syntax declaration into three, where to put
        // attributes
        // of original declaration?

        // Using attributes to mark these three rules
        // (to be used when translating those back to single KIL declaration)
        org.kframework.kore.KList userlistMarker = KList(
                KToken(Sort("userList"), KString(userList.getListType())),
                KToken(Sort("listType"), KString(userList.getSort().getName())));

        org.kframework.kore.Attributes attrs = Attributes(userlistMarker);

        org.kframework.kore.outer.SyntaxProduction prod1, prod2, prod3;

        // lst ::= lst sep lst
        prod1 = SyntaxProduction(sort,
                Seq(NonTerminal(sort), Terminal(userList.getSeparator()), NonTerminal(sort)),
                attrs);

        // lst ::= elem
        prod2 = SyntaxProduction(sort, Seq(NonTerminal(elementSort)), attrs);

        // lst ::= .UserList
        prod3 = SyntaxProduction(sort, Seq(Terminal("." + sort.toString())), attrs);

        res.add(prod1);
        res.add(prod2);
        res.add(prod3);
    }

    public org.kframework.kore.Sort apply(org.kframework.kil.Sort sort) {
        return Sort(sort.getName());
    }
}