// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

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
import org.kframework.kore.Attributes;
import org.kframework.kore.outer.*;

import scala.Enumeration.Value;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.Collections.*;

public class KILtoKORE extends KILTransformation<Object> {

    private org.kframework.kil.loader.Context context;
    private KILtoInnerKORE inner;

    public KILtoKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
        inner = new KILtoInnerKORE(context);
    }

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
        return Module(i.getName(), immutable(items), inner.convertAttributes(i));
    }

    @SuppressWarnings("unchecked")
    public Set<org.kframework.kore.outer.Sentence> apply(ModuleItem i) {
        if (i instanceof Syntax || i instanceof PriorityExtended) {
            return (Set<org.kframework.kore.outer.Sentence>) apply((ASTNode) i);
        } else {
            return Sets.newHashSet((org.kframework.kore.outer.Sentence) apply((ASTNode) i));
        }
    }

    public org.kframework.kore.outer.Bubble apply(StringSentence sentence) {
        return Bubble(sentence.getType(), sentence.getContent(), inner.convertAttributes(sentence));
    }

    public Context apply(org.kframework.kil.Context c) {
        return Context(inner.apply(c.getBody()), inner.applyOrTrue(c.getRequires()));
    }

    public ModuleComment apply(LiterateModuleComment m) {
        return new org.kframework.kore.outer.ModuleComment(m.getValue(),
                inner.convertAttributes(m));
    }

    public org.kframework.kore.outer.Configuration apply(Configuration kilConfiguration) {
        Cell body = (Cell) kilConfiguration.getBody();
        return Configuration(inner.apply(body), inner.applyOrTrue(kilConfiguration.getEnsures()),
                inner.convertAttributes(kilConfiguration));
    }

    public Rule apply(org.kframework.kil.Rule r) {
        return Rule(inner.apply(r.getBody()), inner.applyOrTrue(r.getRequires()),
                inner.applyOrTrue(r.getEnsures()), inner.convertAttributes(r));
    }

    public org.kframework.kore.outer.SyntaxAssociativity apply(PriorityExtendedAssoc ii) {
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

    public Set<org.kframework.kore.outer.Sentence> apply(PriorityExtended pe) {
        Seq<scala.collection.immutable.Set<Tag>> seqOfSetOfTags = immutable(pe.getPriorityBlocks()
                .stream().map(block -> toTags(block.getProductions()))
                .collect(Collectors.toList()));

        return Sets.newHashSet(SyntaxPriority(seqOfSetOfTags));
    }

    public scala.collection.immutable.Set<Tag> toTags(List<KLabelConstant> labels) {
        return immutable(labels.stream().map(l -> Tag(l.getLabel())).collect(Collectors.toSet()));
    }

    public org.kframework.kore.outer.Sentence apply(Import s) {
        return new org.kframework.kore.outer.Import(s.getName(), inner.convertAttributes(s));
    }

    public Set<org.kframework.kore.outer.Sentence> apply(Syntax s) {
        Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();

        org.kframework.kore.Sort sort = apply(s.getDeclaredSort().getSort());

        // just a sort declaration
        if (s.getPriorityBlocks().size() == 0) {
            res.add(SyntaxSort(sort, inner.convertAttributes(s)));
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

                    org.kframework.kore.Attributes attrs = inner.convertAttributes(p);

                    org.kframework.kore.outer.SyntaxProduction prod = SyntaxProduction(
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

    public void applyUserList(Set<org.kframework.kore.outer.Sentence> res,
            org.kframework.kore.Sort sort, Production p, UserList userList) {
        boolean nonEmpty = userList.getListType().equals(UserList.ONE_OR_MORE);

        org.kframework.kore.Sort elementSort = apply(userList.getSort());

        // TODO: we're splitting one syntax declaration into three, where to put
        // attributes
        // of original declaration?

        // Using attributes to mark these three rules
        // (to be used when translating those back to single KIL declaration)

        org.kframework.kore.Attributes attrs = Attributes().add("userList", p.getSort().getName());

        org.kframework.kore.outer.SyntaxProduction prod1, prod2, prod3;

        String kilProductionId = "" + System.identityHashCode(p);

        // lst ::= lst sep lst
        Attributes attrsWithKilProductionId = attrs.add(KILtoInnerKORE.PRODUCTION_ID,
                kilProductionId);
        prod1 = SyntaxProduction(sort,
                Seq(NonTerminal(sort), Terminal(userList.getSeparator()), NonTerminal(sort)),
                attrsWithKilProductionId);

        // lst ::= elem
        prod2 = SyntaxProduction(sort, Seq(NonTerminal(elementSort)), attrsWithKilProductionId);

        // lst ::= .UserList
        prod3 = SyntaxProduction(sort, Seq(Terminal("." + sort.toString())),
                attrsWithKilProductionId);

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
