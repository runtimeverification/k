// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.backend.kore.ToKAppTransformer;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.*;
import org.kframework.kil.Cast.CastType;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;

import com.davekoelle.AlphanumComparator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ConcretizeSyntax extends CopyOnWriteTransformer {

    private final ToKAppTransformer toKApp;

    public ConcretizeSyntax(Context context) {
        super("Abstract K to Syntax K", context);
        toKApp = new ToKAppTransformer(context);
    }

    @Override
    public ASTNode complete(ASTNode node, ASTNode r) {
        if (r instanceof Term && !(r instanceof Variable)) {
            if (node.getAttributes().size() > 0) {
                Cast c = new Cast((Term)r, CastType.SYNTACTIC, context);
                c.copyAttributesFrom(node);
                return super.complete(node, c);
            }
        }
        return super.complete(node, r);
    }

    @Override
    public ASTNode visit(KApp kapp, Void _)  {
        ASTNode t = internalTransform(kapp);
        try {
            t = new TypeSystemFilter(context).visitNode(t);
        } catch (ParseFailedException e) {
            //type error, so don't disambiguate
        }
        return t;
    }

    public static class RemoveEmptyLists extends CopyOnWriteTransformer {
        public RemoveEmptyLists(Context context) {
            super("Reverse AddEmptyLists", context);
        }

        @Override
        public ASTNode visit(TermCons tcParent, Void _)  {
            for (int i = 0; i < tcParent.getContents().size(); i++) {
                Term child = tcParent.getContents().get(i);
                internalTransform(tcParent, i, child);
            }
            return super.visit(tcParent, _);
        }

        private void internalTransform(TermCons tcParent, int i, Term child) {
            if (child instanceof TermCons) {
                TermCons termCons = (TermCons) child;
                if (termCons.getProduction().isListDecl()) {
                    if (AddEmptyLists.isAddEmptyList(context, tcParent.getProduction().getChildSort(i), termCons.getContents().get(0).getSort()) && termCons.getContents().get(1) instanceof ListTerminator) {

                        tcParent.getContents().set(i, termCons.getContents().get(0));
                    }
                }
            } else if (child instanceof Ambiguity) {
                Ambiguity amb = (Ambiguity) child;
                for (Term choice : amb.getContents()) {
                    internalTransform(tcParent, i, choice);
                }
            }
        }
    }


    public ASTNode internalTransform(KApp kapp)  {
        Term label = kapp.getLabel();
        Term child = kapp.getChild();
        child = child.shallowCopy();
        List<Term> possibleTerms;
        if (label instanceof KInjectedLabel && child.equals(KList.EMPTY)) {
            if (label instanceof FreezerLabel) {
                FreezerLabel l = (FreezerLabel) label;
                return new Freezer((Term) this.visitNode(l.getTerm()));
            }
            Term injected = ((KInjectedLabel)label).getTerm();
//            if (injected instanceof Token) {
                return this.visitNode(injected);
//            }
        } else if (label instanceof KLabelConstant) {
            String klabel = ((KLabelConstant) label).getLabel();
            Set<Production> prods = context.klabels.get(klabel);
            List<Term> contents = new ArrayList<Term>();
            possibleTerms = new ArrayList<Term>();
            if (child instanceof KList) {
                contents = ((KList)child).getContents();
            }
            if (prods.size() > 0) {
                for (int i = 0; i < contents.size(); i++) {
                    contents.set(i, (Term) this.visitNode(contents.get(i)));
                }
                for (Production p : prods) {
                    List<Term> newContents = new ArrayList<Term>(contents);
                    if (p.getAttribute("reject") != null)
                        continue;
                    if (p.getArity() != contents.size())
                        continue;
                    for (int i = 0; i < contents.size(); i++) {
                        if (contents.get(i) instanceof KApp && ((KApp)contents.get(i)).getLabel() instanceof KInjectedLabel) {
                            KInjectedLabel l = (KInjectedLabel)((KApp)contents.get(i)).getLabel();
                            if (context.isSubsortedEq(p.getChildSort(i), l.getTerm().getSort())) {
                                newContents.set(i, l.getTerm());
                            }
                        } else {
                        }
                    }
                    possibleTerms.add(new TermCons(p.getSort(), newContents, p));
                }
                if (possibleTerms.size() == 0) {
                    return super.visit(kapp, null);
                }
                if (possibleTerms.size() == 1) {
                    return possibleTerms.get(0);
                } else {
                    return new Ambiguity(Sort.K, possibleTerms);
                }
            } else if (child.equals(KList.EMPTY)) {
                //could be a list terminator, which don't have conses
                Set<Production> listProds = context.listKLabels.get(klabel);
                possibleTerms = new ArrayList<Term>();
                if (listProds != null) {
                    for (Production prod : listProds) {
                        if (prod.getSort().isUserListSort()) {
                            continue;
                        }
                        possibleTerms.add(new ListTerminator(prod.getSort(), null));
                    }
                    if (possibleTerms.size() == 0) {
                        return super.visit(kapp, null);
                    }
                    if (possibleTerms.size() == 1) {
                        return possibleTerms.get(0);
                    } else {

                        return new Ambiguity(Sort.K, possibleTerms);
                    }
                }
            }
        } else if (label instanceof Token) {
            Token token = (Token) label;
            return new Constant(token.tokenSort(), token.value(), null);
        }
        return super.visit(kapp, null);
    }

    @Override
    public ASTNode visit(Cell cell, Void _)  {
        // TODO(AndreiS): fix the printing of the cells which are representing maps
        if (cell.getLabel().matches(".*-fragment")) {
            return this.visitNode(cell.getContents());
        }
        return super.visit(cell, _);
    }

    @Override
    public ASTNode visit(Bag bag, Void _)  {
        List<Term> contents = new ArrayList<Term>();
        for (Term child : bag.getContents()) {
            Term accept = (Term) this.visitNode(child);
            if (accept instanceof ListTerminator) {
                ListTerminator empty = (ListTerminator) accept;
                if (!empty.getSort().equals(Sort.BAG)) {
                    contents.add(accept);
                }
            } else {
                contents.add(accept);
            }
        }
        if (contents.size() == 0) {
            return new ListTerminator(Sort.BAG, null);
        }
        if (contents.size() == 1) {
            return contents.get(0);
        }
        Map<Term, String> unparsedTerms = new HashMap<>();
        for (Term t : contents) {
            UnparserFilter filter = new UnparserFilter(context);
            filter.visitNode(t);
            unparsedTerms.put(t, filter.getResult());
        }
        Collections.sort(contents, new UnparserBagItemComparator(unparsedTerms));
        return new Bag(contents);
    }

    private class UnparserBagItemComparator implements Comparator<Term> {

        private Map<Term, String> unparsedResults;

        private AlphanumComparator comparator = new AlphanumComparator();

        public UnparserBagItemComparator(java.util.Map<Term, String> unparsedResults) {
            this.unparsedResults = unparsedResults;
        }


        @Override
        public int compare(Term o1, Term o2) {
            // case 1: one of o1 and o2 is a cell
            if ((o1 instanceof Cell) && !(o2 instanceof Cell)
                    || !(o1 instanceof Cell) && (o2 instanceof Cell)) {
                return o1 instanceof Cell ? -1 : 1;
            }

            // case 2: o1 and o2 are cells with different labels
            if (o1 instanceof Cell && o2 instanceof Cell
                    && (!((Cell) o1).getLabel().equals(((Cell) o2).getLabel()))) {
                Cell c1 = (Cell) o1;
                Cell c2 = (Cell) o2;
                ConfigurationStructureMap sons = context.getConfigurationStructureMap().get(c1.getLabel()).parent.sons;
                assert sons == context.getConfigurationStructureMap().get(c2.getLabel()).parent.sons;
                return sons.positionOf(c1.getLabel()) < sons.positionOf(c2.getLabel()) ? -1 : 1;
            }

            // case 3: neither o1 nor o2 is a cell
            // case 4: o1 and o2 are cells with the same label
            String s1 = unparsedResults.get(o1);
            String s2 = unparsedResults.get(o2);
            return comparator.compare(s1, s2);
        }

    };


    @Override
    public ASTNode visit(MapBuiltin map, Void _) {
        Term kapp = (Term) toKApp.visitNode(super.visit(map, _));
        return this.visitNode(kapp);
    }

    @Override
    public ASTNode visit(ListBuiltin list, Void _) {
        Term kapp = (Term) toKApp.visitNode(super.visit(list, _));
        return this.visitNode(kapp);
    }

    @Override
    public ASTNode visit(SetBuiltin set, Void _) {
        Term kapp = (Term) toKApp.visitNode(super.visit(set, _));
        return this.visitNode(kapp);
    }
}
