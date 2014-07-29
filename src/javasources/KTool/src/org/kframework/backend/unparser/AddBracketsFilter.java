// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Stack;

public class AddBracketsFilter extends CopyOnWriteTransformer {

    public AddBracketsFilter(Context context) {
        super("Add brackets", context);
    }

    @Override
    public ASTNode visit(TermCons ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(Collection ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(Cell ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(CollectionItem ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(KApp ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(Hole ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(Freezer ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    @Override
    public ASTNode visit(KInjectedLabel ast, Void _)  {
        prepare(ast);
        ASTNode result = super.visit(ast, _);
        boolean needsParens = postpare();
        if (needsParens)
            return new Bracket((Term)result, context);
        return result;
    }

    private enum Associativity {
        LEFT,
        RIGHT,
        NONASSOC,
        ASSOC,
        NONE;
    }

    private enum Fixity {
        BARE_LEFT,
        BARE_RIGHT
    }

    private boolean isUnary(Term t) {
        if (t instanceof TermCons) {
            TermCons tc = (TermCons) t;
            Production p = tc.getProduction();
            if (p.isListDecl()) {
                UserList userList = (UserList) p.getItems().get(0);
                if (tc.getContents().get(1) instanceof ListTerminator && tc.getContents().get(1).getSort().equals(p.getSort()) && context.isSubsortedEq(userList.getSort(), tc.getContents().get(0).getSort())) {
                    return true;
                }
            }
            return tc.getProduction().getArity() == 1;
        } else if (t instanceof CollectionItem) {
            return true;
        } else if (t instanceof Cell || t instanceof Freezer || t instanceof KInjectedLabel) {
            return true;
        }
        return false;
    }

    private Associativity getAssociativity(Term t) {
        if (t instanceof TermCons) {
            TermCons tc = (TermCons)t;
            Production p = tc.getProduction();
            if (p.isListDecl()) {
                UserList userList = (UserList) p.getItems().get(0);
                if (tc.getContents().get(1) instanceof ListTerminator && tc.getContents().get(1).getSort().equals(p.getSort()) && context.isSubsortedEq(userList.getSort(), tc.getContents().get(0).getSort())) {
                    return Associativity.NONE;
                } else {
                    return Associativity.RIGHT;
                }
            }
            if (p.getAttributes().containsKey("left"))
                return Associativity.LEFT;
            if (p.getAttributes().containsKey("right"))
                return Associativity.RIGHT;
            if (p.getAttributes().containsKey("non-assoc"))
                return Associativity.NONASSOC;
        /*    if (p.getArity() == 2) {
                boolean leftAssociate = context.isSubsortedEq(p.getChildSort(0), p.getSort());
                boolean rightAssociate = context.isSubsortedEq(p.getChildSort(1), p.getSort());
                if (!leftAssociate && !rightAssociate) {
                    return Associativity.NONASSOC;
                } else if (!leftAssociate) {
                    return Associativity.RIGHT;
                } else if (!rightAssociate) {
                    return Associativity.LEFT;
                }
            }*/

        } else if (t instanceof Collection) {
            return Associativity.ASSOC;
        }
        return Associativity.NONE;
    }

    private boolean getAssociativity(Term inner, Term outer) {
        if (!(inner instanceof TermCons && outer instanceof TermCons)) {
            return false;
        }
        TermCons tcInner = (TermCons) inner;
        TermCons tcOuter = (TermCons) outer;
        if (tcInner.getCons().equals(tcOuter.getCons())) {
            return true;
        }
        if (context.associativity.get(tcInner.getCons()) == null) {
            return false;
        }
        return context.associativity.get(tcInner.getCons()).contains(tcOuter.getProduction());
    }

    private boolean isAtom(Term inner) {
        if (inner instanceof KLabelConstant) return true;
        if (inner instanceof KApp && ((KApp)inner).getLabel() instanceof Token) return true;
        if (inner instanceof ListTerminator) return true;
        if (inner instanceof FreezerHole) return true;
        if (inner instanceof Hole) return true;
        if (inner instanceof Variable) return true;
        if (inner instanceof TermCons) {
            TermCons tc = (TermCons) inner;
            if (tc.getProduction().getArity() == 0) return true;
        }
        return false;
    }

    /** compute fixity of single production */
    private EnumSet<Fixity> getFixity(Term t) {
        if (isAtom(t)) return EnumSet.noneOf(Fixity.class);
        if (t instanceof TermCons) {
            TermCons tc = (TermCons) t;
            Production p = tc.getProduction();
            EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
            if (!(p.getItems().get(0) instanceof Terminal))
                set.add(Fixity.BARE_LEFT);
            if (!(p.getItems().get(p.getItems().size() - 1) instanceof Terminal))
                set.add(Fixity.BARE_RIGHT);
            return set;
        } else if (t instanceof Collection || t instanceof Freezer) {
            return EnumSet.allOf(Fixity.class);
        } else if (t instanceof CollectionItem || t instanceof Cell) {
            return EnumSet.noneOf(Fixity.class);
        } else if (t instanceof KApp) {
            return EnumSet.of(Fixity.BARE_LEFT);
        } else if (t instanceof KInjectedLabel) {
            return EnumSet.of(Fixity.BARE_RIGHT);
        }
        throw new UnsupportedOperationException("term fixity");
    }

    private EnumSet<Fixity> getPosition(Term inner, Term outer) {
        List<Term> childTerms;
        EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
        if (outer instanceof TermCons) {
            TermCons tc = (TermCons)outer;
            childTerms = tc.getContents();
            Production p = tc.getProduction();
            if (p.isListDecl()) {
                UserList userList = (UserList) p.getItems().get(0);
                if (tc.getContents().get(1) instanceof ListTerminator && tc.getContents().get(1).getSort().equals(p.getSort()) && context.isSubsortedEq(userList.getSort(), tc.getContents().get(0).getSort())) {
                    return EnumSet.allOf(Fixity.class);
                }
            }
        } else if (outer instanceof Collection) {
            Collection c = (Collection)outer;
            childTerms = c.getContents();
        } else if (outer instanceof CollectionItem || outer instanceof Cell || outer instanceof KInjectedLabel || outer instanceof Freezer) {
            return EnumSet.allOf(Fixity.class);
        } else if (outer instanceof KApp) {
            KApp kapp = (KApp) outer;
            childTerms = new ArrayList<Term>();
            childTerms.add(kapp.getLabel());
            childTerms.add(kapp.getChild());
        } else {
            throw new UnsupportedOperationException("position fixity");
        }
        if (childTerms.get(0) == inner)
            set.add(Fixity.BARE_LEFT);
        if (childTerms.get(childTerms.size() - 1) == inner)
            set.add(Fixity.BARE_RIGHT);
        return set;
    }

    private static class ContainsVisitor extends BasicVisitor {
        private boolean found = false;
        private Term inner;
        public ContainsVisitor(Term inner, Context context) {
            super("Term contains target term", context);
            this.inner = inner;
        }
        @Override
        public Void visit(Term t, Void _) {
            if (t == inner) found = true;
            return super.visit(t, _);
        }
        public boolean getFound() {
            return found;
        }
    }

    private static boolean contains(Term outer, Term inner, org.kframework.kil.loader.Context context) {
        ContainsVisitor visit = new ContainsVisitor(inner, context);
        visit.visitNode(outer);
        return visit.getFound();
    }

    /** compute fixity of nonterminal within production */
    private EnumSet<Fixity> getFixity(Term inner, Term outer) {
        if (outer instanceof TermCons) {
            TermCons tc = (TermCons)outer;
            int i;
            for (i = 0; i < tc.getContents().size(); i++) {
                if (contains(tc.getContents().get(i), inner, context))
                    break;
            }
            Production p = tc.getProduction();
            EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
            if (!p.hasTerminalToRight(i)) {
                set.add(Fixity.BARE_RIGHT);
            }
            if (!p.hasTerminalToLeft(i)) {
                set.add(Fixity.BARE_LEFT);
            }
            if (p.isListDecl()) {
                UserList userList = (UserList) p.getItems().get(0);
                if (tc.getContents().get(1) instanceof ListTerminator && tc.getContents().get(1).getSort().equals(p.getSort()) && context.isSubsortedEq(userList.getSort(), tc.getContents().get(0).getSort())) {
                    return EnumSet.allOf(Fixity.class);
                }
            }
            return set;
        } else if (outer instanceof Bag) {
            return EnumSet.allOf(Fixity.class);
        } else if (outer instanceof Collection) {
            //KList or KSequence
            Collection c = (Collection) outer;
            int i;
            for (i = 0; i < c.getContents().size(); i++) {
                if (contains(c.getContents().get(i), inner, context))
                    break;
            }
            EnumSet<Fixity> set = EnumSet.allOf(Fixity.class);
            if (i != 0)
                set.remove(Fixity.BARE_LEFT);
            if (i != c.getContents().size())
                set.remove(Fixity.BARE_RIGHT);
            return set;
        } else if (outer instanceof CollectionItem) {
            return EnumSet.noneOf(Fixity.class);
        } else if (outer instanceof Cell) {
            return EnumSet.noneOf(Fixity.class);
        } else if (outer instanceof KApp) {
            KApp kapp = (KApp) outer;
            if (contains(kapp.getLabel(), inner, context))
                return EnumSet.of(Fixity.BARE_LEFT);
            return EnumSet.noneOf(Fixity.class);
        } else if (outer instanceof Freezer) {
            return EnumSet.allOf(Fixity.class);
        } else if (outer instanceof KInjectedLabel) {
            return EnumSet.of(Fixity.BARE_RIGHT);
        }
        throw new UnsupportedOperationException("subterm fixity");
    }

    private boolean isPriorityWrong(Term outer, Term inner) {
        if (outer instanceof TermCons) {
            TermCons tcOuter = (TermCons) outer;
            for (int i = 0; i < tcOuter.getContents().size(); i++) {
                if (context.isSubsortedEq(tcOuter.getProduction().getChildSort(i), inner.getSort())) {
                    return inner instanceof TermCons && context.isPriorityWrong(tcOuter.getProduction().getKLabel(), ((TermCons)inner).getProduction().getKLabel());
                }
            }
            return !inner.getSort().equals("K");
        } else if (inner instanceof Rewrite && !(outer instanceof Cell)) {
            return true;
        } else if (inner instanceof KSequence && outer instanceof TermCons) {
            return true;
        } else if (outer instanceof KInjectedLabel) {
            KInjectedLabel lbl = (KInjectedLabel)outer;
            String sort = lbl.getTerm().getSort();
            if (MetaK.isKSort(sort)) {
                sort = KInjectedLabel.getInjectedSort(sort);
                if (!context.isSubsortedEq(sort, inner.getSort())) {
                    return true;
                }
            }
        }
        return false;
    }

    private Stack<Term> stack = new Stack<Term>();
    private Stack<Term> leftCapture = new Stack<Term>(), rightCapture = new Stack<Term>();
    private Stack<Boolean> parens = new Stack<Boolean>();

    private void prepare(Term ast)  {
        if (!stack.empty()) {
            Term lc = null, rc = null;
            Term outer = stack.peek();
            EnumSet<Fixity> fixity = getFixity(outer);
            if (!leftCapture.empty()) lc = leftCapture.peek();
            if (!rightCapture.empty()) rc = rightCapture.peek();
            boolean needsParens = parens.peek();
            EnumSet<Fixity> position = getPosition(ast, outer);
            if (isUnary(outer) && fixity.contains(Fixity.BARE_LEFT) && fixity.contains(Fixity.BARE_RIGHT)) {
                if (needsParens) {
                    lc = null;
                    rc = null;
                }
            } else if (position.contains(Fixity.BARE_LEFT) && fixity.contains(Fixity.BARE_LEFT)) {
                rc = outer;
                if (needsParens)
                    lc = null;
            } else if (position.contains(Fixity.BARE_RIGHT) && fixity.contains(Fixity.BARE_RIGHT)) {
                lc = outer;
                if (needsParens)
                    rc = null;
            } else {
                lc = null;
                rc = null;
            }
            leftCapture.push(lc);
            rightCapture.push(rc);
            parens.push(needsParentheses(ast, outer, lc, rc));
        } else {
            leftCapture.push(null);
            rightCapture.push(null);
    //        parens.push(needsParentheses(ast, null, null, null));
            parens.push(false);
        }
        stack.push(ast);
    }

    private boolean postpare() {
        @SuppressWarnings("unused")
        Term inner = stack.pop();
        leftCapture.pop();
        rightCapture.pop();
        boolean needsParens = parens.pop();
        return needsParens;
    }

    private boolean needsParentheses(Term inner, Term outer, Term leftCapture, Term rightCapture)  {
        try {
            boolean priority = isPriorityWrong(outer, inner);
            boolean inversePriority = isPriorityWrong(inner, outer);
            Associativity assoc = getAssociativity(outer);
//            Associativity innerAssoc = getAssociativity(inner);
            EnumSet<Fixity> fixity = getFixity(inner, outer);
            EnumSet<Fixity> innerFixity = getFixity(inner);
//            EnumSet<Fixity> position = getPosition(inner, outer);
            if (isAtom(inner))
                return false;
            if (fixity.size() == 0)
                return false;
            if (priority)
                return true;
            if (isUnary(inner) && innerFixity.contains(Fixity.BARE_LEFT) && innerFixity.contains(Fixity.BARE_RIGHT))
                return false;
/*            if (rightCapture != null) {
                UnparserFilter unparser = new UnparserFilter(false, false, false);
                Term rightCapturePattern = (Term)rightCapture.accept(new MakePattern(inner));
                rightCapturePattern.accept(unparser);
                String unparsed = unparser.getResult();
                ASTNode config = DefinitionLoader.parsePatternAmbiguous(unparsed);
                Rule rl = (Rule) config;
                config = rl.getBody();
                config = config.accept(new AddEmptyLists());
                if (!rightCapturePattern.equals(config)){
                    return true;
                }
            }
            if (leftCapture != null) {
                UnparserFilter unparser = new UnparserFilter(false, false, false);
                Term leftCapturePattern = (Term)leftCapture.accept(new MakePattern(inner));
                leftCapturePattern.accept(unparser);
                String unparsed = unparser.getResult();
                ASTNode config = DefinitionLoader.parsePatternAmbiguous(unparsed);
                Rule rl = (Rule) config;
                config = rl.getBody();
                config = config.accept(new AddEmptyLists());
                if (!leftCapturePattern.equals(config)) {
                    return true;
                }
            }

*/

            if (innerFixity.contains(Fixity.BARE_RIGHT) && rightCapture != null) {
                priority = isPriorityWrong(rightCapture, inner);
                inversePriority = isPriorityWrong(inner, rightCapture);
                if (assoc == Associativity.NONASSOC && !inversePriority) {// && !implicitInversePriority) {
                    return true;
                } else if (assoc == Associativity.NONE && !inversePriority) { //(fixity.contains(Fixity.BARE_LEFT))) {
                    return true;
                } else if (assoc == Associativity.RIGHT && !inversePriority) {
                    return true;
                } else if (assoc == Associativity.LEFT && !inversePriority && !getAssociativity(inner, rightCapture)) {
                    return true;
                }
            }
            if (innerFixity.contains(Fixity.BARE_LEFT) && leftCapture != null) {
                priority = isPriorityWrong(leftCapture, inner);
                inversePriority = isPriorityWrong(inner, leftCapture);
                if (assoc == Associativity.NONASSOC && !inversePriority) {// && !implicitInversePriority) {
                    return true;
                } else if (assoc == Associativity.NONE && !inversePriority) {//(fixity.contains(Fixity.BARE_RIGHT))) {
                    return true;
                } else if (assoc == Associativity.LEFT && !inversePriority) {
                    return true;
                } else if (assoc == Associativity.RIGHT && !inversePriority && !getAssociativity(inner, leftCapture)) {
                    return true;
                }
            }
            return false;
        } catch (UnsupportedOperationException e) {
            return true;
        }
    }
}
