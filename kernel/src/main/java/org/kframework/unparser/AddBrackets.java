// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Tag;
import org.kframework.definition.TerminalLike;
import org.kframework.kil.Attribute;
import org.kframework.kore.Sort;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.collection.Set;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import static org.kframework.Collections.*;

/**
 * Implements the naive algorithm to add brackets in order to disambiguate an unparsed AST. This algorithm executes
 * in linear time in the size of the term, but does not correctly solve grammars in which multiple productions share
 * the same terminals in such a way as to cause ambiguities that cannot be resolved using priorities and associativities.
 * As such, we use this algorithm in krun in output --pretty, but it is insufficient for --output sound.
 */
public class AddBrackets {

    private final Module m;
    public AddBrackets(Module m) {
        this.m = m;
    }

    public ProductionReference addBrackets(ProductionReference t) {
        return addBrackets(t, null, null);
    }

    public ProductionReference addBrackets(ProductionReference t, ProductionReference previousLeftCapture, ProductionReference previousRightCapture) {
        if (t instanceof Constant) {
            return t;
        }
        TermCons outer = (TermCons)t;
        List<Term> newItems = new ArrayList<>();
        for (Term t2 : outer.items()) {
            ProductionReference inner = (ProductionReference) t2;
            EnumSet<Fixity> fixity = getFixity(outer);
            int position = getPosition(inner, outer);
            ProductionReference leftCapture = getLeftCapture(previousLeftCapture, outer, inner);
            ProductionReference rightCapture = getRightCapture(previousRightCapture, outer, inner);
            ProductionReference newInner = addBrackets(inner, outer, leftCapture, rightCapture);
            newInner = addBrackets(newInner, leftCapture, rightCapture);
            newItems.add(newInner);
        }
        return TermCons.apply(ConsPStack.from(newItems), outer.production());
    }

    public ProductionReference addBrackets(ProductionReference inner, TermCons outer, ProductionReference leftCapture, ProductionReference rightCapture) {
        if (requiresBracketWithSimpleAlgorithm(outer, leftCapture, rightCapture, inner)) {
            int position = getPosition(inner, outer);
            Sort outerSort = ((NonTerminal)outer.production().items().apply(position)).sort();
            Sort innerSort = inner.production().sort();
            for (Tuple2<Sort, Set<Production>> sort : iterable(m.bracketProductionsFor())) {
                boolean isCorrectOuterSort = m.subsorts().lessThanEq(sort._1(), outerSort);
                if (isCorrectOuterSort) {
                    for (Production p : mutable(sort._2())) {
                        boolean isCorrectInnerSort = stream(p.items())
                                .filter(i -> i instanceof NonTerminal)
                                .map(i -> (NonTerminal) i)
                                .map(NonTerminal::sort)
                                .filter(s -> m.subsorts().lessThanEq(innerSort, s))
                                .findAny().isPresent();
                        if (isCorrectInnerSort) {
                            return TermCons.apply(ConsPStack.singleton(inner), p);
                        }
                    }
                }
            }
            throw KEMException.criticalError("Bracket required for unparsing, but no brackets in module exist matching inner sort " + innerSort + " and outer sort " + outerSort, inner);
        }
        return inner;
    }

    boolean requiresBracketWithSimpleAlgorithm(ProductionReference outer, ProductionReference leftCapture, ProductionReference rightCapture, ProductionReference inner) {
        boolean priority = isPriorityWrong(outer, inner, getPosition(inner, outer));
        boolean inversePriority;
        EnumSet<Fixity> fixity = getFixity(inner, outer);
        EnumSet<Fixity> innerFixity = getFixity(inner);
        if (inner.production().klabel().equals(outer.production().klabel()) &&
            inner.production().klabel().isDefined() &&
            m.attributesFor().apply(inner.production().klabel().get()).contains(Attribute.ASSOCIATIVE_KEY))
            return false;
        if (inner instanceof Constant)
            return false;
        if (fixity.size() == 0)
            return false;
        if (priority)
            return true;
        if (inner.production().isSyntacticSubsort())
            return false;

        if (innerFixity.contains(Fixity.BARE_RIGHT) && rightCapture != null) {
            inversePriority = isPriorityWrong(inner, rightCapture, inner.production().items().size() - 1);
            EnumSet<Fixity> rightCaptureFixity = getFixity(rightCapture);
            if (!inversePriority && rightCaptureFixity.contains(Fixity.BARE_LEFT)) {
                return true;
            }
        }
        if (innerFixity.contains(Fixity.BARE_LEFT) && leftCapture != null) {
            inversePriority = isPriorityWrong(inner, leftCapture, 0);
            EnumSet<Fixity> leftCaptureFixity = getFixity(leftCapture);
            if (!inversePriority && leftCaptureFixity.contains(Fixity.BARE_RIGHT)) {
                return true;
            }
        }
        return false;
    }

    private boolean isRightAssoc(ProductionReference outer, ProductionReference inner) {
        Tag parentLabel = new Tag(outer.production().klabel().get().name());
        Tag localLabel = new Tag(inner.production().klabel().get().name());
        if (m.rightAssoc().contains(new Tuple2<>(parentLabel, localLabel))) {
            return true;
        }
        return false;
    }

    private boolean isLeftAssoc(ProductionReference outer, ProductionReference inner) {
        Tag parentLabel = new Tag(outer.production().klabel().get().name());
        Tag localLabel = new Tag(inner.production().klabel().get().name());
        if (m.leftAssoc().contains(new Tuple2<>(parentLabel, localLabel))) {
            return true;
        }
        return false;
    }

    private boolean isPriorityWrong(ProductionReference outer, ProductionReference inner, int position) {
        Tag parentLabel = new Tag(outer.production().klabel().get().name());
        Tag localLabel = new Tag(inner.production().klabel().get().name());
        if (m.priorities().lessThan(parentLabel, localLabel)) {
            return true;
        }
        if (m.leftAssoc().contains(new Tuple2<>(parentLabel, localLabel)) && position == outer.production().items().size() - 1) {
            return true;
        }
        if (m.rightAssoc().contains(new Tuple2<>(parentLabel, localLabel)) && position == 0) {
            return true;
        }
        return false;
    }

    private boolean isPriorityWrong(ProductionReference outer, ProductionReference inner) {
        Tag parentLabel = new Tag(outer.production().klabel().get().name());
        Tag localLabel = new Tag(inner.production().klabel().get().name());
        if (m.priorities().lessThan(parentLabel, localLabel)) {
            return true;
        }
        if (m.leftAssoc().contains(new Tuple2<>(parentLabel, localLabel))) {
            return true;
        }
        if (m.rightAssoc().contains(new Tuple2<>(parentLabel, localLabel))) {
            return true;
        }
        return false;
    }

    private enum Fixity {
        BARE_LEFT,
        BARE_RIGHT
    }

    ProductionReference getLeftCapture(ProductionReference previousLeftCapture, ProductionReference outer, ProductionReference inner) {
        EnumSet<Fixity> fixity = getFixity(outer);
        int position = getPosition(inner, outer);
        if (position == 0 && fixity.contains(Fixity.BARE_LEFT)) {
            return previousLeftCapture;
        } else {
            return outer;
        }
    }

    ProductionReference getRightCapture(ProductionReference previousRightCapture, ProductionReference outer, ProductionReference inner) {
        EnumSet<Fixity> fixity = getFixity(outer);
        int position = getPosition(inner, outer);
        if (position == outer.production().items().size() - 1 && fixity.contains(Fixity.BARE_RIGHT)) {
            return previousRightCapture;
        } else {
            return outer;
        }
    }

    private EnumSet<Fixity> getFixity(ProductionReference t) {
        Production p = t.production();
        EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
        if (t instanceof Constant) {
            return set;
        }
        if (p.items().apply(0) instanceof NonTerminal)
            set.add(Fixity.BARE_LEFT);
        if (p.items().apply(p.items().size() - 1) instanceof NonTerminal)
            set.add(Fixity.BARE_RIGHT);
        return set;
    }

    private EnumSet<Fixity> getFixity(ProductionReference inner, ProductionReference outer) {
        assert outer instanceof TermCons;
        TermCons tc = (TermCons)outer;
        int i;
        for (i = 0; i < tc.items().size(); i++) {
            if (tc.get(i) == inner)
                break;
        }
        Production p = tc.production();
        EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
        int position = getPosition(inner, outer);
        if (!hasTerminalAtIdx(p, position+1)) {
            set.add(Fixity.BARE_RIGHT);
        }
        if (!hasTerminalAtIdx(p, position-1)) {
            set.add(Fixity.BARE_LEFT);
        }
        return set;
    }

    boolean hasTerminalAtIdx(Production p, int position) {
        if (position < 0 || position >= p.items().size()) {
            return false;
        }
        return p.items().apply(position) instanceof TerminalLike;
    }

    private int getPosition(ProductionReference inner, ProductionReference outer) {
        EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
        assert outer instanceof TermCons;
        TermCons tc = (TermCons)outer;
        Production p = tc.production();
        for (int i = 0, j = 0; i < p.items().size(); i++) {
            if (p.items().apply(i) instanceof NonTerminal) {
                if (tc.get(j) == inner) {
                    return i;
                }
                j++;
            }
        }
        throw new AssertionError();
    }
}
