// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.Collections;
import org.kframework.POSet;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Tag;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;
import scala.collection.Set;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.HashSet;

import static org.kframework.Collections.*;

/**
 * Apply the priority and associativity filters.
 */
public class PriorityVisitor extends SetsTransformerWithErrors<KEMException> {

    private final POSet<Tag> priorities;
    private final Set<Tuple2<Tag, Tag>> leftAssoc;
    private final Set<Tuple2<Tag, Tag>> rightAssoc;
    public PriorityVisitor(POSet<Tag> priorities, Set<Tuple2<Tag, Tag>> leftAssoc, Set<Tuple2<Tag, Tag>> rightAssoc) {
        super();
        this.priorities = priorities;
        this.leftAssoc = leftAssoc;
        this.rightAssoc = rightAssoc;
    }

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(Ambiguity amb) {
        // if the ambiguity has rewrites at the top, prefer them, and eliminate the rest
        scala.collection.Set<Term> rewrites = amb.items().stream().filter(o ->
                o instanceof TermCons &&
                        ((TermCons) o).production().klabel().isDefined() &&
                        ((TermCons) o).production().klabel().get().name().equals("#KRewrite")).collect(Collections.toSet());
        if (rewrites.size() == 1)
            return apply(rewrites.head());
        if (rewrites.size() != 0 && rewrites.size() != amb.items().size())
            amb = Ambiguity.apply(mutable(rewrites));

        // if the ambiguity has KSeq at the top, prefer them, and eliminate the rest
        rewrites = amb.items().stream().filter(o ->
                o instanceof TermCons &&
                        ((TermCons) o).production().klabel().isDefined() &&
                        ((TermCons) o).production().klabel().get().name().equals("#KSequence")).collect(Collections.toSet());
        if (rewrites.size() == 1)
            return apply(rewrites.head());
        if (rewrites.size() != 0 && rewrites.size() != amb.items().size())
            amb = Ambiguity.apply(mutable(rewrites));

        // if the ambiguity has let at the top, prefer them, and eliminate the rest
        rewrites = amb.items().stream().filter(o ->
                o instanceof TermCons &&
                        ((TermCons) o).production().klabel().isDefined() &&
                        ((TermCons) o).production().klabel().get().name().equals("#let")).collect(Collections.toSet());
        if (rewrites.size() == 1)
            return apply(rewrites.head());
        if (rewrites.size() != 0 && rewrites.size() != amb.items().size())
            amb = Ambiguity.apply(mutable(rewrites));

        return super.apply(amb);
    }

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort()) {
            // match only on the outermost elements
            if (tc.production().att().contains("applyPriority")) {
              String[] pieces = StringUtil.splitOneDimensionalAtt(tc.production().att().get("applyPriority"));
              java.util.Set<Integer> applyAt = new HashSet<>();
              for (String piece : pieces) {
                  try {
                      int i = Integer.parseInt(piece.trim());
                      applyAt.add(i);
                  } catch (NumberFormatException e) {
                      throw KEMException.innerParserError("Invalid applyPriority attribute value: " + piece, e, tc.production().source().orElse(null), tc.production().location().orElse(null));
                  }
              }
              for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                  if (tc.production().items().apply(i) instanceof NonTerminal) {
                      j++;
                      if (applyAt.contains(j)) {
                          PriorityVisitor2.Side side;
                          if (i == 0) {
                            side = PriorityVisitor2.Side.LEFT;
                          } else if (i == tc.production().items().size() - 1) {
                            side = PriorityVisitor2.Side.RIGHT;
                          } else {
                            side = PriorityVisitor2.Side.MIDDLE;
                          }
                          Either<java.util.Set<KEMException>, Term> rez =
                                  new PriorityVisitor2(tc, side, priorities, leftAssoc, rightAssoc).apply(tc.get(j-1));
                          if (rez.isLeft())
                              return rez;
                          tc = tc.with(j-1, rez.right().get());
                      }
                  }
              }
            } else {
                if (tc.production().items().apply(0) instanceof NonTerminal) {
                    Either<java.util.Set<KEMException>, Term> rez =
                            new PriorityVisitor2(tc, PriorityVisitor2.Side.LEFT, priorities, leftAssoc, rightAssoc).apply(tc.get(0));
                    if (rez.isLeft())
                        return rez;
                    tc = tc.with(0, rez.right().get());
                }
                if (tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal) {
                    int last = tc.items().size() - 1;
                    Either<java.util.Set<KEMException>, Term> rez =
                            new PriorityVisitor2(tc, PriorityVisitor2.Side.RIGHT, priorities, leftAssoc, rightAssoc).apply(tc.get(last));
                    if (rez.isLeft())
                        return rez;
                    tc = tc.with(last, rez.right().get());
                }
            }
        }
        return super.apply(tc);
    }

    private static class PriorityVisitor2 extends SetsTransformerWithErrors<KEMException> {
        /**
         * Specifies whether the current node is the left most or the right most child of the parent.
         * This is useful because associativity can be checked at the same time with priorities.
         */
        public enum Side {LEFT, RIGHT, MIDDLE}
        private final TermCons parent;
        private final Side side;
        private final POSet<Tag> priorities;
        private final Set<Tuple2<Tag, Tag>> leftAssoc;
        private final Set<Tuple2<Tag, Tag>> rigthAssoc;

        public PriorityVisitor2(TermCons parent, Side side, POSet<Tag> priorities, Set<Tuple2<Tag, Tag>> leftAssoc, Set<Tuple2<Tag, Tag>> rightAssoc) {
            this.parent = parent;
            this.side = side;
            this.priorities = priorities;
            this.leftAssoc = leftAssoc;
            this.rigthAssoc = rightAssoc;
        }

        private final static java.util.Set<String> rewriteExceptions, kseqExceptions, letExceptions;

        static {
            rewriteExceptions = new HashSet<>();
            rewriteExceptions.add("#ruleRequires");
            rewriteExceptions.add("#ruleEnsures");
            rewriteExceptions.add("#ruleRequiresEnsures");
            rewriteExceptions.add("#KRewrite");
            rewriteExceptions.add("#withConfig");
            rewriteExceptions.add("#KList");
            kseqExceptions = new HashSet<>();
            kseqExceptions.add("#ruleRequires");
            kseqExceptions.add("#ruleEnsures");
            kseqExceptions.add("#ruleRequiresEnsures");
            kseqExceptions.add("#KRewrite");
            kseqExceptions.add("#KSequence");
            kseqExceptions.add("#KList");
            letExceptions = new HashSet<>();
            letExceptions.add("#ruleRequires");
            letExceptions.add("#ruleEnsures");
            letExceptions.add("#ruleRequiresEnsures");
            letExceptions.add("#KRewrite");
            letExceptions.add("#KSequence");
            letExceptions.add("#let");
            letExceptions.add("#KList");
        }

        public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
            Tag parentLabel = new Tag(parent.production().parseLabel().name());
            Tag localLabel = new Tag(tc.production().parseLabel().name());
            if (!parent.production().isSyntacticSubsort() && parent.production().klabel().isDefined()) {
                if (!rewriteExceptions.contains(parentLabel.name()) && localLabel.name().equals("#KRewrite")) {
                    String msg = "Rewrite is not allowed to be an immediate child of " + parent.production().parseLabel() +
                            "    Use parentheses: (x)=>(y) to set the proper scope of the operations.";
                    return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
                }
                if (!kseqExceptions.contains(parentLabel.name()) && localLabel.name().equals("#KSequence")) {
                    String msg = "~> is not allowed to be an immediate child of " + parent.production().parseLabel() +
                            "    Use parentheses: (x)~>(y) to set the proper scope of the operations.";
                    return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
                }
                if (!letExceptions.contains(parentLabel.name()) && localLabel.name().equals("#let")) {
                    String msg = "#let is not allowed to be an immediate child of " + parent.production().parseLabel() +
                            "    Use parentheses: #let x = y #in (z) to set the proper scope of the operations.";
                    return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
                }
                if ((parentLabel.name().equals("#SyntacticCast") || parentLabel.name().startsWith("#SemanticCastTo")) &&
                        tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal) {
                    String msg = parent.production().klabel().get() + " is not allowed to be an immediate child of cast." +
                            "    Use parentheses: (x):Sort to set the proper scope of the operations.";
                    return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
                }
            }
            if (priorities.lessThan(parentLabel, localLabel)) {
                String msg = "Priority filter exception. Cannot use " + localLabel + " as an immediate child of " +
                        parentLabel + ". Consider using parentheses around " + localLabel;
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            if (leftAssoc.contains(new Tuple2<>(parentLabel, localLabel)) && Side.RIGHT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as an immediate right child of " +
                        parentLabel + ". Consider using parentheses around " + localLabel;
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            if (rigthAssoc.contains(new Tuple2<>(parentLabel, localLabel)) && Side.LEFT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as an immediate left child of " +
                        parentLabel + ". Consider using parentheses around " + localLabel;
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }

            return Right.apply(tc);
        }
    }
}
