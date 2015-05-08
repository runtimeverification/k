// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Sets;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.kframework.kore.KORE.*;

/**
 * Remove any use of dots in cells, by replacing them with variables and appropriate connectives.
 * This expects parent cells to have been added by earlier passes, it will only add variables
 *
 * The input to this pass is represents cells as described by {@link IncompleteCellUtils}.
 * In the output cells no longer have dots. Leaf cells have a single argument which is
 * the body, and parent cells are applied directly to the child cells and variables
 * as arguments of the KApply (though not necessarily in the right order) as
 * expected by {@link SortCells}.
 */
public class CloseCells {

    private final ConcretizationInfo cfg;
    private final SortInfo sortInfo;
    private final LabelInfo labelInfo;

    public CloseCells(ConfigurationInfo cfg, SortInfo sortInfo, LabelInfo labelInfo) {
        this.cfg = new ConcretizationInfo(cfg, labelInfo);
        this.sortInfo = sortInfo;
        this.labelInfo = labelInfo;
    }

    public synchronized K close(K term) {
        resetVars();
        gatherVars(term);
        return transform(term);
    }

    private Rule close(Rule rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        return new Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private Context close(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public synchronized Sentence close(Sentence s) {
        if (s instanceof Rule) {
            return close((Rule)s);
        } else if (s instanceof Context) {
            return close((Context)s);
        } else {
            return s;
        }
    }

    private int counter = 0;
    private Set<KVariable> vars = Sets.newHashSet();
    private KRewrite rhsOf = null;

    void resetVars() {
        counter = 0;
        vars.clear();
        rhsOf = null;
    }

    KVariable newDotVariable(Sort s) {
        KVariable newLabel;
        do {
            if (s == null) {
                newLabel = KVariable("DotVar" + (counter++));
            } else {
                newLabel = KVariable("DotVar" + (counter++), Att().add(Attribute.SORT_KEY, s.name()));
            }
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

    void gatherVars(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KVariable v) {
                vars.add(v);
                return super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                return super.apply(closeCell(k));
            }

            @Override
            public K apply(KRewrite k) {
                K l = apply(k.left());
                rhsOf = k;
                K r = apply(k.right());
                rhsOf = null;
                if (l != k.left() || r != k.right()) {
                    return KRewrite(l, r, k.att());
                } else {
                    return k;
                }
            }
        }.apply(term);
    }

    /**
     * Close an individual cell.
     */
    protected KApply closeCell(KApply cell) {
        KLabel label = cell.klabel();
        if (!cfg.isCell(label)) {
            return cell;
        }

        boolean openLeft = IncompleteCellUtils.isOpenLeft(cell);
        boolean openRight = IncompleteCellUtils.isOpenRight(cell);
        List<K> contents = IncompleteCellUtils.getChildren(cell);

        if (cfg.isParentCell(label)) {
            Set<Sort> requiredLeft = new HashSet<>();
            Set<Sort> requiredRight;
            for (Sort child : cfg.getChildren(label)) {
                if (cfg.getMultiplicity(child) == ConfigurationInfo.Multiplicity.ONE) {
                    requiredLeft.add(child);
                }
            }
            requiredRight = new HashSet<>(requiredLeft);
            for (K item : contents) {
                if (item instanceof KRewrite) {
                    KRewrite rw = (KRewrite) item;
                    filterRequired(requiredLeft, rw.left());
                    filterRequired(requiredRight, rw.right());
                } else {
                    filterRequired(requiredLeft, item);
                    filterRequired(requiredRight, item);
                }
            }

            if (!openLeft && !openRight) {
                if (requiredLeft.isEmpty() && requiredRight.isEmpty()) {
                    return KApply(label, KList(contents));
                } else {
                    if (requiredLeft.equals(requiredRight)) {
                        throw KEMException.compilerError("Closed parent cell missing " +
                                "required children " + requiredLeft.toString(), cell);
                    } else {
                        throw KEMException.compilerError("Closed parent cell missing " +
                                "required children " + requiredLeft.toString() + " on left hand side and " + requiredRight.toString() + " on right hand side.", cell);
                    }
                }
            }

            if (rhsOf == null) {
                // close with variable
                List<K> newItems = new ArrayList<>(contents.size() + 1);
                newItems.addAll(contents);
                newItems.add(newDotVariable(null));
                return KApply(label, KList(newItems));
            } else {
                // close by adding default cells
                // since we know we are on the right hand side of a rewrite, we assume that
                // the cell cannot contain a rewrite and therefore requiredLeft will always equal
                // requiredRight. Hence we just pick one.
                List<K> newContents = new ArrayList<>(contents.size() + requiredLeft.size());
                newContents.addAll(contents);
                for (Sort reqChild : requiredLeft) {
                    newContents.add(cfg.getDefaultCell(reqChild));
                }
                return (KApply(label, KList(newContents)));
            }
        }

        // Is a leaf cell
        if (contents.size() != 1) {
            throw KEMException.criticalError("Leaf cells should contain exactly 1 body term,"
                    + " but there are " + contents.size() + " in " + cell.toString());
        }

        if (!openLeft && !openRight) {
            return KApply(label, KList(contents.get(0)));
        }
        if (rhsOf != null) {
            throw KEMException.criticalError("Leaf cells on right hand side of a rewrite" +
                    " may not be open, but " + cell.toString() + " is right of " + rhsOf.toString());
        }

        K body = contents.get(0);
        Sort cellType = cfg.leafCellType(label);
        if (cellType.equals(Sorts.K())) {
            // Need special handling to make a KSequence.
            int bodyLength;
            if (body instanceof KSequence) {
                bodyLength = ((KSequence) body).items().size();
            } else {
                bodyLength = 1;
            }
            List<K> newItems = new ArrayList<>((openLeft ? 1 : 0) + bodyLength + (openRight ? 1 : 0));
            if (openLeft) {
                newItems.add(newDotVariable(cellType));
            }
            if (body instanceof KSequence) {
                newItems.addAll(((KSequence) body).items());
            } else {
                newItems.add(body);
            }
            if (openRight) {
                newItems.add(newDotVariable(cellType));
            }
            return KApply(label, KList(KSequence(newItems)));
        } else {
            KLabel closeOperator = sortInfo.getCloseOperator(cellType);
            if (closeOperator == null) {
                throw KEMException.criticalError("No operator registered for closing cells of sort "
                        + cellType.name() + " when closing cell " + cell.toString());
            }
            LabelInfo.AssocInfo info = labelInfo.getAssocInfo(closeOperator);
            if (!info.isAssoc() && openLeft && openRight) {
                throw KEMException.criticalError(
                        "Ambiguity closing a cell. Operator " + closeOperator.toString()
                                + " for sort " + cellType.name() + " is not associative, "
                                + "but the cell has ellipses on both sides " + cell.toString());
            }
            if (info.isComm() && (!openLeft || !openRight || info.isAssoc())) {
                openLeft = false;
                openRight = true;
            }
            KVariable leftVar = null;
            if (openLeft) {
                leftVar = newDotVariable(cellType);
            }
            if (openRight) {
                body = KApply(closeOperator, KList(body, newDotVariable(cellType)));
            }
            if (openLeft) {
                body = KApply(closeOperator, KList(leftVar, body));
            }
            return KApply(label, KList(body));
        }
    }

    private void filterRequired(Set<Sort> required, K item) {
        if (item instanceof KApply) {
            required.remove(labelInfo.getCodomain(((KApply) item).klabel()));
        } else if (item instanceof KVariable) {
            if (item.att().contains(Attribute.SORT_KEY)) {
                Sort sort = Sort(item.att().<String>get(Attribute.SORT_KEY).get());
                if (cfg.cfg.isCell(sort)) {
                    required.remove(sort);
                } else {
                    required.clear();
                }
            } else {
                required.clear();
            }
        }
    }
}
