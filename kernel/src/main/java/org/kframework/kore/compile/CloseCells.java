// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Sets;
import org.kframework.Collections;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;

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
    private int counter = 0;
    private Set<KVariable> vars = Sets.newHashSet();
    private KRewrite rhsOf = null;
    private ConcretizationInfo cfg;
    private SortInfo sortInfo;
    private LabelInfo labelInfo;
    final static K dots = KApply(KLabel("#dots"));

    public CloseCells(ConfigurationInfo cfg, SortInfo sortInfo, LabelInfo labelInfo) {
        this.cfg = new ConcretizationInfo(cfg, labelInfo);
        this.sortInfo = sortInfo;
        this.labelInfo = labelInfo;
    }

    public KVariable newDotVariable() {
        KVariable newLabel;
        do {
            newLabel = KVariable("DotVar" + (counter++));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

    protected void resetVars() {
        counter = 0;
        vars.clear();
        rhsOf = null;
    }

    protected void gatherVars(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KVariable v) {
                vars.add(v);
                return super.apply(v);
            }
        }.apply(term);
    }

    protected K transform(K term) {
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

    public K close(K term) {
        resetVars();
        gatherVars(term);
        return transform(term);
    }

    public Rule close(Rule rule) {
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

    public Context close(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public Sentence close(Sentence s) {
        if (s instanceof Rule) {
            return close((Rule)s);
        } else if (s instanceof Context) {
            return close((Context)s);
        } else {
            return s;
        }
    }

    ModuleTransformer moduleTransormer = ModuleTransformer.from(this::close);

    public Module close(Module m) {
        return moduleTransormer.apply(m);
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
            Set<Sort> required = new HashSet<>();
            for (Sort child : cfg.getChildren(label)) {
                if (cfg.getMultiplicity(child) == ConfigurationInfo.Multiplicity.ONE) {
                    required.add(child);
                }
            }
            for (K item : contents) {
                if (item instanceof KApply) {
                    required.remove(labelInfo.getCodomain(((KApply) item).klabel()));
                } else if (item instanceof KVariable) {
                    // TODO: should consider variable sorts
                    required.clear();
                }
            }

            if (!openLeft && !openRight) {
                if (required.isEmpty()) {
                    return KApply(label, KList(contents));
                } else {
                    throw new IllegalArgumentException("Closed parent cell missing " +
                            "required children " + required.toString() + " " + cell.toString());
                }
            }

            if (rhsOf == null) {
                // close with variable
                List<K> newItems = new ArrayList<>(contents.size() + 1);
                newItems.addAll(contents);
                newItems.add(newDotVariable());
                return KApply(label, KList(newItems));
            } else {
                // close by adding default cells
                List<K> newContents = new ArrayList<>(contents.size() + required.size());
                newContents.addAll(contents);
                for (Sort reqChild : required) {
                    newContents.add(cfg.getDefaultCell(reqChild));
                }
                return (KApply(label, KList(newContents)));
            }
        }

        // Is a leaf cell
        if (contents.size() != 1) {
            throw new IllegalArgumentException("Leaf cells should contain exactly 1 body term,"
                    + " but there are " + contents.size() + " in " + cell.toString());
        }

        if (!openLeft && !openRight) {
            return KApply(label, KList(contents.get(0)));
        }
        if (rhsOf != null) {
            throw new IllegalArgumentException("Leaf cells on right hand side of a rewrite" +
                    " may not be open, but " + cell.toString() + " is right of " + rhsOf.toString());
        }

        K body = contents.get(0);
        Sort cellType = cfg.leafCellType(label);
        if (cellType.equals(Sort("K"))) {
            // Need special handling to make a KSequence.
            int bodyLength;
            if (body instanceof KSequence) {
                bodyLength = ((KSequence) body).items().size();
            } else {
                bodyLength = 1;
            }
            List<K> newItems = new ArrayList<>((openLeft ? 1 : 0) + bodyLength + (openRight ? 1 : 0));
            if (openLeft) {
                newItems.add(newDotVariable());
            }
            if (body instanceof KSequence) {
                newItems.addAll(((KSequence) body).items());
            } else {
                newItems.add(body);
            }
            if (openRight) {
                newItems.add(newDotVariable());
            }
            return KApply(label, KList(KSequence(newItems)));
        } else {
            KLabel closeOperator = sortInfo.getCloseOperator(cellType);
            if (closeOperator == null) {
                throw new IllegalArgumentException("No operator registered for closing cells of sort "
                        + cellType.name() + " when closing cell " + cell.toString());
            }
            LabelInfo.AssocInfo info = labelInfo.getAssocInfo(closeOperator);
            if (!info.isAssoc() && openLeft && openRight) {
                throw new IllegalArgumentException(
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
                leftVar = newDotVariable();
            }
            if (openRight) {
                body = KApply(closeOperator, KList(body, newDotVariable()));
            }
            if (openLeft) {
                body = KApply(closeOperator, KList(leftVar, body));
            }
            return KApply(label, KList(body));
        }
    }
}
