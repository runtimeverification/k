// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Sets;
import org.junit.Rule;
import org.junit.rules.ExpectedException;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.*;

import org.junit.Test;
import org.junit.Assert;

import java.util.*;

import static org.kframework.kore.KORE.*;

public class CloseCellsTest {

    final SortInfo sortInfo = new SortInfo() {{
        addOp("Map", "'_Map_");
        addOp("List", "'_List_");
    }};

    final TestConfiguration cfgInfo = new TestConfiguration() {{
        addCell(null, "ThreadCell", "<thread>", Multiplicity.STAR);
        addCell("ThreadCell", "KCell", "<k>", Sort("K"));
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
        addCell(null, "ListCell", "<list>", Multiplicity.STAR, Sort("List"));
        addDefault("EnvCell", cell("<env>", KApply(KLabel(".Map"))));
        addDefault("KCell", cell("<k>",stringToToken("defaultK")));
    }};
    final LabelInfo labelInfo = new LabelInfo() {{
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
        addLabel("ThreadCell", "<thread>");
        addLabel("ListCell", "<list>");
        addLabel("Map", "'_Map_", true, true);
        addLabel("List", "'_List_", true);
    }};
    final ConcretizationInfo cfg = new ConcretizationInfo(cfgInfo, labelInfo);

    final static K dots = KApply(KLabel("#dots"));

    public class CloseTerm {
        private int counter = 0;
        private Set<KVariable> vars = Sets.newHashSet();
        private KRewrite rhsOf = null;

        public CloseTerm() {
        }

        public KVariable newDotVariable() {
            KVariable newLabel;
            do {
                newLabel = KVariable("DotVar" + (counter++));
            } while (vars.contains(newLabel));
            vars.add(newLabel);
            return newLabel;
        }

        public K close(K term) {
            counter = 0;
            vars = Sets.newHashSet();
            rhsOf = null;
            new VisitKORE() {
                @Override
                public Void apply(KVariable v) {
                    vars.add(v);
                    return super.apply(v);
                }
            }.apply(term);

            return new TransformKORE() {
                @Override
                public K apply(KApply k) {
                    if (!cfg.isCell(k.klabel())) {
                        return super.apply(k);
                    } else {
                        return closeCell(k);
                    }
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

        protected K closeCell(K term) {
            if (!(term instanceof KApply)) {
                return term;
            }
            KLabel label = ((KApply) term).klabel();
            if (!cfg.isCell(label)) {
                return term;
            }

            List<K> items = ((KApply) term).klist().items();
            boolean openLeft = items.size() > 0 && items.get(0).equals(dots);
            boolean openRight = items.size() > 1 && items.get(items.size() - 1).equals(dots);
            List<K> contents = items.subList(openLeft ? 1 : 0,
                    openRight ? items.size() - 1 : items.size());

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
                    }
                }

                if (!openLeft && !openRight) {
                    if (required.isEmpty()) {
                        return term;
                    } else {
                        throw new IllegalArgumentException("Closed parent cell missing " +
                                "required children " + required.toString() + " " + term.toString());
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
                        + " but there are " + contents.size() + " in " + term.toString());
            }

            if (!openLeft && !openRight) {
                return term;
            }
            if (rhsOf != null) {
                throw new IllegalArgumentException("Leaf cells on right hand side of a rewrite" +
                        " may not be open, but " + term.toString() + " is right of " + rhsOf.toString());
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
                            + cellType.name() + " when closing cell " + term.toString());
                }
                LabelInfo.AssocInfo info = labelInfo.getAssocInfo(closeOperator);
                if (!info.isAssoc() && openLeft && openRight) {
                    throw new IllegalArgumentException(
                            "Ambiguity closing a cell. Operator " + closeOperator.toString()
                                    + " for sort " + cellType.name() + " is not associative, "
                                    + "but the cell has ellipses on both sides " + term.toString());
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

    @Test
    public void testSimpleClosure() {
        K term = cell("<k>", KApply(KLabel("_+_"), KVariable("I"), KVariable("J")), dots);
        K expected = cell("<k>", KSequence(KApply(KLabel("_+_"), KVariable("I"), KVariable("J")),
                KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseTerm().close(term));
    }

    @Test
    public void testCloseMap() {
        K term = cell("<env>",dots,KApply(KLabel("'_|=>_"),intToToken(1),intToToken(2)));
        K expected = cell("<env>", KApply(KLabel("'_Map_"), KApply(KLabel("'_|=>_"), intToToken(1), intToToken(2)), KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseTerm().close(term));
    }

    @Test
    public void testCloseList() {
        K term = KApply(KLabel("#cells"),
                cell("<list>", dots, intToToken(1)),
                cell("<list>", intToToken(2), dots),
                cell("<list>", dots, intToToken(3), dots));
        K expected = KApply(KLabel("#cells"),
                cell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar0"), intToToken(1))),
                cell("<list>", KApply(KLabel("'_List_"), intToToken(2), KVariable("DotVar1"))),
                cell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar2"), KApply(KLabel("'_List_"), intToToken(3), KVariable("DotVar3")))));
        Assert.assertEquals(expected, new CloseTerm().close(term));
    }

    @Test
    public void testCloseCellVar() {
        K term = KApply(KLabel("#cells"),
                cell("<thread>",dots,cell("<k>", intToToken(1))),
                cell("<thread>",cell("<k>", intToToken(2)),dots),
                cell("<thread>",dots,cell("<k>", intToToken(2)),dots));
        K expected = KApply(KLabel("#cells"),
                cell("<thread>",cell("<k>",intToToken(1)),KVariable("DotVar0")),
                cell("<thread>",cell("<k>",intToToken(2)),KVariable("DotVar1")),
                cell("<thread>",cell("<k>",intToToken(2)),KVariable("DotVar2")));
        Assert.assertEquals(expected, new CloseTerm().close(term));
    }

    @Rule
    public ExpectedException exception = ExpectedException.none();

    @Test
    public void testClosedCellError1() {
        K term = cell("<thread>",cell("<k>"));
        exception.expect(IllegalArgumentException.class);
        exception.expectMessage("Closed parent cell missing required children [EnvCell] <thread>(<k>())");
        new CloseTerm().close(term);
    }

    @Test
    public void testCloseCellTerm() {
        K term = KRewrite(KApply(KLabel("#cells")),
                KApply(KLabel("#cells"),
                        cell("<thread>", dots, cell("<k>", intToToken(1))),
                        cell("<thread>", cell("<k>", intToToken(2)), dots),
                        cell("<thread>", dots, cell("<env>", intToToken(2)), dots)));
        K expected = KRewrite(KApply(KLabel("#cells")),
                KApply(KLabel("#cells"),
                cell("<thread>", cell("<k>", intToToken(1)), cell("<env>",KApply(KLabel(".Map")))),
                cell("<thread>", cell("<k>", intToToken(2)), cell("<env>",KApply(KLabel(".Map")))),
                cell("<thread>", cell("<env>", intToToken(2)), cell("<k>",stringToToken("defaultK")))));
        Assert.assertEquals(expected, new CloseTerm().close(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
