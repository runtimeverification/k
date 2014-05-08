// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.BuiltinMap;

import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.utils.general.IndexingStatistics;

import java.io.Serializable;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.util.concurrent.TimeUnit;


/**
 * This visitor class is used to traverse the current term being rewritten in order to select what
 * rules may be applied.
 * <p/>
 * Author: OwolabiL
 * Date: 1/21/14
 * Time: 12:05 PM
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class TermVisitor extends LocalVisitor implements Serializable {
    private static final String K_RESULT = "KResult";
    private static final String EMPTY_LIST_LABEL = "'.List{\",\"}";
    private static final String EMPTY_LIST_SORT = "#ListOf#Bot{\",\"}";
    private static final String LIST_LABEL = "List{\",\"}";
    private static final String USER_LIST_REPLACEMENT = "UserList";
    private static final String K_ITEM_SORT = "KItem";
    private static final String EMPTY_K = "EMPTY_K";
    private static final String K_STRING = "K";
    public static final String NO_K_CELL_PSTRING = "@.NO_K_CELL";
    private final Set<String> pStrings;
    private final Context context;
    private final boolean indexingStats;

    private String pString;
    private int currentPosition = 0;
    private boolean inner = false;
    private String currentLabel;
    private final String SEPARATOR = ".";
    private final String START_STRING = "@.";
    private boolean defHasNOKCellRules;

    // these flags are used to decide whether (or not) to try the i/o rules while rewriting
    // the current term.
    private boolean addInputRules;
    private boolean addOutputRules;

    public TermVisitor(Context context) {
        pStrings = new LinkedHashSet<>();
        this.context = context;
        this.indexingStats = context.javaExecutionOptions.indexingStats;
    }

    public TermVisitor(Context context, boolean hasNOKCellRules) {
        this(context);
        this.defHasNOKCellRules |= hasNOKCellRules;
    }

    @Override
    public void visit(Term node) {
        int BASE_IO_CELL_SIZE = 2;
        if (indexingStats) {
            IndexingStatistics.getPStringStopwatch.reset();
            IndexingStatistics.getPStringStopwatch.start();
        }
        //first find all the term's cells of interest in  a single pass
        CellVisitor cellVisitor = new CellVisitor(context);
        node.accept(cellVisitor);
        pStrings.addAll(cellVisitor.getkCellPStings());

        //needed for kool-static where some rules have no k-cell. Note that we add it last.
        if (defHasNOKCellRules){
            pStrings.add(NO_K_CELL_PSTRING);
        }

        if (indexingStats) {
            IndexingStatistics.getPStringStopwatch.stop();
            IndexingStatistics.getPStringTimes.add(
                    IndexingStatistics.getPStringStopwatch.elapsed(TimeUnit.MICROSECONDS));
            IndexingStatistics.traverseCellsStopwatch.reset();
            IndexingStatistics.traverseCellsStopwatch.start();
        }
        Cell cellOfInterest;

        Cell ioCell;
        List<Term> ioCellList;
        //check whether output rules should be added
        if (cellVisitor.getOutCell() != null) {
            ioCell = cellVisitor.getOutCell();
            ioCellList = ((BuiltinList) ioCell.getContent()).elements();
            if (ioCellList.size() > BASE_IO_CELL_SIZE) {
                addOutputRules = true;
            } else {
                OutPutCellVisitor outPutCellVisitor = new OutPutCellVisitor();
                (ioCell.getContent()).accept(outPutCellVisitor);
                if (outPutCellVisitor.isAddOutCell()) {
                    addOutputRules = true;
                }
            }
        }
        //check whether input rules should be added
        cellOfInterest = cellVisitor.getInCell();
        if (cellOfInterest != null) {
            ioCellList = ((BuiltinList) cellOfInterest.getContent()).elements();
            if (ioCellList.size() > BASE_IO_CELL_SIZE) {
                addInputRules = true;
            }
        }

        if (indexingStats) {
            IndexingStatistics.traverseCellsStopwatch.stop();
            IndexingStatistics.traverseCellsTimes.add(
                    IndexingStatistics.traverseCellsStopwatch.elapsed(TimeUnit.MICROSECONDS));
        }

    }

    @Override
    public void visit(KSequence kSequence) {
        if (kSequence.size() > 0) {
            //TODO (OwolabiL): This is too messy. Restructure the conditionals
            if (kSequence.get(0) instanceof KItem) {
                boolean isKResult = context.isSubsorted(K_RESULT, (kSequence.get(0)).sort());
                if (isKResult) {
                    pString = START_STRING + K_RESULT;
                    kSequence.get(1).accept(this);
                } else {
                    kSequence.get(0).accept(this);
                    if (kSequence.get(0) instanceof Token) {
                        kSequence.get(1).accept(this);
                    }
                }
            } else {
                kSequence.get(0).accept(this);
                if (kSequence.get(0) instanceof Token) {
                    kSequence.get(1).accept(this);
                }
            }
        } else if (kSequence.size() == 0) {
            //there are cases (e.g., in SIMPLE's join rule) where we need to
            // know that one of the K cells in the configuration is empty.
            pStrings.add(START_STRING + EMPTY_K);
        }
    }

    @Override
    public void visit(Token token) {
        //check if we are just starting to create a pString for this term
        //TODO(OwolabiL): Use a better check than the nullity of pString
        if (pString == null) {
            if (context.isSubsorted(K_RESULT, token.sort())) {
                pString = START_STRING + K_RESULT;
                //hack for kool-dynamic
                if (token instanceof BoolToken){
                    pStrings.add(START_STRING+token.sort());
                }
            } else {
                pStrings.add(START_STRING + token.sort());
            }
        }

        if (inner) {
            List<Production> productions1 = context.productionsOf(currentLabel);
            //the production of .K is empty
            if (productions1.isEmpty()) {
                return;
            }

            if (context.isSubsorted(K_RESULT, token.sort())) {
                if (pString != null) {
                    ArrayList<Production> productions = (ArrayList<Production>) productions1;
                    if (productions.size() == 1) {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR +
                                token.sort());
                    } else {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR +
                                USER_LIST_REPLACEMENT);
                    }

                    //hack for kool-dynamic
                    if (token instanceof BoolToken){
                        pStrings.add(pString+".1."+token.sort());
                    }

                }
            } else {
                ArrayList<Production> productions = (ArrayList<Production>) productions1;
                Production p = productions.get(0);
                if (productions.size() == 1) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR +
                            p.getChildSort(0));
                } else {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR +
                            USER_LIST_REPLACEMENT);
                }
            }
        }
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        if (pString == null) {
            pStrings.add(START_STRING + uninterpretedToken.sort());
        } else {
            pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR +
                    uninterpretedToken.sort());
        }
    }

    @Override
    public void visit(KItem kItem) {
        //TODO(OwolabiL): This is starting to get nasty. Refactor.
        if (kItem.kLabel() instanceof KLabelFreezer) {

            if (pString != null) {
                TokenVisitor visitor = new TokenVisitor(context, pString);
                kItem.kLabel().accept(visitor);
                pStrings.addAll(visitor.getCandidates());
            } else if (pString == null){
                //this works for bool ~> (# if_then_else). may not always work
                TokenVisitor visitor = new TokenVisitor(context, "@.KResult");
                kItem.kLabel().accept(visitor);
                pStrings.addAll(visitor.getCandidates());
            }
        } else {
            if (!inner) {
                inner = true;
                currentLabel = kItem.kLabel().toString();
                //needed for simple typed static
                if (context.isSubsortedEq(K_RESULT,kItem.sort()) && ((KList)kItem.kList()).size() == 0){
                    String kItemSort = kItem.sort();
                    pStrings.add(START_STRING+kItemSort);
                }

                // added to handle a case in kool typed static. 1st element in
                // kSequence is already a KResult, but the second Item is simply
                // a KLabel applied to an empty KList:
                //      <k>
                //        (void) ~> discard ~> 'class(theMain) ~> HOLE ;
                //        </k>
                if (!context.isSubsortedEq(K_RESULT,kItem.sort()) && ((KList)kItem.kList()).size() == 0){
                    if (pString != null) {
                        pStrings.add(pString);
                    }
                }

                kItem.kLabel().accept(this);
                kItem.kList().accept(this);
            } else {
                int kListSize = ((KList) kItem.kList()).size();
                if (kListSize == 0 && currentLabel.equals(LIST_LABEL)) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR
                            + EMPTY_LIST_LABEL);
                } else if (kListSize == 0 && kItem.sort().equals(EMPTY_LIST_SORT)) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR
                            + EMPTY_LIST_LABEL);
                } else {
                    if (context.isListSort(kItem.sort())) {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR
                                + USER_LIST_REPLACEMENT);
                        // TODO(Owolabileg): Bad hack to be removed - trying this out for fun where
                        // other kItems apart from kList can have multiple productions
                        TokenVisitor visitor = new TokenVisitor(context, pString);
                        kItem.kLabel().accept(visitor);
                        kItem.kList().accept(visitor);
                        pStrings.addAll(visitor.getCandidates());
                    } else {
                        if (kListSize > 0 && ((KList) kItem.kList()).get(0) instanceof Token
                                && !context.isSubsortedEq(K_RESULT,kItem.sort())) {
                            String sort = ((Token) ((KList) kItem.kList()).get(0)).sort();
                            if (context.isSubsorted(K_RESULT, sort)) {
                                if (kItem.sort().equals(K_ITEM_SORT)) {
                                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR
                                            + kItem.kLabel()
                                            + SEPARATOR + (currentPosition) + SEPARATOR + sort);
                                } else {
                                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR
                                            + K_RESULT);
                                }
                            } else {
                                ArrayList<Production> productions =
                                        (ArrayList<Production>) context.productionsOf(currentLabel);
                                Production p = productions.get(0);
                                String test = pString + SEPARATOR + (currentPosition) + SEPARATOR;
                                if (p.getChildSort(currentPosition - 1).equals(K_STRING)) {
                                    //TODO(OwolabiL): This needs to be investigated further and
                                    // handled properly. This is not a good way to handle this case.
                                    pStrings.add(test + kItem.kLabel() + SEPARATOR + "1.Exp");
                                } else {
                                    pStrings.add(test + p.getChildSort(currentPosition - 1));
                                }
                            }
                        } else {
                            //TODO(OwolabiL): This needs to be investigated further and handled
                            // properly. Plus there's duplicated code here to be possibly removed.
                            String test = pString + SEPARATOR + currentPosition + SEPARATOR;
                            ArrayList<Production> productions =
                                    (ArrayList<Production>) context.productionsOf(currentLabel);
                            Production p = productions.get(0);
                            if (p.getChildSort(currentPosition - 1).equals(K_STRING)) {
                                pStrings.add(test + kItem.kLabel() + SEPARATOR + (currentPosition) +
                                        SEPARATOR + kItem.sort());
                            } else {
                                pStrings.add(test + kItem.sort());
                            }
                        }
                    }
                }
            }
        }
    }

    @Override
    public void visit(KList kList) {
        if (kList.size() == 0) {
            pStrings.add(pString);
        } else {
            for (int i = 0; i < kList.size(); i++) {
                currentPosition = i + 1;
                kList.get(i).accept(this);
            }
        }
    }

    @Override
    public void visit(KLabelConstant kLabel) {
        //making sure this does not shadow existing
        pString = START_STRING + kLabel.toString();
    }

    /**
     * The environment recovery will need this
     *
     * @param builtinMap the map to be visited
     */
    @Override
    public void visit(BuiltinMap builtinMap) {
        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + builtinMap.sort());
    }

    public Set<String> getpStrings() {
        return pStrings;
    }

    public boolean isAddInputRules() {
        return addInputRules;
    }

    public boolean isAddOutputRules() {
        return addOutputRules;
    }

    private class TokenVisitor extends TermVisitor {

        private final String baseString;
        private String pString;
        private final List<String> candidates;

        public TokenVisitor(Context context, String string) {
            super(context);
            baseString = string;
            candidates = new ArrayList<>();
        }

        @Override
        public void visit(KLabelFreezer kLabelFreezer) {
            KItem frozenItem = (KItem) kLabelFreezer.term();
            frozenItem.kLabel().accept(this);
            frozenItem.kList().accept(this);
        }

        @Override
        public void visit(KLabelConstant kLabel) {
            pString = baseString + ".1." + kLabel.toString();
        }

        @Override
        public void visit(UninterpretedToken uninterpretedToken) {
            candidates.add(pString + SEPARATOR + currentPosition + SEPARATOR
                    + uninterpretedToken.sort());
        }

        @Override
        public void visit(KList kList) {
            for (int i = 0; i < kList.size(); i++) {
                currentPosition = i + 1;
                kList.get(i).accept(this);
            }
        }

        @Override
        public void visit(Hole hole) {
            candidates.add(pString + SEPARATOR + currentPosition + ".HOLE");
        }

        @Override
        public void visit(Token token) {
            candidates.add(pString + SEPARATOR + currentPosition + SEPARATOR + token.sort());
        }

        public void visit(KItem kItem) {
            candidates.add(pString + SEPARATOR + currentPosition + SEPARATOR + kItem.sort());
        }

        private List<String> getCandidates() {
            return candidates;
        }

    }
}
