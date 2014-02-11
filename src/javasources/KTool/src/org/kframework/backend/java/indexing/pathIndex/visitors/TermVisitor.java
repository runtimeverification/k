package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Author: OwolabiL
 * Date: 1/21/14
 * Time: 12:05 PM
 */
public class TermVisitor extends LocalVisitor {
    private final Set<String> pStrings;

    private final Context context;

    private String pString;
    private int currentPosition = 0;
    private boolean inner = false;
    private String currentLabel;
    private final String SEPARATOR = ".";
    private final String START_STRING = "@.";

    public TermVisitor(Context context) {
        pStrings = new HashSet<>();
        this.context = context;
    }

    @Override
    public void visit(Term node) {
        Term lookedUpK = LookupCell.find(node, "k");
        if (lookedUpK != null) {
            (LookupCell.find(node, "k")).accept(this);
        }
    }

    @Override
    public void visit(Cell cell) {
        cell.getContent().accept(this);
    }


    @Override
    public void visit(KSequence kSequence) {
        if (kSequence.size() > 0) {
//            System.out.println("1st: "+(KItem)kSequence.get(0));
            //TODO (OwolabiL): This is too messy. Restructure the conditionals
            if (kSequence.get(0) instanceof KItem) {
                boolean isKResult = context.isSubsorted("KResult", ((KItem) kSequence.get(0)).sort());
                if (isKResult) {
                    pString = START_STRING + "KResult";
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
        }
    }

    @Override
    public void visit(Token token) {

        if (pString == null) {
            if (context.isSubsorted("KResult", token.sort())) {
                pString = START_STRING + "KResult";
            } else {
                //TODO(OwolabiL): Use a better check than the nullity of pString
                pStrings.add(START_STRING + token.sort());
            }
        }

        if (inner) {
            List<Production> productions1 = context.productionsOf(currentLabel);
            //the production of .K is empty
            if (productions1.isEmpty()) {
                return;
            }
            ArrayList<Production> productions = (ArrayList<Production>) productions1;
            Production p = productions.get(0);
            if (context.isSubsorted("KResult", token.sort())) {
                if (pString != null) {
                    if (productions.size() == 1) {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + token.sort());
                    } else {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + "UserList");
                    }
                }
            } else {
                if (productions.size() == 1) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + p.getChildSort(0));
                } else {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + "UserList");
                }
            }
        }
    }

    @Override
    public void visit(KItem kItem) {
        if (kItem.kLabel() instanceof KLabelFreezer) {
            if (pString != null) {
                TokenVisitor visitor = new TokenVisitor(context, pString);
                kItem.kLabel().accept(visitor);
                pStrings.addAll(visitor.getCandidates());
            }
        } else {
            if (!inner) {
                inner = true;
                currentLabel = kItem.kLabel().toString();
                ((KLabelConstant)kItem.kLabel()).accept(this);
                ((KList)kItem.kList()).accept(this);
            } else {
                int kListSize = ((KList) kItem.kList()).size();
                if (kListSize == 0 && currentLabel.equals("List{\",\"}")) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + "'.List{\",\"}");
                } else if (kListSize == 0 && kItem.sort().equals("#ListOf#Bot{\",\"}")) {
                    pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + "'.List{\",\"}");
                } else {
                    if (context.isListSort(kItem.sort())) {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + "UserList");
                    } else {
                        pStrings.add(pString + SEPARATOR + currentPosition + SEPARATOR + kItem.sort());
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

//    @Override
//    public void visit(KLabel kLabel) {
//        pString = START_STRING + kLabel.toString();
//    }

    @Override
    public void visit(KLabelConstant kLabel) {
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

    private class TokenVisitor extends TermVisitor {
        private final String baseString;
        private String pString;
        private final List<String> candidates;

        public TokenVisitor(Context context, String string) {
            super(context);
            this.baseString = string;
            candidates = new ArrayList<>();
        }

        @Override
        public void visit(KLabelFreezer kLabelFreezer) {
            KItem frozenItem = (KItem) kLabelFreezer.term();
            frozenItem.kLabel().accept(this);
            frozenItem.kList().accept(this);
        }

//        @Override
//        public void visit(KLabel kLabel) {
//            pString = baseString + ".1." + kLabel;
//        }

        @Override
        public void visit(KLabelConstant kLabel) {
            pString = baseString + ".1." + kLabel.toString();
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
