package org.kframework.parser.concrete2;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;

import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalId;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.RegExState;
import org.kframework.parser.concrete2.Grammar.State.OrderingInfo;
import org.kframework.parser.concrete2.Grammar.StateId;

/**
 * A simple visitor that goes through every accessible production and creates the NFA states for the
 * parser. First step is to create a NonTerminal object for every declared syntactic sort. These
 * will be referenced each time a NonTerminalState is created.
 */
public class KSyntax2GrammarStatesFilter extends BasicVisitor {
    public KSyntax2GrammarStatesFilter(Context context) {
        super(KSyntax2GrammarStatesFilter.class.getName(), context);

        // create a NonTerminal for every declared sort
        for (String sort : context.definedSorts) {
            if (!ntmap.containsKey(sort)) {
                NonTerminal nt = new NonTerminal(new NonTerminalId(sort),
                        new StateId("Entry-" + sort), OrderingInfo.ZERO,
                        new StateId("Exit-" + sort), OrderingInfo.ZERO);
                ntmap.put(sort, nt);
            }
        }
    }

    private int seed = 0;
    private Map<String, NonTerminal> ntmap = new HashMap<>();
    private int getUid() {
        return seed++;
    }

    @Override
    public void visit(Production prd) {
        NonTerminal nt = ntmap.get(prd.getSort());
        NextableState previous = nt.entryState;
        if (prd.isListDecl()) {
            UserList ul = (UserList) prd.getItems().get(0);
            // label for '_,_
            Grammar.RegExState epsilonForLabel1 = new Grammar.RegExState(
                    new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(""),
                    new KLabelConstant(prd.getKLabel()));
            // label for '.Ids (list terminator)
            Grammar.RegExState epsilonForLabel2 = new Grammar.RegExState(
                    new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(""),
                    new KLabelConstant("'." + prd.getSort()));
            previous.next.add(epsilonForLabel1);
            previous.next.add(epsilonForLabel2);
            NonTerminalState nts = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    ntmap.get(ul.getSort()),
                    false, null);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(ul.getSeparator()),
                    null);
            epsilonForLabel1.next.add(nts);
            // if the list can be empty add the jump connection
            if (ul.getListType().equals("*"))
                nts.next.add(epsilonForLabel2);
            nts.next.add(pstate);
            pstate.next.add(epsilonForLabel1);
            previous = epsilonForLabel2;
            /**
             * Allows for empty* cons lists which always terminate with the identity element of the list.
             *     |----empty-list----|
             *     |                  |
             * (|--|--[e1]------[Id]----->[e2]---|)
             *          ^        |
             *          |-[","]<-|
             */
        } else if (prd.isSubsort()) {
            if (prd.containsAttribute("klabel")) {
                Grammar.RegExState epsilonForLabel1 = new Grammar.RegExState(
                        new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                        nt, OrderingInfo.ZERO,
                        Pattern.compile(""),
                        new KLabelConstant(prd.getKLabel()));
                previous.next.add(epsilonForLabel1);
                previous = epsilonForLabel1;
            }
            Sort srt = (Sort) prd.getItems().get(0);
            NonTerminalState nts = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    ntmap.get(srt.getName()),
                    false, null);
            previous.next.add(nts);
            previous = nts;
        } else if (prd.isLexical()) {
            // TODO: this should have the sort of the production and not K
            Lexical lx = (Lexical) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(lx.getLexicalRule()),
                    null);
            previous.next.add(pstate);
            previous = pstate;
        } else if (prd.isConstant()) {
            // TODO: this should have the sort of the production and not K
            Terminal terminal = (Terminal) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(terminal.getTerminal()),
                    null);
            previous.next.add(pstate);
            previous = pstate;
        } else {
            // just a normal production with Terminals and Sort alternations
            Grammar.RegExState epsilonForLabel = new Grammar.RegExState(
                    new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(""),
                    new KLabelConstant(prd.getKLabel()));
            previous.next.add(epsilonForLabel);
            previous = epsilonForLabel;
            for (ProductionItem prdItem : prd.getItems()) {
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    PrimitiveState pstate = new RegExState(
                            new StateId(prd.getSort() + "-T-" + getUid()),
                            nt, OrderingInfo.ZERO,
                            Pattern.compile(terminal.getTerminal()),
                            null);
                    previous.next.add(pstate);
                    previous = pstate;
                } else if (prdItem instanceof Sort) {
                    Sort srt = (Sort) prdItem;
                    NonTerminalState nts = new NonTerminalState(
                            new StateId(prd.getSort() + "-S-" + getUid()),
                            nt, OrderingInfo.ZERO,
                            ntmap.get(srt.getName()),
                            false, null);
                    previous.next.add(nts);
                    previous = nts;
                } else {
                    assert false : "Didn't expect this ProductionItem type here: " + prdItem.getClass().getName();
                }
            }
        }
    }

    @Override
    public void visit(Sentence s) {
        // skip visiting rules, contexts and configurations
    }
}
