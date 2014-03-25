package org.kframework.parser.concrete2;

import java.util.regex.Pattern;

import org.kframework.kil.Configuration;
import org.kframework.kil.KLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rule;
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
            NonTerminal nt = new NonTerminal(new NonTerminalId(sort),
                    new StateId("Entry-" + sort), OrderingInfo.ZERO,
                    new StateId("Exit-" + sort), OrderingInfo.ZERO);
            grammar.add(nt);
        }
    }

    private int seed = 0;
    private Grammar grammar = new Grammar();

    private int getUid() {
        return seed++;
    }

    @Override
    public void visit(Production prd) {
        NonTerminal nt = grammar.get(prd.getSort());
        NextableState previous = nt.entryState;
        if (prd.isListDecl()) {
            UserList ul = (UserList) prd.getItems().get(0);

            NonTerminalState Id = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    grammar.get(ul.getSort()),
                    false, null, null);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile("\\Q" + ul.getSeparator() + "\\E"),
                    null, TreeCleanerVisitor.DELETESORT);
            NonTerminalState Ids = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    grammar.get(prd.getSort()),
                    false, new KLabelConstant(prd.getKLabel()), null);
            nt.entryState.next.add(Id);
            Id.next.add(pstate);
            pstate.next.add(Ids);
            Ids.next.add(nt.exitState);

            if (!ul.getListType().equals("*")) {
                NonTerminalState Id2 = new NonTerminalState(
                        new StateId(prd.getSort() + "-S-" + getUid()),
                        nt, OrderingInfo.ZERO,
                        grammar.get(ul.getSort()),
                        false, null, null);
                previous.next.add(Id2);
                previous = Id2;
            }
            // label for '.Ids (list terminator)
            NonTerminal specialNt = getListTerminatorNT(prd.getSort());
            NonTerminalState special = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    specialNt,
                    false,  null, null);
            previous.next.add(special);
            previous = special;
            // label for '_,_
            if (!ul.getListType().equals("*")) {
                Grammar.RegExState epsilonForLabel2 = new Grammar.RegExState(
                        new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                        nt, OrderingInfo.ZERO,
                        Pattern.compile(""),
                        new KLabelConstant(prd.getKLabel()),
                        TreeCleanerVisitor.DELETESORT);
                previous.next.add(epsilonForLabel2);
                previous = epsilonForLabel2;
            }
            /**
             * Allows for empty* cons lists which always terminate with the identity element of the list.
             *                           '_,_
             * (|-|-->[Id]----->(,)---->[Ids]--|->|)
             *    |                            |
             *    |-->[Id]-->[special]->(e2)---|
             *                 '.Ids     '_,_
             */
        } else if (prd.isSubsort()) {
            KLabel kl = null;
            if (prd.containsAttribute("klabel")) {
                kl = new KLabelConstant(prd.getKLabel());
            }
            Sort srt = (Sort) prd.getItems().get(0);
            NonTerminalState nts = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    grammar.get(srt.getName()),
                    false, kl, prd.getSort());
            previous.next.add(nts);
            previous = nts;
        } else if (prd.isLexical()) {
            Lexical lx = (Lexical) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(lx.getLexicalRule()),
                    null, prd.getSort());
            previous.next.add(pstate);
            previous = pstate;
        } else if (prd.isConstant()) {
            Terminal terminal = (Terminal) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    // TODO: if there is a \\E in the input string, this next line will fail
                    // should double escape \ if there is an odd number
                    Pattern.compile("\\Q" + terminal.getTerminal() + "\\E"),
                    null, prd.getSort());
            previous.next.add(pstate);
            previous = pstate;
        } else {
            // just a normal production with Terminals and Sort alternations
            for (ProductionItem prdItem : prd.getItems()) {
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    PrimitiveState pstate = new RegExState(
                            new StateId(prd.getSort() + "-T-" + getUid()),
                            nt, OrderingInfo.ZERO,
                            // TODO: if there is a \\E in the input string, this next line will fail
                            // should double escape \ if there is an odd number
                            Pattern.compile("\\Q" + terminal.getTerminal() + "\\E"),
                            null, TreeCleanerVisitor.DELETESORT);
                    previous.next.add(pstate);
                    previous = pstate;
                } else if (prdItem instanceof Sort) {
                    Sort srt = (Sort) prdItem;
                    NonTerminalState nts = new NonTerminalState(
                            new StateId(prd.getSort() + "-S-" + getUid()),
                            nt, OrderingInfo.ZERO,
                            grammar.get(srt.getName()),
                            false, null, null);
                    previous.next.add(nts);
                    previous = nts;
                } else {
                    assert false : "Didn't expect this ProductionItem type here: " + prdItem.getClass().getName();
                }
            }
            Grammar.RegExState epsilonForLabel = new Grammar.RegExState(
                    new Grammar.StateId(prd.getSort() + "-ET-" + getUid()),
                    nt, OrderingInfo.ZERO,
                    Pattern.compile(""),
                    new KLabelConstant(prd.getKLabel()),
                    TreeCleanerVisitor.DELETESORT);
            previous.next.add(epsilonForLabel);
            previous = epsilonForLabel;
        }
        previous.next.add(nt.exitState);
    }

    // label for '.Ids (list terminator)
    private NonTerminal getListTerminatorNT(String sort) {
        NonTerminal nt = new NonTerminal(new NonTerminalId(sort + "-special"),
                new StateId("Entry-special-" + sort), OrderingInfo.ZERO,
                new StateId("Exit-special-" + sort), OrderingInfo.ZERO);
        Grammar.RegExState epsilonForLabel = new Grammar.RegExState(
                new Grammar.StateId(sort + "-ET-" + getUid()),
                nt, OrderingInfo.ZERO,
                Pattern.compile(""),
                new KLabelConstant("'." + sort),
                TreeCleanerVisitor.DELETESORT);
        nt.entryState.next.add(epsilonForLabel);
        epsilonForLabel.next.add(nt.exitState);
        return nt;
    }

    @Override
    public void visit(Rule s) {
        // skip visiting rules, contexts and configurations
    }

    @Override
    public void visit(Configuration s) {
        // skip visiting rules, contexts and configurations
    }

    @Override
    public void visit(org.kframework.kil.Context s) {
        // skip visiting rules, contexts and configurations
    }

    public Grammar getGrammar() {
        grammar.addWhiteSpace();
        grammar.finalize();
        return grammar;
    }
}
