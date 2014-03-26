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
import org.kframework.parser.concrete2.Grammar.DeleteRule;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalId;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.RegExState;
import org.kframework.parser.concrete2.Grammar.RuleState;
import org.kframework.parser.concrete2.Grammar.State.OrderingInfo;
import org.kframework.parser.concrete2.Grammar.StateId;
import org.kframework.parser.concrete2.Grammar.WrapLabelRule;

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
            NonTerminal nt = new NonTerminal(new NonTerminalId(sort));
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

            NonTerminal specialNt = getListTerminatorNT(prd.getSort());
            String ntName = prd.getSort() + "-helper";
            if (ul.getListType().equals("*")) {
                // create the branch which allows for empty lists
                NonTerminalState special = new NonTerminalState(new StateId(ntName + "-S-" + getUid()), nt, specialNt, false);
                nt.entryState.next.add(special);
                special.next.add(nt.exitState);
                previous = special;
            }
            {
                NonTerminal wrapperNt = new NonTerminal(new NonTerminalId(ntName));
                NonTerminalState IdsHelper = new NonTerminalState(new StateId(ntName + "-S-" + getUid()), nt, wrapperNt, false);
                // label for '.Ids (list terminator)
                nt.entryState.next.add(IdsHelper);
                IdsHelper.next.add(nt.exitState);

                // inside the wrapperNt
                NonTerminalState Id = new NonTerminalState(new StateId(ntName + "-S-" + getUid()), wrapperNt, grammar.get(ul.getSort()), false);
                PrimitiveState separatorState = new RegExState(new StateId(ntName + "-T-" + getUid()), wrapperNt, Pattern.compile("\\Q" + ul.getSeparator() + "\\E"), TreeCleanerVisitor.DELETESORT);
                RuleState deleteToken = new RuleState(new StateId(ntName + "-D-" + getUid()), wrapperNt, new DeleteRule(1, true));
                NonTerminalState Ids = new NonTerminalState(new StateId(ntName + "-S-" + getUid()), wrapperNt, wrapperNt, false);
                RuleState labelState = new RuleState(new StateId(ntName + "-L-" + getUid()), wrapperNt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
                wrapperNt.entryState.next.add(Id);
                Id.next.add(separatorState);
                separatorState.next.add(deleteToken);
                deleteToken.next.add(Ids);
                Ids.next.add(labelState);
                labelState.next.add(wrapperNt.exitState);

                // label for '.Ids (list terminator)
                NonTerminalState special = new NonTerminalState(new StateId(prd.getSort() + "-S-" + getUid()), wrapperNt, specialNt, false);
                Id.next.add(special);
                RuleState labelState2 = new RuleState(new StateId(prd.getSort() + "-L-" + getUid()), wrapperNt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
                special.next.add(labelState2);

                labelState2.next.add(wrapperNt.exitState);
                /**
                 * Allows for non empty cons lists which always terminate with the identity element of the list.
                 * Ids:                      '_,_
                 * (|---->[Id]-|--->(,)---->[Ids]--|->|)
                 *             |                   |
                 *             |>[special]->(e2)---|
                 *                 '.Ids     '_,_
                 */
            }
        } else if (prd.isSubsort()) {
            Sort srt = (Sort) prd.getItems().get(0);
            NonTerminalState nts = new NonTerminalState(
                    new StateId(prd.getSort() + "-S-" + getUid()),
                    nt, grammar.get(srt.getName()), false);
            previous.next.add(nts);
            previous = nts;
            if (prd.containsAttribute("klabel")) {
                RuleState rs1 = new RuleState(new StateId("AddLabelRS-" + getUid()), nt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
                previous.next.add(rs1);
                previous = rs1;
            }
        } else if (prd.isLexical()) {
            Lexical lx = (Lexical) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()),
                    nt, Pattern.compile(lx.getLexicalRule()), prd.getSort());
            previous.next.add(pstate);
            previous = pstate;
        } else if (prd.isConstant()) {
            Terminal terminal = (Terminal) prd.getItems().get(0);
            PrimitiveState pstate = new RegExState(
                    new StateId(prd.getSort() + "-T-" + getUid()), nt,
                    // TODO: if there is a \\E in the input string, this next line will fail
                    // should double escape \ if there is an odd number
                    Pattern.compile("\\Q" + terminal.getTerminal() + "\\E"), prd.getSort());
            previous.next.add(pstate);
            previous = pstate;
        } else {
            // just a normal production with Terminals and Sort alternations
            for (ProductionItem prdItem : prd.getItems()) {
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    PrimitiveState pstate = new RegExState(
                            new StateId(prd.getSort() + "-T-" + getUid()), nt,
                            // TODO: if there is a \\E in the input string, this next line will fail
                            // should double escape \ if there is an odd number
                            Pattern.compile("\\Q" + terminal.getTerminal() + "\\E"), TreeCleanerVisitor.DELETESORT);
                    previous.next.add(pstate);
                    RuleState rs1 = new RuleState(new StateId("DelTerminalRS-" + getUid()), nt, new DeleteRule(1, true));
                    pstate.next.add(rs1);
                    previous = rs1;
                } else if (prdItem instanceof Sort) {
                    Sort srt = (Sort) prdItem;
                    NonTerminalState nts = new NonTerminalState(
                            new StateId(prd.getSort() + "-S-" + getUid()),
                            nt, grammar.get(srt.getName()), false);
                    previous.next.add(nts);
                    previous = nts;
                } else {
                    assert false : "Didn't expect this ProductionItem type here: " + prdItem.getClass().getName();
                }
            }
            RuleState rs1 = new RuleState(new StateId("AddLabelRS-" + getUid()), nt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
            previous.next.add(rs1);
            previous = rs1;
        }
        previous.next.add(nt.exitState);
    }

    // label for '.Ids (list terminator)
    private NonTerminal getListTerminatorNT(String sort) {
        NonTerminal nt = new NonTerminal(new NonTerminalId(sort + "-special"));
        RuleState rs1 = new RuleState(new StateId("AddLabelRS-" + getUid()), nt, new WrapLabelRule(new KLabelConstant("'." + sort), sort));
        nt.entryState.next.add(rs1);
        rs1.next.add(nt.exitState);
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
