package org.kframework.parser.concrete2;

import java.util.regex.Pattern;

import org.kframework.kil.Configuration;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSorts;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.RegExState;
import org.kframework.parser.concrete2.Grammar.RuleState;
import org.kframework.parser.concrete2.Rule.AddLocationRule;
import org.kframework.parser.concrete2.Rule.DeleteRule;
import org.kframework.parser.concrete2.Rule.WrapLabelRule;

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
            grammar.add(new NonTerminal(sort));
        }
    }

    private Grammar grammar = new Grammar();

    @Override
    public void visit(Production prd) {
        NonTerminal nt = grammar.get(prd.getSort());
        assert nt != null : "Could not find in the grammar the required sort: " + prd.getSort();
        NextableState previous = nt.entryState;
        if (prd.isListDecl()) {
            // ************************************** start of list creation **********************
            UserList ul = prd.getListDecl();
            /**
             * An empty list such as Ids ::= List{Id,","} is treated as if it would be written
             * as the following:
             *
             * Ids ::= IdsTerminator
             *       | NeIds
             * NeIds ::= Id IdsTerminator [klabel('_,_)]
             *         | Id "," NeIds     [klabel('_,_)]
             * IdsTerminator ::= ""       [klabel('.Ids)]
             *
             * However, it's implemented by directly generating the grammar because all the labels
             * must maintain the sort of the original production, therefore we create the
             * following graph:
             *
             * IdsTerminator:
             * (|-----<'.Ids>---<loc>---|)
             *
             * NeIds:
             * (|-----[Id]--+--(",")---<Del>---[NeIds]--+--<'_,_>---<loc>-|)
             *              |                           |
             *              +-----[IdsTerminator]-------+
             *
             * Ids:
             * (|--+-/-[IdsTerminator]-/-+--|) // optional line if the list type is *
             *     |                     |
             *     +-------[NeIds]-------+
             */

            // IdsTerminator
            NonTerminal IdsTerminatorNt = new NonTerminal(prd.getSort() + "-Terminator");
            {
                RuleState terminatorLabelRule = new RuleState("AddLabelRS", IdsTerminatorNt,
                    new WrapLabelRule(new KLabelConstant(ul.getTerminatorKLabel()), prd.getSort()));
                RuleState locRule = new RuleState(prd.getSort() + "-R", IdsTerminatorNt,
                    new AddLocationRule());

                IdsTerminatorNt.entryState.next.add(terminatorLabelRule);
                terminatorLabelRule.next.add(locRule);
                locRule.next.add(IdsTerminatorNt.exitState);
            }
            // NeIds
            String ntName = prd.getSort();
            NonTerminal NeIdsNt = new NonTerminal("Ne-" + ntName);
            {
                NonTerminalState IdState = new NonTerminalState(ntName + "-S", NeIdsNt,
                    grammar.get(ul.getSort()), false);
                PrimitiveState separatorState = new RegExState(ntName + "-T", NeIdsNt,
                    Pattern.compile(ul.getSeparator(), Pattern.LITERAL), KSorts.K);
                RuleState deleteToken = new RuleState(ntName + "-D", NeIdsNt,
                    new DeleteRule(1, true));
                NonTerminalState NeIdsState = new NonTerminalState(ntName + "-S", NeIdsNt,
                    NeIdsNt, false);
                RuleState labelState = new RuleState(ntName + "-L", NeIdsNt,
                    new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
                RuleState locRule = new RuleState(prd.getSort() + "-R", NeIdsNt,
                    new AddLocationRule());

                NeIdsNt.entryState.next.add(IdState);
                IdState.next.add(separatorState);
                separatorState.next.add(deleteToken);
                deleteToken.next.add(NeIdsState);
                NeIdsState.next.add(labelState);
                labelState.next.add(locRule);
                locRule.next.add(NeIdsNt.exitState);

                NonTerminalState IdsTerminatorState = new NonTerminalState(
                    prd.getSort() + "-S", NeIdsNt, IdsTerminatorNt, false);

                IdState.next.add(IdsTerminatorState);
                IdsTerminatorState.next.add(labelState);
            }
            // Ids
            NonTerminal IdsNt = nt;
            {
                if (ul.getListType().equals(UserList.ZERO_OR_MORE)) {
                    // create the branch which allows for empty lists
                    NonTerminalState special = new NonTerminalState(ntName + "-S", IdsNt,
                        IdsTerminatorNt, false);
                    previous.next.add(special);
                    special.next.add(IdsNt.exitState);
                }
                NonTerminalState NeIdsState = new NonTerminalState(ntName + "-S", IdsNt,
                    NeIdsNt, false);
                IdsNt.entryState.next.add(NeIdsState);
                // NeIdsState.next.add(IdsNt.exitState); // added at the end
                previous = NeIdsState;
            }
            // ************************************** end of list creation **********************
        } else if (prd.isSubsort()) {
            Sort srt = prd.getSubsort();
            NonTerminalState nts = new NonTerminalState(
                    prd.getSort() + "-S", nt, grammar.get(srt.getName()), false);
            previous.next.add(nts);
            previous = nts;
            // if the subsort has a klabel attached to it, then we must attach a label to it
            if (prd.containsAttribute("klabel")) {
                RuleState rs1 = new RuleState("AddLabelRS",
                    nt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
                previous.next.add(rs1);
                RuleState locRule = new RuleState(prd.getSort() + "-R", nt, new AddLocationRule());
                rs1.next.add(locRule);
                previous = locRule;
            }
        } else if (prd.isLexical()) {
            Lexical lx = prd.getLexical();
            String pattern = prd.containsAttribute(Constants.REGEX) ?
                                prd.getAttribute(Constants.REGEX) :
                                lx.getLexicalRule();
            PrimitiveState pstate = new RegExState(prd.getSort() + "-T",
                nt, Pattern.compile(pattern), prd.getSort());
            previous.next.add(pstate);
            RuleState locRule = new RuleState(prd.getSort() + "-R", nt, new AddLocationRule());
            pstate.next.add(locRule);
            previous = locRule;
        } else if (prd.isConstant()) {
            Terminal terminal = prd.getConstant();
            PrimitiveState pstate = new RegExState(
                prd.getSort() + "-T", nt,
                Pattern.compile(terminal.getTerminal(), Pattern.LITERAL), prd.getSort());
            previous.next.add(pstate);
            RuleState locRule = new RuleState(prd.getSort() + "-R", nt, new AddLocationRule());
            pstate.next.add(locRule);
            previous = locRule;
        } else {
            // just a normal production with Terminals and Sort alternations
            for (ProductionItem prdItem : prd.getItems()) {
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    PrimitiveState pstate = new RegExState(
                        prd.getSort() + "-T", nt,
                        Pattern.compile(terminal.getTerminal(), Pattern.LITERAL), KSorts.K);
                    previous.next.add(pstate);
                    RuleState rs1 = new RuleState("DelTerminalRS", nt, new DeleteRule(1, true));
                    pstate.next.add(rs1);
                    previous = rs1;
                } else if (prdItem instanceof Sort) {
                    Sort srt = (Sort) prdItem;
                    NonTerminalState nts = new NonTerminalState(
                        prd.getSort() + "-S", nt, grammar.get(srt.getName()), false);
                    previous.next.add(nts);
                    previous = nts;
                } else {
                    assert false : "Didn't expect this ProductionItem type: " + prdItem.getClass().getName();
                }
            }
            RuleState rs1 = new RuleState("AddLabelRS",
                nt, new WrapLabelRule(new KLabelConstant(prd.getKLabel()), prd.getSort()));
            previous.next.add(rs1);
            RuleState locRule = new RuleState(prd.getSort() + "-R", nt, new AddLocationRule());
            rs1.next.add(locRule);
            previous = locRule;
        }
        previous.next.add(nt.exitState);
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
        grammar.compile();
        return grammar;
    }
}
