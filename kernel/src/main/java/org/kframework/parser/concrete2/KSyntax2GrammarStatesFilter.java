// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.kframework.kil.Configuration;
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
import org.kframework.parser.generator.CollectTerminalsVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * A simple visitor that goes through every accessible production and creates the NFA states for the
 * parser. First step is to create a NonTerminal object for every declared syntactic sort. These
 * will be referenced each time a NonTerminalState is created.
 */
public class KSyntax2GrammarStatesFilter extends BasicVisitor {
    public KSyntax2GrammarStatesFilter(CollectTerminalsVisitor ctv, Set<Sort> declaredSorts, KExceptionManager kem) {
        super(KSyntax2GrammarStatesFilter.class.getName(), null);
        this.ctv = ctv;
        this.kem = kem;

        // create a NonTerminal for every declared sort
        for (Sort sort : declaredSorts) {
            grammar.add(new NonTerminal(sort.getName()));
        }
    }

    private Grammar grammar = new Grammar();
    private CollectTerminalsVisitor ctv;
    private final KExceptionManager kem;

    @Override
    public Void visit(Production prd, Void _void) {
        if (prd.containsAttribute("notInPrograms") || prd.containsAttribute("reject"))
            return null;
        NonTerminal nt = grammar.get(prd.getSort().getName());
        assert nt != null : "Could not find in the grammar the required sort: " + prd.getSort();
        NextableState previous = nt.entryState;
        // all types of production follow pretty much the same pattern
        // previous = entryState
        // loop: add a new State to the 'previous' state; update 'previous' state
        if (prd.isListDecl()) {
            if (true) { // circular DFA/associative lists (faster)
                UserList ul = prd.getListDecl();
                String ntName = prd.getSort().getName();
                /**
                 * It may be more efficient to make it this way.
                 *
                 * (|---+-------/------+--<'_,_>--<loc>--|)
                 *      |              |
                 *      |     +--------+
                 *      +---[E]---(",")--<Del>--+
                 *           ^------------------+
                 */
                RuleState labelState = new RuleState(ntName + "-L", nt, new WrapLabelRule(prd));
                NonTerminalState IdState = new NonTerminalState(ntName + "-S", nt, grammar.get(ul.getSort().getName()), false);
                PrimitiveState separatorState = new RegExState(ntName + "-T", nt, Pattern.compile(ul.getSeparator(), Pattern.LITERAL), null);
                RuleState deleteToken = new RuleState(ntName + "-D", nt, new DeleteRule(1, true));

                if (ul.getListType().equals(UserList.ZERO_OR_MORE)) {
                    // create the branch which allows for empty lists
                    nt.entryState.next.add(labelState);
                }

                nt.entryState.next.add(IdState);
                IdState.next.add(labelState);
                IdState.next.add(separatorState);
                separatorState.next.add(deleteToken);
                deleteToken.next.add(IdState);
                // NeIdsState.next.add(IdsNt.exitState); // added at the end
                previous = labelState;
            } else { // TODO: remove once the quadratic behaviors are sorted out
                // Using multiple non-terminals but slower. It also creates the correct ambiguities.
                // ************************************** start of list creation **********************
                UserList ul = prd.getListDecl();
                /**
                 * An empty list such as Ids ::= List{Id,","} is treated as if it would be written
                 * as the following:
                 *
                 * Ids ::= IdsTerminator
                 *       | NeIds
                 * NeIds ::= Id IdsTerminator [klabel('_,_void)]
                 *         | Id "," NeIds     [klabel('_,_void)]
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
                 * (|--+-/-[IdsTerminator]-/-+--|) // used only if the list type is *
                 *     |                     |
                 *     +-------[NeIds]-------+
                 */

                // IdsTerminator
                NonTerminal IdsTerminatorNt = new NonTerminal(prd.getSort() + "-Terminator");
                {
                    RuleState terminatorLabelRule = new RuleState("AddLabelRS", IdsTerminatorNt,
                            new WrapLabelRule(prd));
                    RuleState locRule = new RuleState(prd.getSort() + "-R", IdsTerminatorNt,
                            new AddLocationRule());

                    IdsTerminatorNt.entryState.next.add(terminatorLabelRule);
                    terminatorLabelRule.next.add(locRule);
                    locRule.next.add(IdsTerminatorNt.exitState);
                }
                // NeIds
                String ntName = prd.getSort().getName();
                NonTerminal NeIdsNt = new NonTerminal("Ne-" + ntName);
                {
                    NonTerminalState IdState = new NonTerminalState(ntName + "-S", NeIdsNt,
                            grammar.get(ul.getSort().getName()), false);
                    PrimitiveState separatorState = new RegExState(ntName + "-T", NeIdsNt,
                            Pattern.compile(ul.getSeparator(), Pattern.LITERAL), null);
                    RuleState deleteToken = new RuleState(ntName + "-D", NeIdsNt,
                            new DeleteRule(1, true));
                    NonTerminalState NeIdsState = new NonTerminalState(ntName + "-S", NeIdsNt,
                            NeIdsNt, false);
                    RuleState labelState = new RuleState(ntName + "-L", NeIdsNt,
                            new WrapLabelRule(prd));
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
            }
        } else if (prd.isLexical()) {
            // T ::= Token{regex}
            // these kind of productions create KApps which contain token elements
            Lexical lx = prd.getLexical();
            Pattern p;
            if (!prd.containsAttribute(Constants.REGEX)) {
                // try to use the regular expression from SDF.
                // If it's not compatible give a warning
                try {
                    p = Pattern.compile(lx.getLexicalRule());
                } catch (PatternSyntaxException ex) {
                    p = Pattern.compile("NoMatch");
                    String msg = "Lexical pattern not compatible with the new parser.";
                    kem.registerCompilerWarning(msg, ex, lx);
                }
            } else {
                p = Pattern.compile(prd.getAttribute(Constants.REGEX));
            }

            // check to see which terminals match the current regular expression and send it to
            // the PrimitiveState for rejection
            Set<String> rejects = new HashSet<>();
            if (!prd.containsAttribute("noAutoReject")) {
                for (Terminal keyword : ctv.terminals) {
                    Matcher m = p.matcher(keyword.getTerminal());
                    if (m.matches())
                        rejects.add(keyword.getTerminal());
                }
            }
            for (Production preject : ctv.rejects) {
                if (preject.getSort().equals(prd.getSort())) {
                    rejects.add(((Terminal) preject.getItems().get(0)).getTerminal());
                }
            }
            PrimitiveState pstate = new RegExState(prd.getSort().getName() + "-T",
                nt, p, prd, rejects);
            previous.next.add(pstate);
            previous = pstate;
        } else {
            // just a normal production with Terminals and Sort alternations
            // this will create a labeled KApp with the same arity as the production
            for (ProductionItem prdItem : prd.getItems()) {
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    PrimitiveState pstate = new RegExState(
                            prd.getSort() + "-T", nt,
                            Pattern.compile(terminal.getTerminal(), Pattern.LITERAL), null);
                    previous.next.add(pstate);
                    RuleState del = new RuleState("DelTerminalRS", nt, new DeleteRule(1, true));
                    pstate.next.add(del);
                    previous = del;
                } else if (prdItem instanceof org.kframework.kil.NonTerminal) {
                    org.kframework.kil.NonTerminal srt = (org.kframework.kil.NonTerminal) prdItem;
                    NonTerminalState nts = new NonTerminalState(
                            prd.getSort() + "-S", nt, grammar.get(srt.getName()), false);
                    previous.next.add(nts);
                    previous = nts;
                } else if (prdItem instanceof Lexical) {
                    Lexical lx = prd.getLexical();
                    Pattern p;
                    try {
                        p = Pattern.compile(lx.getLexicalRule());
                    } catch (PatternSyntaxException ex) {
                        p = Pattern.compile("NoMatch");
                        String msg = "Lexical pattern not compatible with the new parser.";
                        kem.registerCompilerWarning(msg, ex, lx);
                    }
                    PrimitiveState pstate = new RegExState(prd.getSort().getName() + "-T", nt, p, prd);
                    previous.next.add(pstate);
                    previous = pstate;
                } else {
                    assert false : "Didn't expect this ProductionItem type: " + prdItem.getClass().getName();
                }
            }
            RuleState labelRule = new RuleState("AddLabelRS",
                    nt, new WrapLabelRule(prd));
            previous.next.add(labelRule);
            previous = labelRule;
        }
        RuleState locRule = new RuleState(prd.getSort() + "-R", nt, new AddLocationRule());
        previous.next.add(locRule);
        previous = locRule;

        previous.next.add(nt.exitState);
        return null;
    }

    @Override
    public Void visit(Rule s, Void _void) {
        // skip visiting rules, contexts and configurations
        return null;
    }

    @Override
    public Void visit(Configuration s, Void _void) {
        // skip visiting rules, contexts and configurations
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context s, Void _void) {
        // skip visiting rules, contexts and configurations
        return null;
    }

    public Grammar getGrammar() {
        grammar.addWhiteSpace();
        grammar.compile();
        return grammar;
    }
}
