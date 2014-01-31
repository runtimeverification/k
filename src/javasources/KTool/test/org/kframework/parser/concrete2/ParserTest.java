package org.kframework.parser.concrete2;

import junit.framework.TestCase;

public class ParserTest extends TestCase {
    public void setUp() throws Exception {
        super.setUp();

    }

    public void testEmptyGrammar() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.State.OrderingInfo oinf2 = new Grammar.State.OrderingInfo(2);
        Grammar.State.OrderingInfo oinf3 = new Grammar.State.OrderingInfo(3);

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, oinf2, stiend, oinf3);

        nt1.entryState.next.add(nt1.exitState);

        ParseState ps = new ParseState("");
        Parser parser = new Parser(ps);
        parser.parse(nt1, 0);
    }

    public void testSingleToken() throws Exception {

    }

    public void testSequenceOfTokens() throws Exception {

    }

    public void testDisjunctionOfTokens() throws Exception {

    }

    public void testListOfTokens() throws Exception {

    }

    public void testNestedNonTerminals() throws Exception {

    }

    public void testArithmeticLanguage() throws Exception {

    }
}
