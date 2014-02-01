package org.kframework.parser.concrete2;

import junit.framework.TestCase;
import org.kframework.kil.*;
import org.kframework.utils.Stopwatch;
import java.lang.management.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.regex.Pattern;

public class ParserTest extends TestCase {
    public static void main(String[] args) {
        try {
            System.in.read();
            new ParserTest().testListOfTokens();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
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
        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(KList.EMPTY)));

        assertEquals("Empty Grammar check: ", expected, result);

    }

    public void testSingleToken() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+"));


        nt1.entryState.next.add(res);
        res.next.add(nt1.exitState);

        ParseState ps = new ParseState("asdfAAA1");
        Parser parser = new Parser(ps);

        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(klist(Token.kAppOf("K", "asdfAAA1")))));
        assertEquals("Single Token check: ", expected, result);
    }

    public void testSequenceOfTokens() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+ +"));
        Grammar.RegExState res2 = new Grammar.RegExState(new Grammar.StateId("RegExStid2"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile("[a-zA-Z0-9]+"));


        nt1.entryState.next.add(res1);
        res1.next.add(res2);
        res2.next.add(nt1.exitState);

        ParseState ps = new ParseState("asdfAAA1 adfsf");
        Parser parser = new Parser(ps);

        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(klist(Token.kAppOf("K", "asdfAAA1 "), Token.kAppOf("K", "adfsf")))));
        assertEquals("Single Token check: ", expected, result);
    }

    public void testDisjunctionOfTokens() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-z0-9]+"));
        Grammar.RegExState res2 = new Grammar.RegExState(new Grammar.StateId("RegExStid2"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[A-Z0-2]+"));
        Grammar.RegExState res3 = new Grammar.RegExState(new Grammar.StateId("RegExStid3"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile("[3-9]*"));

        nt1.entryState.next.add(res1);
        nt1.entryState.next.add(res2);
        res1.next.add(nt1.exitState);
        res2.next.add(res3);
        res3.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("abc")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "abc")))));
            assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("ABC")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "ABC"), Token.kAppOf("K", "")))));
            assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("123")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "123")), klist(Token.kAppOf("K", "12"), Token.kAppOf("K", "3")))));
            assertEquals("Single Token check: ", expected, result);
        }
    }

    public void testListOfTokens() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]"));

        nt1.entryState.next.add(res1);
        nt1.entryState.next.add(nt1.exitState);
        res1.next.add(nt1.exitState);
        res1.next.add(res1);

        {
            Term result = new Parser(new ParseState("abc")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "a"), Token.kAppOf("K", "b"), Token.kAppOf("K", "c")))));
            assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist())));
            assertEquals("Single Token check: ", expected, result);
        }

        {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < 100; i++) {
                sb.append('a');
            }
            for (int j = 0; j < 20; j++) {
                long start = getCpuTime();
                for (int i = 0; i < 100; i++) {
                    Term result = new Parser(new ParseState(sb.toString())).parse(nt1, 0);
                }
                long end = getCpuTime();
                System.out.println("Time: " + ((end - start) / 1000000.0));
            }
        }
    }
    public static long getCpuTime( ) {
        ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
        return bean.isCurrentThreadCpuTimeSupported( ) ?
                bean.getCurrentThreadCpuTime( ) : 0L;
    }
    public void testNestedNonTerminals1() throws Exception {
        // A ::= ""
        //     | x A y

    }

    public void testNestedNonTerminals2() throws Exception {

    }

    public void testNestedNonTerminals3() throws Exception {

    }

    public void testNestedNonTerminals4() throws Exception {

    }

    public void testNestedNonTerminals5() throws Exception {

    }

    public void testArithmeticLanguage() throws Exception {

    }

    public static Ambiguity amb(Term ... terms) {
        return new Ambiguity("K", Arrays.asList(terms));
    }

    public static KList klist(Term ... terms) {
        return new KList(Arrays.asList(terms));
    }
}
