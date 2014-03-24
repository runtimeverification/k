package org.kframework.parser.concrete2;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.kil.*;

import java.lang.management.*;

import java.util.Arrays;
import java.util.regex.Pattern;

public class ParserTest {
    /* public static void main(String[] args) {
        try {
            System.in.read();
            new ParserTest().testListOfTokens();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    public void setUp() throws Exception {
        super.setUp();

    }*/

    @Test
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

        Assert.assertEquals("Empty Grammar check: ", expected, result);
        // the start and exit state of the NonTerminal
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }

    @Test
    public void testSingleToken() throws Exception {
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+"), null, KSorts.K);


        nt1.entryState.next.add(res);
        res.next.add(nt1.exitState);

        ParseState ps = new ParseState("asdfAAA1");
        Parser parser = new Parser(ps);

        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(klist(Token.kAppOf(KSorts.K, "asdfAAA1")))));
        Assert.assertEquals("Single Token check: ", expected, result);
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(nt1));
    }

    @Test
    public void testSequenceOfTokens() throws Exception {
        // A ::= #token{"[a-zA-Z0-9]+ +"} #token{"[a-zA-Z0-9]+"} [klabel(seq)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+ +"), null, KSorts.K);
        Grammar.RegExState res2 = new Grammar.RegExState(new Grammar.StateId("RegExStid2"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile("[a-zA-Z0-9]+"), label("seq"), KSorts.K);


        nt1.entryState.next.add(res1);
        res1.next.add(res2);
        res2.next.add(nt1.exitState);

        ParseState ps = new ParseState("asdfAAA1 adfsf");
        Parser parser = new Parser(ps);

        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(klist(kapp("seq", Token.kAppOf(KSorts.K, "asdfAAA1 "), Token.kAppOf(KSorts.K, "adfsf"))))));
        Assert.assertEquals("Single Token check: ", expected, result);
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(nt1));
    }

    @Test
    public void testDisjunctionOfTokens() throws Exception {
        // A ::= #token{"[a-z0-9]+"} [klabel(s1)]
        //     | #token{"[A-Z0-2]+"} #token{"[3-9]*"} [klabel(s3)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-z0-9]+"), label("s1"), KSorts.K);
        Grammar.RegExState res2 = new Grammar.RegExState(new Grammar.StateId("RegExStid2"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[A-Z0-2]+"), null, KSorts.K);
        Grammar.RegExState res3 = new Grammar.RegExState(new Grammar.StateId("RegExStid3"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile("[3-9]*"), label("s3"), KSorts.K);

        nt1.entryState.next.add(res1);
        nt1.entryState.next.add(res2);
        res1.next.add(nt1.exitState);
        res2.next.add(res3);
        res3.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("abc")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("s1", Token.kAppOf(KSorts.K, "abc"))))));
            Assert.assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("ABC")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("s3", Token.kAppOf(KSorts.K, "ABC"), Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("123")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("s1", Token.kAppOf(KSorts.K, "123"))), klist(kapp("s3", Token.kAppOf(KSorts.K, "12"), Token.kAppOf(KSorts.K, "3"))))));
            Assert.assertEquals("Single Token check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(nt1));
    }

    @Test
    public void testListOfTokens() throws Exception {
        // A ::= ("[a-zA-Z0-9]")* "" [klabel(seq)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]"), null, KSorts.K);
        Grammar.RegExState epsilonForLabel = new Grammar.RegExState(new Grammar.StateId("RegExEpsilon"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile(""), label("seq"), KSorts.K);

        nt1.entryState.next.add(res1);
        nt1.entryState.next.add(epsilonForLabel);
        res1.next.add(epsilonForLabel);
        res1.next.add(res1);
        epsilonForLabel.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("abc")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("seq", Token.kAppOf(KSorts.K, "a"), Token.kAppOf(KSorts.K, "b"), Token.kAppOf(KSorts.K, "c"), Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("Single Token check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("seq", Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("Single Token check: ", expected, result);
        }

        /*
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
        */
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }
    public static long getCpuTime( ) {
        ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
        return bean.isCurrentThreadCpuTimeSupported( ) ?
                bean.getCurrentThreadCpuTime( ) : 0L;
    }

    @Test
    public void testNestedNonTerminals1() throws Exception {
        // A ::= ""    [klabel(epsilon)]
        //     | x A y [klabel(xAy)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState resx = new Grammar.RegExState(new Grammar.StateId("RegExStidx"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("x"), null, KSorts.K);
        Grammar.RegExState resy = new Grammar.RegExState(new Grammar.StateId("RegExStidy"), nt1, new Grammar.State.OrderingInfo(3), Pattern.compile("y"), label("xAy"), KSorts.K);
        Grammar.RegExState epsilonForLabel = new Grammar.RegExState(new Grammar.StateId("RegExEpsilon"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile(""), label("epsilon"), KSorts.K);

        Grammar.NonTerminalState nts = new Grammar.NonTerminalState(new Grammar.StateId("NT"), nt1, new Grammar.State.OrderingInfo(2), nt1, false, null, KSorts.K);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(epsilonForLabel);
        epsilonForLabel.next.add(nt1.exitState);
        resx.next.add(nts);
        nts.next.add(resy);
        resy.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xxyy")).parse(nt1, 0);
            Term expected =
                amb(klist(amb(klist(kapp("xAy",
                    Token.kAppOf(KSorts.K, "x"),
                    amb(klist(kapp("xAy",
                        Token.kAppOf(KSorts.K, "x"),
                        amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, "")))),
                        Token.kAppOf(KSorts.K, "y")))),
                    Token.kAppOf(KSorts.K, "y"))))));
            Assert.assertEquals("x^ny^n check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }

    @Test
    public void testNestedNonTerminals2() throws Exception {
        // A ::= ""  [klabel(epsilon)]
        //     | A y [klabel(Ay)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState resy = new Grammar.RegExState(new Grammar.StateId("RegExStidy"), nt1, new Grammar.State.OrderingInfo(3), Pattern.compile("y"), label("Ay"), KSorts.K);
        Grammar.RegExState epsilonForLabel = new Grammar.RegExState(new Grammar.StateId("RegExEpsilon"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile(""), label("epsilon"), KSorts.K);

        Grammar.NonTerminalState nts = new Grammar.NonTerminalState(new Grammar.StateId("NT"), nt1, new Grammar.State.OrderingInfo(2), nt1, false, null, KSorts.K);

        nt1.entryState.next.add(nts);
        nt1.entryState.next.add(epsilonForLabel);
        epsilonForLabel.next.add(nt1.exitState);
        nts.next.add(resy);
        resy.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("yy")).parse(nt1, 0);
            Term expected =
                amb(klist(amb(klist(kapp("Ay",
                    amb(klist(kapp("Ay",
                        amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, "")))),
                        Token.kAppOf(KSorts.K, "y")))),
                    Token.kAppOf(KSorts.K, "y"))))));
            Assert.assertEquals("y^n check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }

    @Test
    public void testNestedNonTerminals3() throws Exception {
        // A ::= ""  [klabel(epsilon)]
        //     | x A [klabel(xA)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState resx = new Grammar.RegExState(new Grammar.StateId("RegExStidx"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("x"), null, KSorts.K);

        Grammar.NonTerminalState nts = new Grammar.NonTerminalState(new Grammar.StateId("NT"), nt1, new Grammar.State.OrderingInfo(2), nt1, false, label("xA"), KSorts.K);
        Grammar.RegExState epsilonForLabel = new Grammar.RegExState(new Grammar.StateId("RegExEpsilon"), nt1, new Grammar.State.OrderingInfo(2), Pattern.compile(""), label("epsilon"), KSorts.K);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(epsilonForLabel);
        epsilonForLabel.next.add(nt1.exitState);
        resx.next.add(nts);
        nts.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, ""))))));
            Assert.assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xx")).parse(nt1, 0);
            Term expected =
                amb(klist(amb(klist(kapp("xA",
                        Token.kAppOf(KSorts.K, "x"),
                        amb(klist(kapp("xA",
                                Token.kAppOf(KSorts.K, "x"),
                                amb(klist(kapp("epsilon", Token.kAppOf(KSorts.K, ""))))))))))));
            Assert.assertEquals("x^n check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }

    @Test
    public void testNestedNonTerminals4() throws Exception {
        // A ::= "x" [klabel(x)]
        //     | A A [klabel(AA)]
        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState resx = new Grammar.RegExState(new Grammar.StateId("RegExStidx"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("x"), label("x"), KSorts.K);

        Grammar.NonTerminalState nts1 = new Grammar.NonTerminalState(new Grammar.StateId("NT1"), nt1, new Grammar.State.OrderingInfo(2), nt1, false, null, KSorts.K);
        Grammar.NonTerminalState nts2 = new Grammar.NonTerminalState(new Grammar.StateId("NT2"), nt1, new Grammar.State.OrderingInfo(3), nt1, false, label("AA"), KSorts.K);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(nts1);

        resx.next.add(nt1.exitState);

        nts1.next.add(nts2);
        nts2.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("x")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("x", Token.kAppOf(KSorts.K, "x"))))));
            Assert.assertEquals("Single char check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xx")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("AA", amb(klist(kapp("x", Token.kAppOf(KSorts.K, "x")))), amb(klist(kapp("x", Token.kAppOf(KSorts.K, "x")))))))));
            Assert.assertEquals("AA check: ", expected, result);
        }
        Term X = kapp("x", Token.kAppOf(KSorts.K, "x"));
        {
            Term result = new Parser(new ParseState("xxx")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(kapp("AA", amb(klist(kapp("AA", amb(klist(X)), amb(klist(X))))), amb(klist(X)))),
                                          klist(kapp("AA", amb(klist(X)), amb(klist(kapp("AA", amb(klist(X)), amb(klist(X))))))))));
            Assert.assertEquals("AAA check: ", expected, result);
        }
        {
            Term result = new Parser(new ParseState("xxxx")).parse(nt1, 0);
            Term t1 = amb(klist(X));
            Term t2 = amb(klist(kapp("AA", t1, t1)));
            Term t3 = amb(klist(kapp("AA", t2, t1)), klist(kapp("AA", t1, t2)));
            Term t4 = amb(klist(kapp("AA", t1, t3)), klist(kapp("AA", t2, t2)), klist(kapp("AA", t3, t1)));
            Term expected = amb(klist(t4));
            Assert.assertEquals("AAA check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(nt1);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(nt1));
    }

    @Test
    public void testNestedNonTerminals5() throws Exception {
        // A1 ::= "x"  [klabel(x)]
        // A2 ::= A1   [klabel(n1)]
        // ....
        // An ::= An-1 [klabel(n[n-1])]
        // start symb is An
        Grammar.NonTerminalId baseCaseId = new Grammar.NonTerminalId("BaseCase");
        Grammar.StateId baseCaseEntry= new Grammar.StateId("BaseCaseEntry");
        Grammar.StateId baseCaseExit = new Grammar.StateId("BaseCaseExit");

        Grammar.NonTerminal baseCase = new Grammar.NonTerminal(baseCaseId, baseCaseEntry, new Grammar.State.OrderingInfo(-1),
                                                                      baseCaseExit,  new Grammar.State.OrderingInfo(1));
        Grammar.RegExState resx = new Grammar.RegExState(new Grammar.StateId("X"), baseCase, new Grammar.State.OrderingInfo(0), Pattern.compile("x"), label("x"), KSorts.K);

        baseCase.entryState.next.add(resx);
        resx.next.add(baseCase.exitState);

        Term expected = amb(klist(kapp("x", Token.kAppOf(KSorts.K, "x"))));

        for (int i = 2; i < 10; i++) {
            Grammar.NonTerminal nt = new Grammar.NonTerminal(new Grammar.NonTerminalId("NT"+i),
                    new Grammar.StateId("NT"+1+"Entry"), new Grammar.State.OrderingInfo(-i),
                    new Grammar.StateId("NT"+1+"Exit"), new Grammar.State.OrderingInfo(2*i-1));
            Grammar.NonTerminalState state = new Grammar.NonTerminalState(
                    new Grammar.StateId("S"+i), nt, new Grammar.State.OrderingInfo(2*i-2), baseCase, false, label("n" + i), KSorts.K);
            nt.entryState.next.add(state);
            state.next.add(nt.exitState);
            baseCase = nt;
            expected = amb(klist(kapp("n" + i, expected)));
        }

        {
            Term result = new Parser(new ParseState("x")).parse(baseCase, 0);
            expected = amb(klist(expected));
            Assert.assertEquals("Single char check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(baseCase);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(baseCase.entryState) && nc.isNullable(baseCase.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(baseCase));
    }

    @Test
    public void testNestedNonTerminals6() throws Exception {
        // A1 ::= ""  [klabel(x)]
        // A2 ::= A1   [klabel(n1)]
        // ....
        // An ::= An-1 [klabel(n[n-1])]
        // start symb is An

        Grammar.NonTerminalId baseCaseId = new Grammar.NonTerminalId("BaseCase");
        Grammar.StateId baseCaseEntry= new Grammar.StateId("BaseCaseEntry");
        Grammar.StateId baseCaseExit = new Grammar.StateId("BaseCaseExit");

        Grammar.NonTerminal baseCase = new Grammar.NonTerminal(baseCaseId, baseCaseEntry, new Grammar.State.OrderingInfo(-1),
                baseCaseExit,  new Grammar.State.OrderingInfo(1));
        Grammar.RegExState resx = new Grammar.RegExState(new Grammar.StateId("X"), baseCase, new Grammar.State.OrderingInfo(0), Pattern.compile(""), label("x"), KSorts.K);

        baseCase.entryState.next.add(resx);
        resx.next.add(baseCase.exitState);

        Term expected = amb(klist(kapp("x", Token.kAppOf(KSorts.K, ""))));

        for (int i = 2; i < 10; i++) {
            Grammar.NonTerminal nt = new Grammar.NonTerminal(new Grammar.NonTerminalId("NT"+i),
                    new Grammar.StateId("NT"+i+"Entry"), new Grammar.State.OrderingInfo(-i),
                    new Grammar.StateId("NT"+i+"Exit"), new Grammar.State.OrderingInfo(2*i-1));
            Grammar.NonTerminalState state = new Grammar.NonTerminalState(
                    new Grammar.StateId("S"+i), nt, new Grammar.State.OrderingInfo(2*i-2), baseCase, false, label("n" + i), KSorts.K);
            nt.entryState.next.add(state);
            state.next.add(nt.exitState);
            baseCase = nt;
            expected = amb(klist(kapp("n" + i, expected)));
        }

        {
            Term result = new Parser(new ParseState("")).parse(baseCase, 0);
            expected = amb(klist(expected));
            Assert.assertEquals("Single char check: ", expected, result);
        }
        Grammar grammar = new Grammar();
        grammar.add(baseCase);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(baseCase.entryState) && nc.isNullable(baseCase.exitState));
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(baseCase));
    }

    @Test
    public void testArithmeticLanguage() throws Exception {
        // Lit  ::= Token{[0-9]+}[klabel(lit)]
        // Term ::= "(" Exp ")"  [klabel(bracket)]
        //        | Term "*" Lit [klabel(mul)]
        //        | Lit
        // Exp  ::= Exp "+" Term [klabel(plus)]
        //        | Term
        Grammar.NonTerminal lit = new Grammar.NonTerminal(new Grammar.NonTerminalId("Lit"),
                new Grammar.StateId("LitEntry"), new Grammar.State.OrderingInfo(0),
                new Grammar.StateId("LitExit"), new Grammar.State.OrderingInfo(1));
        Grammar.NonTerminal trm = new Grammar.NonTerminal(new Grammar.NonTerminalId("Trm"),
                new Grammar.StateId("TrmEntry"), new Grammar.State.OrderingInfo(0),
                new Grammar.StateId("TrmExit"), new Grammar.State.OrderingInfo(3));
        Grammar.NonTerminal exp = new Grammar.NonTerminal(new Grammar.NonTerminalId("Exp"),
                new Grammar.StateId("ExpEntry"), new Grammar.State.OrderingInfo(0),
                new Grammar.StateId("ExpExit"), new Grammar.State.OrderingInfo(5));

        { // lit
            Grammar.RegExState litState = new Grammar.RegExState(new Grammar.StateId("LitState"), lit, new Grammar.State.OrderingInfo(0), Pattern.compile("[0-9]+"), label("lit"), KSorts.K);
            lit.entryState.next.add(litState);
            litState.next.add(lit.exitState);
        }

        { // trm
            Grammar.RegExState lparen = new Grammar.RegExState(new Grammar.StateId("LParen"), trm, new Grammar.State.OrderingInfo(0), Pattern.compile("\\("), null, KSorts.K);
            Grammar.RegExState rparen = new Grammar.RegExState(new Grammar.StateId("RParen"), trm, new Grammar.State.OrderingInfo(0), Pattern.compile("\\)"), label("bracket"), KSorts.K);
            Grammar.RegExState star = new Grammar.RegExState(new Grammar.StateId("Star"), trm, new Grammar.State.OrderingInfo(0), Pattern.compile("\\*"), null, KSorts.K);
            Grammar.NonTerminalState expState = new Grammar.NonTerminalState(new Grammar.StateId("Trm->Exp"), trm, new Grammar.State.OrderingInfo(6), exp, false, null, KSorts.K);
            Grammar.NonTerminalState trmState = new Grammar.NonTerminalState(new Grammar.StateId("Trm->Trm"), trm, new Grammar.State.OrderingInfo(4), trm, false, null, KSorts.K);
            Grammar.NonTerminalState lit1State = new Grammar.NonTerminalState(new Grammar.StateId("Trm->Lit1"), trm, new Grammar.State.OrderingInfo(2), lit, false, label("mul"), KSorts.K);
            Grammar.NonTerminalState lit2State = new Grammar.NonTerminalState(new Grammar.StateId("Trm->Lit2"), trm, new Grammar.State.OrderingInfo(2), lit, false, null, KSorts.K);

            trm.entryState.next.add(lparen);
            lparen.next.add(expState);
            expState.next.add(rparen);
            rparen.next.add(trm.exitState);

            trm.entryState.next.add(trmState);
            trmState.next.add(star);
            star.next.add(lit1State);
            lit1State.next.add(trm.exitState);

            trm.entryState.next.add(lit2State);
            lit2State.next.add(trm.exitState);
        }

        { // exp
            Grammar.RegExState plus = new Grammar.RegExState(new Grammar.StateId("Plus"), exp, new Grammar.State.OrderingInfo(0), Pattern.compile("\\+"), null, KSorts.K);
            Grammar.NonTerminalState expState = new Grammar.NonTerminalState(new Grammar.StateId("Exp->Exp"), exp, new Grammar.State.OrderingInfo(6), exp, false, null, KSorts.K);
            Grammar.NonTerminalState trm1State = new Grammar.NonTerminalState(new Grammar.StateId("Exp->Trm1"), exp, new Grammar.State.OrderingInfo(4), trm, false, label("plus"), KSorts.K);
            Grammar.NonTerminalState trm2State = new Grammar.NonTerminalState(new Grammar.StateId("Exp->Trm2"), exp, new Grammar.State.OrderingInfo(4), trm, false, null, KSorts.K);

            exp.entryState.next.add(expState);
            expState.next.add(plus);
            plus.next.add(trm1State);
            trm1State.next.add(exp.exitState);

            exp.entryState.next.add(trm2State);
            trm2State.next.add(exp.exitState);
        }

        {
            Term result = new Parser(new ParseState("1+2*3")).parse(exp, 0);
            Term expected = amb(klist(amb(klist(kapp("plus", amb(klist(amb(klist(amb(klist(kapp("lit", token("1")))))))),
                                                token("+"),
                                                amb(klist(kapp("mul", amb(klist(amb(klist(kapp("lit", token("2")))))),
                                                          token("*"),
                                                          amb(klist(kapp("lit", token("3"))))))))))));
            Assert.assertEquals("1+2*3: ", expected, result);
        }
        //Assert.assertEquals("Expected Nullable NTs", 9, Nullability.getReachableNullableStates(exp).size());
        Grammar grammar = new Grammar();
        grammar.add(exp);
        Nullability nc = new Nullability(grammar) ;
        Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(exp.entryState) && nc.isNullable(exp.exitState));
        Assert.assertEquals("Expected Nullable NTs", false, nc.isNullable(exp));

    }

    public static Ambiguity amb(Term ... terms) {
        return new Ambiguity(KSorts.K, Arrays.asList(terms));
    }

    public static KApp kapp(String label, Term ... terms) {
        return KApp.of(label(label), terms);
    }

    public static KList klist(Term ... terms) {
        return new KList(Arrays.asList(terms));
    }

    public static KApp token(String x) {
        return Token.kAppOf(KSorts.K, x);
    }

    public static KLabel label(String x) {
        return new KLabelConstant(x);
    }
}
