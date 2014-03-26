package org.kframework.parser.concrete2;

import junit.framework.TestCase;
import org.kframework.kil.*;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalId;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.RegExState;
import org.kframework.parser.concrete2.Grammar.State;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.StateId;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.Arrays;
import java.util.regex.Pattern;

public class ParserTest extends TestCase {
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

    public void testEmptyGrammar() throws Exception {
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        State.OrderingInfo oinf2 = new State.OrderingInfo(2);
        State.OrderingInfo oinf3 = new State.OrderingInfo(3);

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, oinf2, stiend, oinf3);

        nt1.entryState.next.add(nt1.exitState);

        ParseState ps = new ParseState("");
        Parser parser = new Parser(ps);
        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(KList.EMPTY)));

        assertEquals("Empty Grammar check: ", expected, result);
    }

    public void testSingleToken() throws Exception {
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState res = new RegExState(new StateId("RegExStid"), nt1, new State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+"));


        nt1.entryState.next.add(res);
        res.next.add(nt1.exitState);

        ParseState ps = new ParseState("asdfAAA1");
        Parser parser = new Parser(ps);

        Term result = parser.parse(nt1, 0);
        Term expected = amb(klist(amb(klist(Token.kAppOf("K", "asdfAAA1")))));
        assertEquals("Single Token check: ", expected, result);
    }

    public void testSequenceOfTokens() throws Exception {
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState res1 = new RegExState(new StateId("RegExStid"), nt1, new State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]+ +"));
        RegExState res2 = new RegExState(new StateId("RegExStid2"), nt1, new State.OrderingInfo(2), Pattern.compile("[a-zA-Z0-9]+"));


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
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState res1 = new RegExState(new StateId("RegExStid"), nt1, new State.OrderingInfo(1), Pattern.compile("[a-z0-9]+"));
        RegExState res2 = new RegExState(new StateId("RegExStid2"), nt1, new State.OrderingInfo(1), Pattern.compile("[A-Z0-2]+"));
        RegExState res3 = new RegExState(new StateId("RegExStid3"), nt1, new State.OrderingInfo(2), Pattern.compile("[3-9]*"));

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
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState res1 = new RegExState(new StateId("RegExStid"), nt1, new State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]"));

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
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState resx = new RegExState(new StateId("RegExStidx"), nt1, new State.OrderingInfo(1), Pattern.compile("x"));
        RegExState resy = new RegExState(new StateId("RegExStidy"), nt1, new State.OrderingInfo(3), Pattern.compile("y"));

        NonTerminalState nts = new NonTerminalState(new StateId("NT"), nt1, new State.OrderingInfo(2), nt1, false);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(nt1.exitState);
        resx.next.add(nts);
        nts.next.add(resy);
        resy.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(KList.EMPTY)));
            assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xxyy")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "x"), amb(klist(Token.kAppOf("K", "x"), amb(KList.EMPTY), Token.kAppOf("K", "y"))), Token.kAppOf("K", "y")))));
            assertEquals("x^ny^n check: ", expected, result);
        }
    }

    public void testNestedNonTerminals2() throws Exception {
        // A ::= ""
        //     | A y
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState resy = new RegExState(new StateId("RegExStidy"), nt1, new State.OrderingInfo(3), Pattern.compile("y"));

        NonTerminalState nts = new NonTerminalState(new StateId("NT"), nt1, new State.OrderingInfo(2), nt1, false);

        nt1.entryState.next.add(nts);
        nt1.entryState.next.add(nt1.exitState);
        nts.next.add(resy);
        resy.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(KList.EMPTY)));
            assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("yy")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(amb(klist(amb(KList.EMPTY), Token.kAppOf("K", "y"))), Token.kAppOf("K", "y")))));
            assertEquals("y^n check: ", expected, result);
        }
    }

    public void testNestedNonTerminals3() throws Exception {
        // A ::= ""
        //     | x A
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState resx = new RegExState(new StateId("RegExStidx"), nt1, new State.OrderingInfo(1), Pattern.compile("x"));

        NonTerminalState nts = new NonTerminalState(new StateId("NT"), nt1, new State.OrderingInfo(2), nt1, false);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(nt1.exitState);
        resx.next.add(nts);
        nts.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("")).parse(nt1, 0);
            Term expected = amb(klist(amb(KList.EMPTY)));
            assertEquals("EmtpyString check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xx")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "x"), amb(klist(Token.kAppOf("K", "x"), amb(KList.EMPTY)))))));
            assertEquals("x^n check: ", expected, result);
        }
    }

    public void testNestedNonTerminals4() throws Exception {
        // A ::= "x"
        //     | A A
        NonTerminalId ntistart = new NonTerminalId("StartNT");
        StateId stistart = new StateId("StartState");
        StateId stiend = new StateId("EndState");

        NonTerminal nt1 = new NonTerminal(ntistart, stistart, new State.OrderingInfo(0), stiend, new State.OrderingInfo(100));

        RegExState resx = new RegExState(new StateId("RegExStidx"), nt1, new State.OrderingInfo(1), Pattern.compile("x"));

        NonTerminalState nts1 = new NonTerminalState(new StateId("NT1"), nt1, new State.OrderingInfo(2), nt1, false);
        NonTerminalState nts2 = new NonTerminalState(new StateId("NT2"), nt1, new State.OrderingInfo(3), nt1, false);

        nt1.entryState.next.add(resx);
        nt1.entryState.next.add(nts1);

        resx.next.add(nt1.exitState);

        nts1.next.add(nts2);
        nts2.next.add(nt1.exitState);

        {
            Term result = new Parser(new ParseState("x")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(Token.kAppOf("K", "x")))));
            assertEquals("Single char check: ", expected, result);
        }

        {
            Term result = new Parser(new ParseState("xx")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(amb(klist(Token.kAppOf("K", "x"))), amb(klist(Token.kAppOf("K", "x")))))));
            assertEquals("AA check: ", expected, result);
        }
        Term X = Token.kAppOf("K", "x");
        {
            Term result = new Parser(new ParseState("xxx")).parse(nt1, 0);
            Term expected = amb(klist(amb(klist(amb(klist(amb(klist(X)), amb(klist(X)))), amb(klist(X))),
                                          klist(amb(klist(X)), amb(klist(amb(klist(X)), amb(klist(X))))))));
            assertEquals("AAA check: ", expected, result);
        }
        {
            Term result = new Parser(new ParseState("xxxx")).parse(nt1, 0);
            Term t1 = amb(klist(X));
            Term t2 = amb(klist(t1, t1));
            Term t3 = amb(klist(t2, t1), klist(t1, t2));
            Term t4 = amb(klist(t3, t1), klist(t2, t2), klist(t1, t3));
            Term expected = amb(klist(t4));
            assertEquals("AAA check: ", expected, result);
        }
    }

    public void testNestedNonTerminals5() throws Exception {

        NonTerminalId baseCaseId = new NonTerminalId("BaseCase");
        StateId baseCaseEntry= new StateId("BaseCaseEntry");
        StateId baseCaseExit = new StateId("BaseCaseExit");

        NonTerminal baseCase = new NonTerminal(baseCaseId, baseCaseEntry, new State.OrderingInfo(-1),
                                                                      baseCaseExit,  new State.OrderingInfo(1));
        RegExState resx = new RegExState(new StateId("X"), baseCase, new State.OrderingInfo(0), Pattern.compile("x"));

        baseCase.entryState.next.add(resx);
        resx.next.add(baseCase.exitState);

        Term expected = amb(klist(Token.kAppOf("K", "x")));

        for (int i = 2; i < 10; i++) {
            NonTerminal nt = new NonTerminal(new NonTerminalId("NT"+i),
                    new StateId("NT"+i+"Entry"), new State.OrderingInfo(-i),
                    new StateId("NT"+i+"Exit"), new State.OrderingInfo(2*i-1));
            NonTerminalState state = new NonTerminalState(
                    new StateId("S"+i), nt, new State.OrderingInfo(2*i-2), baseCase, false);
            nt.entryState.next.add(state);
            state.next.add(nt.exitState);
            baseCase = nt;
            expected = amb(klist(expected));
        }

        {
            Term result = new Parser(new ParseState("x")).parse(baseCase, 0);
            expected = amb(klist(expected));
            assertEquals("Single char check: ", expected, result);
        }
    }

    public void testArithmeticLanguage() throws Exception {
        NonTerminal lit = new NonTerminal(new NonTerminalId("Lit"),
                new StateId("LitEntry"), new State.OrderingInfo(0),
                new StateId("LitExit"), new State.OrderingInfo(1));
        NonTerminal trm = new NonTerminal(new NonTerminalId("Trm"),
                new StateId("TrmEntry"), new State.OrderingInfo(0),
                new StateId("TrmExit"), new State.OrderingInfo(3));
        NonTerminal exp = new NonTerminal(new NonTerminalId("Exp"),
                new StateId("ExpEntry"), new State.OrderingInfo(0),
                new StateId("ExpExit"), new State.OrderingInfo(5));

        { // lit
            RegExState litState = new RegExState(new StateId("LitState"), lit, new State.OrderingInfo(0), Pattern.compile("[0-9]+"));
            lit.entryState.next.add(litState);
            litState.next.add(lit.exitState);
        }

        { // trm
            RegExState lparen = new RegExState(new StateId("LParen"), trm, new State.OrderingInfo(0), Pattern.compile("\\("));
            RegExState rparen = new RegExState(new StateId("RParen"), trm, new State.OrderingInfo(0), Pattern.compile("\\)"));
            RegExState star = new RegExState(new StateId("Star"), trm, new State.OrderingInfo(0), Pattern.compile("\\*"));
            NonTerminalState expState = new NonTerminalState(new StateId("Trm->Exp"), trm, new State.OrderingInfo(6), exp, false);
            NonTerminalState trmState = new NonTerminalState(new StateId("Trm->Trm"), trm, new State.OrderingInfo(4), trm, false);
            NonTerminalState lit1State = new NonTerminalState(new StateId("Trm->Lit1"), trm, new State.OrderingInfo(2), lit, false);
            NonTerminalState lit2State = new NonTerminalState(new StateId("Trm->Lit2"), trm, new State.OrderingInfo(2), lit, false);

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
            RegExState plus = new RegExState(new StateId("Plus"), exp, new State.OrderingInfo(0), Pattern.compile("\\+"));
            NonTerminalState expState = new NonTerminalState(new StateId("Exp->Exp"), exp, new State.OrderingInfo(6), exp, false);
            NonTerminalState trm1State = new NonTerminalState(new StateId("Exp->Trm1"), exp, new State.OrderingInfo(4), trm, false);
            NonTerminalState trm2State = new NonTerminalState(new StateId("Exp->Trm2"), exp, new State.OrderingInfo(4), trm, false);

            exp.entryState.next.add(expState);
            expState.next.add(plus);
            plus.next.add(trm1State);
            trm1State.next.add(exp.exitState);

            exp.entryState.next.add(trm2State);
            trm2State.next.add(exp.exitState);
        }

        {
            Term result = new Parser(new ParseState("1+2*3")).parse(exp, 0);
            Term expected = amb(klist(amb(klist(amb(klist(amb(klist(amb(klist(token("1"))))))),
                                                token("+"),
                                                amb(klist(amb(klist(amb(klist(token("2"))))),
                                                          token("*"),
                                                          amb(klist(token("3")))))))));
            assertEquals("1+2*3: ", expected, result);
        }
    }

//    public void testPrecedence1() throws Exception {
//        NonTerminal e = new NonTerminal(new NonTerminalId("E"),
//            new StateId("E-entry"), new State.OrderingInfo(?),
//            new StateId("E-exit"), new State.OrderingInfo(?));
//        { // lit
//            NextableState var = new RegExState(new StateId("Var"), e, new State.OrderingInfo(?), Pattern.compile("[a-z]"));
//            NextableState varLabel = new WrapLabelRuleState(new StateId("VarLabel"), e, new State.OrderingInfo(?), new KLabelConstant("Var"));
//            e.entryState.next.add(var);
//            var.next.add(varLabel);
//            varLabel.next.add(e.exitState);
//        }
//
//        { // plus
//            NextableState e1 = new NonTerminalState(new StateId("Plus-e1"), e, new State.OrderingInfo(?), e, false);
//            NextableState plus = new RegExState(new StateId("Plus-token"), e, new State.OrderingInfo(?), Pattern.compile("\\+"));
//            NextableState e2 = new NonTerminalState(new StateId("Plus-e1"), e, new State.OrderingInfo(?), e, false);
//            NextableState plusLabel = new WrapLabelRuleState(new StateId("Plus-label"), e, new State.OrderingInfo(?), new KLabelConstant("_+_"));
//            e.entryState.next.add(e1);
//            e1.next.add(plus);
//            plus.next.add(e2);
//            e2.next.add(plusLabel);
//            plusLabel.next.add(e.exitState);
//        }
//
//        { // times
//            NextableState e1 = new NonTerminalState(new StateId("Times-e1"), e, new State.OrderingInfo(?), e, false);
//            NextableState times = new RegExState(new StateId("Times-token"), e, new State.OrderingInfo(?), Pattern.compile("\\*"));
//            NextableState e2 = new NonTerminalState(new StateId("Times-e1"), e, new State.OrderingInfo(?), e, false);
//            NextableState timesLabel = new RuleState(new StateId("Times-label"), e, new State.OrderingInfo(?), new WrapLabelRule(new KLabelConstant("_*_")));
//            e.entryState.next.add(e1);
//            e1.next.add(times);
//            times.next.add(e2);
//            e2.next.add(timesLabel);
//            timesLabel.next.add(e.exitState);
//        }
//
//        {
//            Term result = new Parser(new ParseState("x+y*z")).parse(e, 0);
//            /*Term expected = amb(klist(amb(klist(amb(klist(amb(klist(amb(klist(token("1"))))))),
//                token("+"),
//                amb(klist(amb(klist(amb(klist(token("2"))))),
//                    token("*"),
//                    amb(klist(token("3")))))))));*/
//            assertEquals("1+2*3: ", null, result);
//            // lookahead success
//            // lookahead failure
//            // require context
//            // reduce = Adopt
//            // insert
//            // delete = Done
//            // assoc
//            // prec
//            // prefer
//        }
//
//    }

    public static Ambiguity amb(Term ... terms) {
        return new Ambiguity("K", Arrays.asList(terms));
    }

    public static KList klist(Term ... terms) {
        return new KList(Arrays.asList(terms));
    }

    public static KApp token(String x) {
        return Token.kAppOf("K", x);
    }
}
