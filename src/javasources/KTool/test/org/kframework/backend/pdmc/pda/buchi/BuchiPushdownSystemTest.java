package org.kframework.backend.pdmc.pda.buchi;

import org.apache.commons.lang3.tuple.Pair;
import org.junit.Assert;
import org.junit.Test;

import org.kframework.backend.pdmc.pda.PushdownSystem;
import org.kframework.backend.pdmc.pda.buchi.PromelaBuchi;
import org.kframework.backend.pdmc.pda.buchi.parser.PromelaBuchiParser;
import org.kframework.backend.pdmc.pda.graph.TarjanSCC;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;

import java.io.ByteArrayInputStream;


/**
 * Created by Traian on 04.02.2014.
 */
public class BuchiPushdownSystemTest {
    @Test
    public void testProduct() throws Exception {
        String promelaString = "" +
            "never { /* ! (px0 \\/ px1) */\n" +
            "T0_init:\n"                  +
            "\tif\n" +
                "\t:: (1) -> goto T0_init"                           +
            "\t:: (!px0 && !px1) -> goto accept_all\n" +
            "\tfi;\n" +
            "accept_all:\n" +
            "\tskip\n" +
            "}\n";

        PromelaBuchi automaton = PromelaBuchiParser.parse(new ByteArrayInputStream(promelaString.getBytes("UTF-8")));

        PushdownSystem<String,String> pds = PushdownSystem.of(""+
                "<x0, p> => <x0>;\n" +
                "<x0, p> => <x1, p p>;\n" +
                "<x1, p> => <x1, p p>;\n" +
                "<x1, p> => <x0>;\n" +
                "<x0, p>");

        ConcreteEvaluator<String,String> evaluator = ConcreteEvaluator.of(""
                + "<x0, p> |= px0;\n"
                +  "<x1, p> |= px1;");

        BuchiPushdownSystem<String, String> bps = new BuchiPushdownSystem<>(pds, automaton, evaluator);
        System.err.print(bps.toString());

        BuchiPushdownSystemTools<String, String> bpsTool = new BuchiPushdownSystemTools<>(bps);
        System.err.println("\n------------------------");

        PAutomaton<PAutomatonState<Pair<String, BuchiState>, String>,BuchiPushdownSystemTools.LabelledAlphabet<String,String>> post = bpsTool.getPostStar();
        System.err.println("\n------------------------");
        System.err.println(post.toString());
    }

    @Test
         public void testProduct1() throws Exception {
        String promelaString = "" +
                "never { /* ! [](px1 -> <> px0) */\n" +
                "T0_init:\n" +
                "\tif\n" +
                "\t:: (1) -> goto T0_init\n" +
                "\t:: (!px0 && px1) -> goto accept_S2\n" +
                "\tfi;\n" +
                "accept_S2:\n" +
                "\tif\n" +
                "\t:: (!px0) -> goto accept_S2\n" +
                "\tfi;\n" +
                "T1_all:\n" +
                "\tskip\n" +
                "}\n";

        PromelaBuchi automaton = PromelaBuchiParser.parse(new ByteArrayInputStream(promelaString.getBytes("UTF-8")));

        PushdownSystem<String,String> pds = PushdownSystem.of(""+
                "<x0, p> => <x0>;\n" +
                "<x0, p> => <x1, p p>;\n" +
                "<x1, p> => <x1, p p>;\n" +
                "<x1, p> => <x0>;\n" +
                "<x0, p>");

        ConcreteEvaluator<String,String> evaluator = ConcreteEvaluator.of(""
                + "<x0, p> |= px0;\n"
                +  "<x1, p> |= px1;");

        BuchiPushdownSystem<String, String> bps = new BuchiPushdownSystem<>(pds, automaton, evaluator);
        System.err.println("\n----Buchi Pushdown System---");
        System.err.print(bps.toString());

        BuchiPushdownSystemTools<String, String> bpsTool = new BuchiPushdownSystemTools<>(bps);


        PAutomaton<PAutomatonState<Pair<String, BuchiState>, String>,BuchiPushdownSystemTools.LabelledAlphabet<String,String>> post = bpsTool.getPostStar();
        System.err.println("\n\n\n----Post Automaton----");
        System.err.println(post.toString());

        TarjanSCC repeatedHeads = bpsTool.getRepeatedHeadsGraph();
        System.err.println("\n\n\n----Repeated Heads----");
        System.err.println(repeatedHeads.toString());

        System.err.println("\n\n\n----Strongly Connected Components----");
        System.err.println(repeatedHeads.getSCCSString());
    }

    @Test
    public void testMarcelloTrue() throws Exception {
        String promelaString = "" +
                "never { /* ! [](px1 -> X (px1 \\/ px2)) */\n" +
                "T0_init:\n" +
                "\tif\n" +
                "\t:: (1) -> goto T0_init\n" +
                "\t:: (px1) -> goto accept_S2\n" +
                "\tfi;\n" +
                "accept_S2:\n" +
                "\tif\n" +
                "\t:: (!px1 && !px2) -> goto accept_all\n" +
                "\tfi;\n" +
                "accept_all:\n" +
                "\tskip\n" +
                "}\n";


        PromelaBuchi automaton = PromelaBuchiParser.parse(new ByteArrayInputStream(promelaString.getBytes("UTF-8")));

        PushdownSystem<String,String> pds = PushdownSystem.of(""+
                "<x0, p>     => <x0, skip ret>;\n" +
                "<x0, p>     => <x01, incx ret>;\n" +
                "<x01, incx> => <x0, p incx>;\n" +
                "<x0, skip>  => <x0>;\n" +
                "<x0, incx>  => <x1>;\n" +
                "<x1, incx>  => <x2>;\n" +
                "<x2, incx>  => <x0>;\n" +
                "<x0, ret>   => <x0>;\n" +
                "<x1, ret>   => <x1>;\n" +
                "<x2, ret>   => <x2>;\n" +
                "<x0, p>");

        String[] states = new String[] {"x0", "x01", "x1", "x2"};
        String[] heads = new String[] {"p", "incx", "skip", "ret"};
        String evalString = "";
        for (int s = 0; s < states.length; s++)
            for (int h = 0; h < heads.length; h++) {
                evalString += "<" + states[s] + ", " + heads[h] +
                        "> |= p";
                if (s != 1) evalString += states[s];
                else evalString += "x0";
                evalString += ";\n";
            }
        System.err.println(evalString);
        ConcreteEvaluator<String,String> evaluator
                = ConcreteEvaluator.of(evalString);

        BuchiPushdownSystem<String, String> bps = new BuchiPushdownSystem<>(pds, automaton, evaluator);
        System.err.println("\n----Buchi Pushdown System---");
        System.err.print(bps.toString());

        BuchiPushdownSystemTools<String, String> bpsTool = new BuchiPushdownSystemTools<>(bps);


        PAutomaton<PAutomatonState<Pair<String, BuchiState>, String>,BuchiPushdownSystemTools.LabelledAlphabet<String,String>> post = bpsTool.getPostStar();
        System.err.println("\n\n\n----Post Automaton----");
        System.err.println(post.toString());

        TarjanSCC repeatedHeads = bpsTool.getRepeatedHeadsGraph();
        System.err.println("\n\n\n----Repeated Heads----");
        System.err.println(repeatedHeads.toString());

        System.err.println("\n\n\n----Strongly Connected Components----");
        System.err.println(repeatedHeads.getSCCSString());
    }

    @Test
    public void testMarcelloFalse() throws Exception {
        String promelaString = "never { /* ! [](px1 -> X px0) */\n" +
                "T0_init:\n" +
                " if\n" +
                " :: (1) -> goto T0_init\n" +
                " :: (px1) -> goto accept_S2\n" +
                " fi;\n" +
                "accept_S2:\n" +
                " if\n" +
                " :: (!px0) -> goto accept_all\n" +
                " fi;\n" +
                "accept_all:\n" +
                " skip\n" +
                "}";


        PromelaBuchi automaton = PromelaBuchiParser.parse(new ByteArrayInputStream(promelaString.getBytes("UTF-8")));

        PushdownSystem<String,String> pds = PushdownSystem.of(""+
                "<x0, p>     => <x0, skip ret>;\n" +
                "<x0, p>     => <x01, incx ret>;\n" +
                "<x01, incx> => <x0, p incx>;\n" +
                "<x0, skip>  => <x0>;\n" +
                "<x0, incx>  => <x1>;\n" +
                "<x1, incx>  => <x2>;\n" +
                "<x2, incx>  => <x0>;\n" +
                "<x0, ret>   => <x0>;\n" +
                "<x1, ret>   => <x1>;\n" +
                "<x2, ret>   => <x2>;\n" +
                "<x0, p>");

        String[] states = new String[] {"x0", "x01", "x1", "x2"};
        String[] heads = new String[] {"p", "incx", "skip", "ret"};
        String evalString = "";
        for (int s = 0; s < states.length; s++)
            for (int h = 0; h < heads.length; h++) {
                evalString += "<" + states[s] + ", " + heads[h] +
                        "> |= p";
                if (s != 1) evalString += states[s];
                else evalString += "x0";
                evalString += ";\n";
            }
        System.err.println(evalString);
        ConcreteEvaluator<String,String> evaluator
                = ConcreteEvaluator.of(evalString);

        BuchiPushdownSystem<String, String> bps = new BuchiPushdownSystem<>(pds, automaton, evaluator);
        System.err.println("\n----Buchi Pushdown System---");
        System.err.print(bps.toString());

        BuchiPushdownSystemTools<String, String> bpsTool = new BuchiPushdownSystemTools<>(bps);


        PAutomaton<PAutomatonState<Pair<String, BuchiState>, String>,BuchiPushdownSystemTools.LabelledAlphabet<String,String>> post = bpsTool.getPostStar();
        System.err.println("\n\n\n----Post Automaton----");
        System.err.println(post.toString());

        TarjanSCC repeatedHeads = bpsTool.getRepeatedHeadsGraph();
        System.err.println("\n\n\n----Repeated Heads----");
        System.err.println(repeatedHeads.toString());

        System.err.println("\n\n\n----Strongly Connected Components----");
        System.err.println(repeatedHeads.getSCCSString());
    }
}
