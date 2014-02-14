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

        PAutomaton<PAutomatonState<Pair<String,BuchiState>,String>, Pair<String, Boolean>> post = bpsTool.getPostStar();
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


        PAutomaton<PAutomatonState<Pair<String,BuchiState>,String>, Pair<String, Boolean>> post = bpsTool.getPostStar();
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


        PAutomaton<PAutomatonState<Pair<String,BuchiState>,String>, Pair<String, Boolean>> post = bpsTool.getPostStar();
        System.err.println("\n\n\n----Post Automaton----");
        System.err.println(post.toString());

        TarjanSCC repeatedHeads = bpsTool.getRepeatedHeadsGraph();
        System.err.println("\n\n\n----Repeated Heads----");
        System.err.println(repeatedHeads.toString());

        System.err.println("\n\n\n----Strongly Connected Components----");
        System.err.println(repeatedHeads.getSCCSString());
    }
}
