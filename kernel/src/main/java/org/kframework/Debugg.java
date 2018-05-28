// TODO - rewrite this with JsonWriter - https://javabeginners.de/Frameworks/Json/Json_schreiben.php
package org.kframework;

import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.KRun;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.unparser.OutputModes;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.function.Consumer;

public class Debugg {

    static Module module;
    static OutputModes output;
    static Consumer<byte[]> print;
    static ColorSetting colorize;
    static PrintWriter writer;

    static ArrayList<String> ruleProfs;
    static ArrayList<String> steps;
    static String cstep;
    private static String targetTerm;
    private static String initialTerm;
    private static String currentTerm; // saved to catch crashing terms
    private static String currentRule; // saved to catch crashing terms
    private static boolean crash;
    private static String exception;
    private static Module unparsingModule;
    private static boolean circWatcher;
    private static boolean specRule;


    private static HashMap<String, Boolean> ruleMap;
    private static HashMap<String, Boolean> nodeMap;
    private static HashMap<String, Boolean> normalNodes;

    private static Queue<String> tmpRules;

    public static void init(Module module, OutputModes output, Consumer<byte[]> print, ColorSetting colorize) {
        Debugg.module = module;
        Debugg.output = output;
        Debugg.print = print;
        Debugg.colorize = colorize;
        Debugg.crash = false;
        Debugg.circWatcher = false;
        Debugg.specRule = false;
        Debugg.ruleMap = new HashMap<>();
        ruleProfs = new ArrayList<>();
        Debugg.nodeMap = new HashMap<>();
        Debugg.normalNodes = new HashMap<>();
        Debugg.currentRule = "";
        Debugg.unparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();
    }

    public static void step(String s) {
        cstep = s;
  //      System.out.println("STEPP: "+s);
    }

   // public static String getJSON() {
   //     return "{\n" +
   //                 "term: \"" + xmlTerm +"\",\n" +
   //             "}\n";
   // }

/*    public static void print(K term) {
        xmlTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
//      Debugg.writer.println(s);
    }*/

    public static void setInitialTerm(K term, K constraint) {
        initialTerm = addNode(term, constraint);
        System.out.println("initt "+initialTerm);
    }

    public static void setTargetTerm(K term, K constraint) {
        targetTerm = addNode(term, constraint);
        System.out.println("targett "+targetTerm);
    }

    public static void setCurrentTerm(K term, K constraint, boolean normal) {
        // currentTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        currentTerm = addNode(term, constraint);

        if(!Debugg.normalNodes.containsKey(currentTerm)) {
            normalNodes.put(currentTerm, normal);
            if(normal) {
                System.out.println("normalnode " + currentTerm);
            }
        }
    }
    public static void setCurrentRule(String rule) {
        // currentTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        currentRule = rule;
    }

    public static void log(K term) {
        System.out.println(KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize));
    }

    public static void save() {
        StringBuilder rules = new StringBuilder();
        /*for (String key : Debugg.ruleMap.keySet()) {
            if(!rules.toString().equals("")) rules.append(",\n");
            rules.append("\"")
                    .append(key)
                    .append("\": \"")
                    .append(Debugg.ruleMap.get(key))
                    .append("\"");
        }*/
        /*StringBuilder nodes = new StringBuilder();
        for (String key : Debugg.nodeMap.keySet()) {
            if(!nodes.toString().equals("")) nodes.append(",\n");
            nodes.append("\"")
                    .append(key)
                    .append("\": ")
                    .append(Debugg.nodeMap.get(key));
        }*/
        String json = "{\n"
           // + "\"rules\": "  + "{\n" + rules + "\n},\n"
            //+ "\"nodes\": "  + "{\n" + nodes + "\n},\n"
            + "\"proofs\": [\n" + String.join(",\n", ruleProfs) + "\n]\n"
            + "}\n";
        //try {


            //DateFormat df = new SimpleDateFormat("yyyy_MM_dd_HH_mm");
            //Date today = Calendar.getInstance().getTime();
            //String reportDate = df.format(today);
            //Debugg.writer = new PrintWriter("steps/debug_" + reportDate + ".json");
            //Debugg.writer.println(json);
            //Debugg.writer.close();
        //} catch (FileNotFoundException e) {
        //    e.printStackTrace();
        //}
    }

    public static String addNode(K term, K constraint) {
        String t = KRun.getString(Debugg.unparsingModule, Debugg.output, Debugg.print, term, Debugg.colorize);
        String c = KRun.getString(Debugg.unparsingModule, Debugg.output, Debugg.print, constraint, Debugg.colorize);
        String node = "{\n"
                + "\"term\": \"" + t + "\",\n"
                + "\"constraint\": \"" + c + "\"\n"
                + "}\n";
        String node_key = Integer.toHexString(node.hashCode());
        if(!Debugg.nodeMap.containsKey(node_key)) {
            nodeMap.put(node_key, true);
            try {
                Debugg.writer = new PrintWriter("nodes/" + node_key + ".json");
                Debugg.writer.println(node);
                Debugg.writer.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
        }
        return node_key;
    }

    public static void addStep(K from, K to, K from_c, K to_c) {
        //.replaceAll("\n","\\\\n")
        /*String jsonStep = "{\n" +
                    "\"step\": \"" + cstep +"\",\n" +
                    "\"from\": \"" + addNode(from, from_c) +"\",\n" +
                    "\"to\": \""   + addNode(to, to_c) +"\"\n" +
                "}\n";

        steps.add(jsonStep);
        */
        String from_key = addNode(from, from_c);
        String to_key = addNode(to, to_c);
        System.out.println("step " + cstep + " " + from_key + " " + to_key);
    }

    public static void resetTmpRules() {
        tmpRules = new LinkedList<String>();
    }
    public static void pushTmpRule(String rule_key) {
        tmpRules.add(rule_key);
    }
    public static String getTmpRule() {
        return tmpRules.remove();
    }

    public static void addStepRule(K from, K to, K from_c, K to_c, String rule_key) {
        /*String jsonStep = "{\n" +
                "\"step\": \"" + cstep +"\",\n" +
                "\"from\": \"" + addNode(from, from_c) +"\",\n" +
                "\"to\": \""   + addNode(to, to_c) +"\",\n" +
                "\"rule\": \"" + rule_key + "\"\n" + //.replaceAll("\"","'").replaceAll("/\\\\","AND")
                "}";
        */
        String from_key = addNode(from, from_c);
        String to_key = addNode(to, to_c);
        System.out.println("rstep " + cstep+" "+ from_key +" "+ to_key +" "+ rule_key);
        //steps.add(jsonStep);
    }

    public static void addRule(String rule_key, String rule) {
        if(!Debugg.ruleMap.containsKey(rule_key)) {
            try {
                Debugg.writer = new PrintWriter("rules/" + rule_key + ".json");
                Debugg.writer.println(rule);
                Debugg.writer.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
            System.out.println("newrule " + rule_key);
            Debugg.ruleMap.put(rule_key, true);
        }
    }

    public static void setUpProveRule() {
        Debugg.steps = new ArrayList<String>();
    }


    public static void saveIntermediate() {
        //String steps = String.join(",\n", Debugg.steps);

        //String jsonRuleProve = "{\n" +
        //        "\"initialTerm\": \"" + initialTerm + "\",\n" +
        //        "\"targetTerm\": \""  + targetTerm  + "\",\n" +
        //        "\"steps\": [" + steps + "]\n" +
        //        "}\n";
        //ruleProfs.add(jsonRuleProve);
        //Debugg.save();
        //ruleProfs.remove(ruleProfs.size() - 1);
    }

    public static void endProveRule() {
        String steps = String.join(",\n", Debugg.steps);
        String crash = "";
        if(Debugg.crash) {
            System.out.println("crash " + currentTerm);
            //String crashTermString = KRun.getString(Debugg.module, Debugg.output, Debugg.print, Debugg.currentTerm, Debugg.colorize);
            crash = ",\"crash\": \"" + currentTerm +"\"\n" +
                    ",\"crash_rule\": \"" + currentRule.replaceAll("\"","'").replaceAll("/\\\\","AND") + "\"\n" +
                    ",\"exception\": \"" + Debugg.exception + "\"\n";
        }

        String jsonRuleProve = "{\n" +
                "\"initialTerm\": \"" + initialTerm + "\",\n" +
                "\"targetTerm\": \""  + targetTerm  + "\",\n" +
                "\"steps\": [" + steps + "]\n" +
                crash +
                "}\n";
        ruleProfs.add(jsonRuleProve);
    }

    public static void saveCrashTerm(Exception e) {
        Debugg.exception = e.toString().replaceAll("\n","\\\\n").replaceAll("\"","'");
        Debugg.crash = true;
    }

    public static void circProve(K left, K right) {
        String lhs = KRun.getString(Debugg.unparsingModule, Debugg.output, Debugg.print, left, Debugg.colorize);
        String rhs = KRun.getString(Debugg.unparsingModule, Debugg.output, Debugg.print, right, Debugg.colorize);
        if(Debugg.circWatcher && Debugg.specRule) {
            String circc = "{\n" +
                    "\"term\": \"" + Debugg.currentTerm + "\"," +
                    "\"lhs\":  \"" + lhs +"\"," +
                    "\"rhs\": \"" + rhs + "\""  +
                    "}";
            String circc_key = Integer.toHexString(circc.hashCode());

            try {
                Debugg.writer = new PrintWriter("circc/" + circc_key + ".json");
                Debugg.writer.println(circc);
                Debugg.writer.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
            System.out.println("circc " + circc_key);

        }
    }

    public static void setCircWatcher(boolean circ) {
        Debugg.circWatcher = circ;
    }

    public static void setSpecRule(boolean main) {
        Debugg.specRule = main;
    }

    public static void specialTerm(String kcontent) {
        if(kcontent.equals("#halt_EVM(.KList)")) {
            System.out.println("specialnode halt" + currentTerm);
        }
        if(kcontent.equals("#exception_EVM(.KList)")) {
            System.out.println("specialnode exception" + currentTerm);
        }
        if(kcontent.equals("#revert_EVM(.KList)")) {
            System.out.println("specialnode revert " + currentTerm);
        }
        if(kcontent.equals("#end_EVM(.KList)")) {
            System.out.println("specialnode end " + currentTerm);
        }
    }

    public static void branchingNode(K term, K constraint) {
        String node_key = addNode(term, constraint);
        System.out.println("specialnode branch " + node_key);
    }
}
