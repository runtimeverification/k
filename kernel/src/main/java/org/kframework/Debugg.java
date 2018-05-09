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


    private static HashMap<String, Boolean> ruleMap;
    private static HashMap<String, Boolean> nodeMap;

    private static Queue<String> tmpRules;

    public static void init(Module module, OutputModes output, Consumer<byte[]> print, ColorSetting colorize) {
        Debugg.module = module;
        Debugg.output = output;
        Debugg.print = print;
        Debugg.colorize = colorize;
        Debugg.crash = false;
        Debugg.ruleMap = new HashMap<>();
        ruleProfs = new ArrayList<>();
        Debugg.nodeMap = new HashMap<>();
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
    }

    public static void setTargetTerm(K term, K constraint) {
        targetTerm = addNode(term, constraint);
    }

    public static void setCurrentTerm(K term, K constraint) {
        // currentTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        currentTerm = addNode(term, constraint);
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
        try {


            DateFormat df = new SimpleDateFormat("yyyy_MM_dd_HH_mm");
            Date today = Calendar.getInstance().getTime();
            String reportDate = df.format(today);
            Debugg.writer = new PrintWriter("steps/debug_" + reportDate + ".json");
            Debugg.writer.println(json);
            Debugg.writer.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
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
            try {
                Debugg.writer = new PrintWriter("nodes/" + node_key + ".json");
                Debugg.writer.println(node);
                Debugg.writer.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
        }
        nodeMap.put(node.hashCode() + "", true);
        return node_key;
    }

    public static void addStep(K from, K to, K from_c, K to_c) {
        //.replaceAll("\n","\\\\n")
        String jsonStep = "{\n" +
                    "\"step\": \"" + cstep +"\",\n" +
                    "\"from\": \"" + addNode(from, from_c) +"\",\n" +
                    "\"to\": \""   + addNode(to, to_c) +"\"\n" +
                "}\n";

        steps.add(jsonStep);

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
        String jsonStep = "{\n" +
                "\"step\": \"" + cstep +"\",\n" +
                "\"from\": \"" + addNode(from, from_c) +"\",\n" +
                "\"to\": \""   + addNode(to, to_c) +"\",\n" +
                "\"rule\": \"" + rule_key + "\"\n" + //.replaceAll("\"","'").replaceAll("/\\\\","AND")
                "}";

        steps.add(jsonStep);
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
        }
        Debugg.ruleMap.put(rule_key, true);
    }

    public static void setUpProveRule() {
        Debugg.steps = new ArrayList<String>();
    }


    public static void saveIntermediate() {
        String steps = String.join(",\n", Debugg.steps);

        String jsonRuleProve = "{\n" +
                "\"initialTerm\": \"" + initialTerm + "\",\n" +
                "\"targetTerm\": \""  + targetTerm  + "\",\n" +
                "\"steps\": [" + steps + "]\n" +
                "}\n";
        ruleProfs.add(jsonRuleProve);
        Debugg.save();
        ruleProfs.remove(ruleProfs.size() - 1);
    }

    public static void endProveRule() {
        String steps = String.join(",\n", Debugg.steps);
        String crash = "";
        if(Debugg.crash) {
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
}
