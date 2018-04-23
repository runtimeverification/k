package org.kframework;

import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.KRun;
import org.kframework.unparser.OutputModes;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
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
    private static K currentTerm; // saved to catch crashing terms
    private static K currentRule; // saved to catch crashing terms
    private static boolean crash;
    private static String exception;

    public static void init(Module module, OutputModes output, Consumer<byte[]> print, ColorSetting colorize) {
        Debugg.module = module;
        Debugg.output = output;
        Debugg.print = print;
        Debugg.colorize = colorize;
        Debugg.crash = false;
        ruleProfs = new ArrayList<>();
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

    public static void setInitialTerm(K term) {
        initialTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
    }

    public static void setTargetTerm(K term) {
        targetTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
    }

    public static void setCurrentTerm(K term) {
        // currentTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        currentTerm = term;
    }
    public static void setCurrentRule(K rule) {
        // currentTerm = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        currentRule = rule;
    }

    public static void log(K term) {
        System.out.println(KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize));
    }

    public static void close() {
        String json = "[" + String.join(",\n", ruleProfs) + "]";
        try {
            Debugg.writer = new PrintWriter("debug.json");
            Debugg.writer.println(json);
            Debugg.writer.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    public static void addStep(K term, K term1, String cconst) {
        String from = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        String to   = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term1, Debugg.colorize);

        String jsonStep = "{\n" +
                    "\"step\": \"" + cstep +"\",\n" +
                    "\"from\": \"" + from  +"\",\n" +
                    "\"from_constraint\": \"" + cconst.replaceAll("\n","\\\\n") + "\",\n" +
                    "\"to\": \""   + to    +"\"\n" +
                "}";

        steps.add(jsonStep);

    }

    public static void addStepRule(K term, K term1, String rule) {
        String from = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term, Debugg.colorize);
        String to   = KRun.getString(Debugg.module, Debugg.output, Debugg.print, term1, Debugg.colorize);

        String jsonStep = "{\n" +
                "\"step\": \"" + cstep +"\",\n" +
                "\"from\": \"" + from  +"\",\n" +
                "\"rule\": \"" + rule.replaceAll("\"","'").replaceAll("/\\\\","AND") + "\",\n" +
                "\"to\": \""   + to    +"\"\n" +
                "}";

        steps.add(jsonStep);
    }

    public static void setUpProveRule() {
        Debugg.steps = new ArrayList<String>();
    }

    public static void endProveRule() {
        String steps = String.join(",\n", Debugg.steps);
        String crash = "";
        if(Debugg.crash) {
            String crashTermString = KRun.getString(Debugg.module, Debugg.output, Debugg.print, Debugg.currentTerm, Debugg.colorize);
            crash = ",\"crash\": \"" + crashTermString +"\"\n" +
                    ",\"crash_rule\": \"" + currentRule.toString().replaceAll("\"","'").replaceAll("/\\\\","AND") + "\"\n" +
                    ",\"exception\": \"" + Debugg.exception + "\"";
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
