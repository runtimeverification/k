// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.Definition;
import org.kframework.kil.KSorts;
import org.kframework.kil.Lexical;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.parser.concrete2.KSyntax2GrammarStatesFilter;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.StringUtil;

/**
 * Collect the syntax module, call the syntax collector and print SDF for programs.
 */
public class ProgramSDF {

    public static StringBuilder getSdfForPrograms(Definition def, Context context) {

        // collect all the syntax modules
        CollectSynModulesVisitor csmv = new CollectSynModulesVisitor(context);
        csmv.visitNode(def);

        // collect the syntax from those modules
        ProgramSDFVisitor psdfv = new ProgramSDFVisitor(context);
        CollectTerminalsVisitor ctv = new CollectTerminalsVisitor(context);
        // visit all modules to collect all Terminals first
        for (String modName : csmv.synModNames) {
            Module m = def.getModulesMap().get(modName);
            ctv.visitNode(m);
        }
        KSyntax2GrammarStatesFilter ks2gsf = new KSyntax2GrammarStatesFilter(context, ctv);
        // generate SDF and states for the new parser, using the terminals collected from the
        // previous step
        for (String modName : csmv.synModNames) {
            Module m = def.getModulesMap().get(modName);
            psdfv.visitNode(m);
            ks2gsf.visitNode(m);
        }

        // for each start sort in the grammar
        // automatically add a production of the type K ::= <start-sort>
        // this will allow the parser to accept any sort as input if the definition doesn't contain
        // a configuration, or the $PGM variable has sort K
        for (String sort : psdfv.startSorts) {
            if (!Sort.isBasesort(sort) && !context.isListSort(sort)) {
                List<ProductionItem> pi = new ArrayList<>();
                pi.add(new Sort(sort));
                Production prod = new Production(new Sort(KSorts.K), pi);
                ks2gsf.visitNode(prod);
            }
        }

        // save the new parser info
        new File(context.kompiled, "pgm").mkdirs();
        BinaryLoader.save(context.kompiled.getPath()+ "/pgm/newParser.bin", ks2gsf.getGrammar());

        StringBuilder sdf = new StringBuilder();
        sdf.append("module Program\n\n");
        sdf.append("imports Common\n");
        sdf.append("imports KBuiltinsBasic\n");
        sdf.append("exports\n\n");
        sdf.append("context-free syntax\n");
        sdf.append(psdfv.sdf);

        sdf.append("context-free start-symbols\n");
        // sdf.append(StringUtil.escapeSortName(context.startSymbolPgm) + "\n");
        for (String s : psdfv.startSorts) {
            if (!s.equals("Start"))
                sdf.append(StringUtil.escapeSortName(s) + " ");
        }
        sdf.append("K\n");

        sdf.append("context-free syntax\n");

        for (Production p : psdfv.outsides) {
            if (p.isListDecl()) {
                UserList si = (UserList) p.getItems().get(0);
                sdf.append("    {" + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\"}" + si.getListType() + " -> " + StringUtil.escapeSortName(p.getSort()));
                sdf.append(" {cons(\"" + p.getAttribute("cons") + "\")}\n");
            } else {
                sdf.append("    ");
                List<ProductionItem> items = p.getItems();
                for (int i = 0; i < items.size(); i++) {
                    ProductionItem itm = items.get(i);
                    if (itm instanceof Terminal) {
                        Terminal t = (Terminal) itm;
                        sdf.append("\"" + StringUtil.escape(t.getTerminal()) + "\" ");
                    } else if (itm instanceof Sort) {
                        Sort srt = (Sort) itm;
                        // if we are on the first or last place and this sort is not a list, just print the sort
                        if (i == 0 || i == items.size() - 1) {
                            sdf.append(StringUtil.escapeSortName(srt.getName()) + " ");
                        } else {
                            // if this sort should be inserted to avoid the priority filter, then add it to the list
                            psdfv.insertSorts.add(srt.getName());
                            String tempstr = srt.getName();
                            if (tempstr.endsWith("CellSort") || tempstr.endsWith("CellFragment"))
                                tempstr = "Bag";
                            sdf.append("InsertDz" + StringUtil.escapeSortName(tempstr) + " ");
                        }
                    }
                }
                sdf.append("-> " + StringUtil.escapeSortName(p.getSort()));
                sdf.append(SDFHelper.getSDFAttributes(p.getAttributes()) + "\n");
            }
        }

        for (String ss : psdfv.insertSorts)
            sdf.append("    " + StringUtil.escapeSortName(ss) + " -> InsertDz" + StringUtil.escapeSortName(ss) + "\n");

        sdf.append("\n\n");
        for (String sort : psdfv.constantSorts) {
            String s = StringUtil.escapeSortName(sort);
            sdf.append("    Dz" + s + "        -> " + s + "    {cons(\"" + s + "1Const\")}\n");
        }

        sdf.append("\n");
        //sdf.append("    DzDzINT        -> DzDzInt\n");
        //sdf.append("    DzDzID        -> DzDzId\n");
        //sdf.append("    DzDzSTRING    -> DzDzString\n");
        //sdf.append("    DzDzFLOAT    -> DzDzFloat\n");
        sdf.append("\n");

        sdf.append("\n%% start symbols subsorts\n");
        sdf.append("    KItem        -> K\n");
        for (String s : psdfv.startSorts) {
            if (!Sort.isBasesort(s) && !context.isListSort(s))
                sdf.append("    " + StringUtil.escapeSortName(s) + "        -> K\n");
        }

        if (context.kompileOptions.backend == Backend.SYMBOLIC) {
            sdf.append("\ncontext-free syntax\n");
            sdf.append("    DzId    -> UnitDz\n");
            sdf.append("    DzBool    -> UnitDz\n");
            sdf.append("    DzInt    -> UnitDz\n");
            sdf.append("    DzFloat    -> UnitDz\n");
            sdf.append("    DzString-> UnitDz\n");
            for (String s : psdfv.startSorts) {
                if (!Sort.isBasesort(s) && !context.isListSort(s))
                    if (AddSymbolicK.allowKSymbolic(s)) {
                        sdf.append("    \"" + AddSymbolicK.symbolicConstructor(s) + "\"    \"(\" UnitDz \")\"    -> ");
                        sdf.append(StringUtil.escapeSortName(s) + "    {cons(\"" + StringUtil.escapeSortName(s) + "1Symb\")}\n");
                    }
            }
        }

        sdf.append("lexical syntax\n");
        for (Production prd : psdfv.constants) {
            sdf.append("    " + prd.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(prd.getSort()) + "\n");
        }

        sdf.append("\n\n");

        for (String t : ctv.terminals) {
            if (t.matches("[a-zA-Z\\_][a-zA-Z0-9\\_]*")) {
                sdf.append("    \"" + StringUtil.escape(t) + "\" -> IdDz {reject}\n");
            }
        }

        sdf.append("\n");
        sdf.append(SDFHelper.getFollowRestrictionsForTerminals(ctv.terminals));

        sdf.append("\n\n");

        // lexical rules
        sdf.append("lexical syntax\n");
        java.util.Set<String> lexerSorts = new HashSet<String>();
        for (Production p : psdfv.lexical) {
            Lexical l = (Lexical) p.getItems().get(0);
            lexerSorts.add(p.getSort());
            sdf.append("    " + l.getLexicalRule() + " -> " + StringUtil.escapeSortName(p.getSort()) + "Dz\n");
            if (l.getFollow() != null && !l.getFollow().equals("")) {
                psdfv.restrictions.add(new Restrictions(new Sort(p.getSort()), null, l.getFollow()));
            }

            // reject all terminals that match the regular expression of the lexical production
            if (p.containsAttribute("regex")) {
                Pattern pat = Pattern.compile(p.getAttribute("regex"));
                for (String t : ctv.terminals) {
                    Matcher m = pat.matcher(t);
                    if (m.matches())
                        sdf.append("    \"" + StringUtil.escape(t) + "\" -> " + StringUtil.escapeSortName(p.getSort()) + "Dz {reject}\n");
                }
            } else {
                // if there is no regex attribute, then do it the old fashioned way, but way more inefficient
                // add rejects for all possible combinations
                for (String t : ctv.terminals) {
                    sdf.append("    \"" + StringUtil.escape(t) + "\" -> " + StringUtil.escapeSortName(p.getSort()) + "Dz {reject}\n");
                }
            }
        }

        // adding cons over lexical rules
        sdf.append("context-free syntax\n");
        for (String s : lexerSorts) {
            sdf.append("    " + StringUtil.escapeSortName(s) + "Dz -> " + StringUtil.escapeSortName(s) + " {cons(\"" + StringUtil.escapeSortName(s) + "1Const\")}\n");
        }
        sdf.append("\n\n");

        // follow restrictions
        sdf.append("context-free restrictions\n");
        for (Restrictions r : psdfv.restrictions) {
            if (r.getTerminal() != null && !r.getTerminal().getTerminal().equals(""))
                sdf.append("    \"" + StringUtil.escape(r.getTerminal().getTerminal()) + "\" -/- " + r.getPattern() + "\n");
            else
                sdf.append("    " + StringUtil.escapeSortName(r.getSort().getName()) + " -/- " + r.getPattern() + "\n");
        }

        return sdf;
    }
}
