// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.kframework.backend.Backends;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.Definition;
import org.kframework.kil.Lexical;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
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
        for (Sort s : psdfv.startSorts) {
            if (!s.isBaseSort() && !context.isListSort(s)) {
                List<ProductionItem> pi = new ArrayList<>();
                pi.add(new NonTerminal(s));
                Production prod = new Production(new NonTerminal(Sort.K), pi);
                ks2gsf.visitNode(prod);
            }
        }

        // save the new parser info
        new File(context.kompiled, "pgm").mkdirs();
        BinaryLoader.instance().saveOrDie(context.kompiled.getPath()+ "/pgm/newParser.bin", ks2gsf.getGrammar());

        StringBuilder sdf = new StringBuilder();
        sdf.append("module Program\n\n");
        sdf.append("imports Common\n");
        sdf.append("imports KBuiltinsBasic\n");
        sdf.append("exports\n\n");
        sdf.append("context-free syntax\n");
        sdf.append(psdfv.sdf);

        sdf.append("context-free start-symbols\n");
        // sdf.append(StringUtil.escapeSort(context.startSymbolPgm) + "\n");
        for (Sort s : psdfv.startSorts) {
            if (!s.equals("Start"))
                sdf.append(StringUtil.escapeSort(s) + " ");
        }
        sdf.append("K\n");

        sdf.append("context-free syntax\n");

        for (Production p : psdfv.outsides) {
            if (p.isListDecl()) {
                UserList si = (UserList) p.getItems().get(0);
                sdf.append("    {" + StringUtil.escapeSort(si.getSort()) + " " + StringUtil.enquoteCString(si.getSeparator()) + "}" + si.getListType() + " -> " + StringUtil.escapeSort(p.getSort()));
                sdf.append(" {cons(\"" + context.getConses().inverse().get(p) + "\")}\n");
            } else {
                sdf.append("    ");
                List<ProductionItem> items = p.getItems();
                for (int i = 0; i < items.size(); i++) {
                    ProductionItem itm = items.get(i);
                    if (itm instanceof Terminal) {
                        Terminal t = (Terminal) itm;
                        sdf.append(t.toString() + " ");
                    } else if (itm instanceof NonTerminal) {
                        NonTerminal srt = (NonTerminal) itm;
                        // if we are on the first or last place and this sort is not a list, just print the sort
                        if (i == 0 || i == items.size() - 1) {
                            sdf.append(StringUtil.escapeSort(srt) + " ");
                        } else {
                            // if this sort should be inserted to avoid the priority filter, then add it to the list
                            psdfv.insertSorts.add(srt.getSort());
                            String tempstr = srt.toString();
                            if (tempstr.endsWith("CellSort") || tempstr.endsWith("CellFragment"))
                                tempstr = "Bag";
                            sdf.append("InsertDz" + StringUtil.escapeSort(tempstr) + " ");
                        }
                    }
                }
                sdf.append("-> " + StringUtil.escapeSort(p.getSort()));
                sdf.append(SDFHelper.getSDFAttributes(p, context.getConses()) + "\n");
            }
        }

        for (Sort ss : psdfv.insertSorts)
            sdf.append("    " + StringUtil.escapeSort(ss) + " -> InsertDz" + StringUtil.escapeSort(ss) + "\n");

        sdf.append("\n\n");
        for (Sort sort : psdfv.constantSorts) {
            String s = StringUtil.escapeSort(sort);
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
        for (Sort s : psdfv.startSorts) {
            if (!s.isBaseSort() && !context.isListSort(s))
                sdf.append("    " + StringUtil.escapeSort(s) + "        -> K\n");
        }

        //TODO(dwightguth): remove for modularization
        if (context.kompileOptions.backend.equals(Backends.SYMBOLIC)) {
            sdf.append("\ncontext-free syntax\n");
            sdf.append("    DzId    -> UnitDz\n");
            sdf.append("    DzBool    -> UnitDz\n");
            sdf.append("    DzInt    -> UnitDz\n");
            sdf.append("    DzFloat    -> UnitDz\n");
            sdf.append("    DzString-> UnitDz\n");
            for (Sort s : psdfv.startSorts) {
                if (!s.isBaseSort() && !context.isListSort(s))
                    if (AddSymbolicK.allowKSymbolic(s)) {
                        sdf.append("    \"" + AddSymbolicK.symbolicConstructor(s) + "\"    \"(\" UnitDz \")\"    -> ");
                        sdf.append(StringUtil.escapeSort(s) + "    {cons(\"" + StringUtil.escapeSort(s) + "1Symb\")}\n");
                    }
            }
        }

        sdf.append("lexical syntax\n");
        for (Production prd : psdfv.constants) {
            sdf.append("    " + prd.getItems().get(0) + " -> Dz" + StringUtil.escapeSort(prd.getSort()) + "\n");
        }

        sdf.append("\n\n");

        for (Terminal t : ctv.terminals) {
            if (t.getTerminal().matches("[a-zA-Z\\_][a-zA-Z0-9\\_]*")) {
                sdf.append("    " + t.toString() + " -> IdDz {reject}\n");
            }
        }

        sdf.append("\n");
        sdf.append(SDFHelper.getFollowRestrictionsForTerminals(ctv.terminals));

        sdf.append("\n\n");

        // lexical rules
        sdf.append("lexical syntax\n");
        java.util.Set<Sort> lexerSorts = new HashSet<>();
        for (Production p : psdfv.lexical) {
            Lexical l = (Lexical) p.getItems().get(0);
            lexerSorts.add(p.getSort());
            sdf.append("    " + l.getLexicalRule() + " -> " + StringUtil.escapeSort(p.getSort()) + "Dz\n");
            if (l.getFollow() != null && !l.getFollow().equals("")) {
                psdfv.restrictions.add(new Restrictions(new NonTerminal(p.getSort()), null, l.getFollow()));
            }

            if (!p.containsAttribute("noAutoReject")) {
                // reject all terminals that match the regular expression of the lexical production
                if (p.containsAttribute("regex")) {
                    Pattern pat = Pattern.compile(p.getAttribute("regex"));
                    for (Terminal t : ctv.terminals) {
                        Matcher m = pat.matcher(t.getTerminal());
                        if (m.matches())
                            sdf.append("    " + t.toString() + " -> " + StringUtil.escapeSort(p.getSort()) + "Dz {reject}\n");
                    }
                } else {
                    // if there is no regex attribute, then do it the old fashioned way, but way more inefficient
                    // add rejects for all possible combinations
                    for (Terminal t : ctv.terminals) {
                        sdf.append("    " + t.toString() + " -> " + StringUtil.escapeSort(p.getSort()) + "Dz {reject}\n");
                    }
                }
            }
        }

        // adding cons over lexical rules
        sdf.append("context-free syntax\n");
        for (Sort s : lexerSorts) {
            sdf.append("    " + StringUtil.escapeSort(s) + "Dz -> " + StringUtil.escapeSort(s) + " {cons(\"" + StringUtil.escapeSort(s) + "1Const\")}\n");
        }
        sdf.append("\n\n");

        // follow restrictions
        sdf.append("context-free restrictions\n");
        for (Restrictions r : psdfv.restrictions) {
            if (r.getTerminal() != null && !r.getTerminal().getTerminal().equals(""))
                sdf.append("    " + StringUtil.enquoteCString(r.getTerminal().getTerminal()) + " -/- " + r.getPattern() + "\n");
            else
                sdf.append("    " + StringUtil.escapeSort(r.getNonTerminal()) + " -/- " + r.getPattern() + "\n");
        }

        return sdf;
    }
}
