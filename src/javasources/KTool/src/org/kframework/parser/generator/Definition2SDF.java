// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.Subsort;
import org.kframework.utils.StringUtil;

public class Definition2SDF {

    public static StringBuilder getSdfForDefinition(Definition def, Context context) {

        StringBuilder sdf = new StringBuilder("module Integration\n\n");
        sdf.append("imports Common\n");
        sdf.append("imports KTechnique\n");
        sdf.append("imports KBuiltinsBasic\n\n");
        sdf.append("exports\n\n");
        sdf.append("context-free syntax\n");

        DefinitionSDFVisitor psdfv = new DefinitionSDFVisitor(true, context);
        CollectTerminalsVisitor terminals = new CollectTerminalsVisitor(context);
        psdfv.visitNode(def);
        terminals.visitNode(def);

        for (Production p1 : psdfv.listProds)
            for (Production p2 : psdfv.listProds)
                if (p1 != p2) {
                    String srt1 = ((UserList) p1.getItems().get(0)).getSort();
                    String srt2 = ((UserList) p2.getItems().get(0)).getSort();
                    if (psdfv.subsorts.contains(new Subsort(srt1, srt2)))
                        psdfv.subsorts.add(new Subsort(p1.getSort(), p2.getSort()));
                }

        sdf.append(psdfv.sdf);

        sdf.append("%% subsorts 1\n");
        sdf.append("context-free priorities\n{\n");
        // 1
        // print Sort -> K > A -> B > K -> Sort
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Subsort subs : psdfv.subsorts) {
            String s1 = subs.getSmallSort();
            String s2 = subs.getBigSort();
            if (!Sort.isBasesort(s1) && !Sort.isBasesort(s2)) {
                sdf.append("    " + StringUtil.escapeSortName(s1) + " -> " + StringUtil.escapeSortName(s2));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s2) + "12" + StringUtil.escapeSortName(s1) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSortName(s.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n\n");

        sdf.append("%% subsorts 1a\n");
        sdf.append("context-free priorities\n{\n");
        // 1
        // print Sort -> K > A -> B > K -> Sort
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSortName(s.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n\n");

        sdf.append("%% subsorts 2\n");
        // print K -> Sort > Sort -> K
        sdf.append("context-free priorities\n{\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSortName(s.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n");

        sdf.append("context-free syntax\n");

        for (Production p : psdfv.outsides) {
            if (p.isListDecl()) {
                UserList si = (UserList) p.getItems().get(0);
                sdf.append("    " + StringUtil.escapeSortName(si.getSort()) + " \"" + si.getSeparator() + "\" " + StringUtil.escapeSortName(p.getSort()) + " -> "
                        + StringUtil.escapeSortName(p.getSort()));
                sdf.append(" {cons(\"" + p.getAttribute("cons") + "\")}\n");
                sdf.append("    \"." + p.getSort() + "\" -> " + StringUtil.escapeSortName(p.getSort()));
                sdf.append(" {cons(\"" + StringUtil.escapeSortName(p.getSort()) + "1Empty\")}\n");
            } else if (p.containsAttribute("bracket")) {
                // don't add bracket attributes added by the user
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
                            psdfv.insertSorts.add(srt);
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
        for (Sort ss : psdfv.insertSorts)
            sdf.append("    " + StringUtil.escapeSortName(ss.getName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getName()) + "\n");

        sdf.append("\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("     K CastTypeDz \"" + s.getName() + "\"    -> " + StringUtil.escapeSortName(s.getName()) + "DzVar    {cons(\"" + StringUtil.escapeSortName(s.getName()) + "1Cast\")}\n");
            }
        }
        sdf.append("     K CastTypeDz \"K\"        -> VariableDz    {cons(\"K1Cast\")}\n");
        sdf.append("     K CastTypeDz \"KItem\"    -> VariableDz    {cons(\"KItem1Cast\")}\n");
        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("     " + StringUtil.escapeSortName(s.getName()) + "DzVar   -> " + StringUtil.escapeSortName(s.getName()) + "\n");
            }
        }

        sdf.append("\n");
        sdf.append("    VariableDz -> K\n");

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

        sdf.append("lexical syntax\n");
        for (Production p : psdfv.constants) {
            sdf.append("    " + p.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(p.getSort()) + "\n");
        }

        sdf.append("\n\n%% sort predicates\n");
        // print is<Sort> predicates (actually KLabel)
        for (Sort sort : psdfv.userSorts) {
            if (!MetaK.isKSort(sort.getName())) {
                sdf.append("    \"" + AddPredicates.syntaxPredicate(sort.getName()) + "\"      -> DzKLabel\n");
            }
            if (AddSymbolicK.allowKSymbolic(sort.getName())) {
                sdf.append("    \"" + AddPredicates.symbolicPredicate(sort.getName()) + "\"      -> DzKLabel\n");
                sdf.append("    \"" + AddSymbolicK.symbolicConstructor(sort.getName()) + "\"      -> DzKLabel\n");
            }
        }

        sdf.append("\n\n");

        sdf.append("\n%% terminals reject\n");
        sdf.append(SDFHelper.getFollowRestrictionsForTerminals(terminals.terminals));

        sdf.append("context-free restrictions\n");

        for (Sort s : psdfv.userSorts) {
            if (!s.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + "DzVar -/- [a-zA-Z0-9\\{]\n");
            }
        }
        sdf.append("    VariableDz -/- [a-zA-Z0-9\\{]\n");

        sdf.append("lexical restrictions\n");
        sdf.append("%% some restrictions to ensure greedy matching for user defined constants\n");
        //sdf.append("    DzDzInt -/- [0-9]\n");
        sdf.append("    \"is\" -/- [\\#A-Z]\n");
        sdf.append("\n");

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
                for (String t : terminals.terminals) {
                    Matcher m = pat.matcher(t);
                    if (m.matches())
                        sdf.append("    \"" + StringUtil.escape(t) + "\" -> " + StringUtil.escapeSortName(p.getSort()) + "Dz {reject}\n");
                }
            } else {
                // if there is no regex attribute, then do it the old fashioned way, but way more inefficient
                // add rejects for all possible combinations
                for (String t : terminals.terminals) {
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
