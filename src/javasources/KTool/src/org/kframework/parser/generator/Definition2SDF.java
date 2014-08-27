// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.Definition;
import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Restrictions;
import org.kframework.kil.NonTerminal;
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
                    String srt1 = ((UserList) p1.getItems().get(0)).getSort().getName();
                    String srt2 = ((UserList) p2.getItems().get(0)).getSort().getName();
                    if (psdfv.subsorts.contains(new Subsort(srt1, srt2)))
                        psdfv.subsorts.add(new Subsort(p1.getSort().getName(), p2.getSort().getName()));
                }

        sdf.append(psdfv.sdf);

        sdf.append("%% subsorts 1\n");
        sdf.append("context-free priorities\n{\n");
        // 1
        // print Sort -> K > A -> B > K -> Sort
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Subsort subs : psdfv.subsorts) {
            Sort s1 = Sort.of(subs.getSmallSort());
            Sort s2 = Sort.of(subs.getBigSort());
            if (!s1.isBaseSort() && !s2.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s1.getName()) + " -> " + StringUtil.escapeSortName(s2.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s2) + "12" + StringUtil.escapeSortName(s1) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
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
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSortName(s.getName()) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSortName(s.getName()) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSortName(s.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n\n");

        sdf.append("%% subsorts 2\n");
        // print K -> Sort > Sort -> K
        sdf.append("context-free priorities\n{\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSortName(s.getName()));
                // sdf.append(" {cons(\"" + StringUtil.escapeSortName(s.getName()) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
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
                sdf.append("    " + StringUtil.escapeSortName(si.getSort().getName()) + " " + StringUtil.enquoteCString(si.getSeparator()) + " " + StringUtil.escapeSortName(p.getSort().getName()) + " -> "
                        + StringUtil.escapeSortName(p.getSort().getName()));
                sdf.append(" {cons(\"" + context.getConses().inverse().get(p) + "\")}\n");
                sdf.append("    \"." + p.getSort() + "\" -> " + StringUtil.escapeSortName(p.getSort().getName()));
                sdf.append(" {cons(\"" + StringUtil.escapeSortName(p.getSort().getName()) + "1Empty\")}\n");
            } else if (p.containsAttribute("bracket")) {
                // don't add bracket attributes added by the user
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
                sdf.append("-> " + StringUtil.escapeSortName(p.getSort().getName()));
                sdf.append(SDFHelper.getSDFAttributes(p, context.getConses()) + "\n");
            }
        }
        for (NonTerminal ss : psdfv.insertSorts)
            sdf.append("    " + StringUtil.escapeSortName(ss.getName()) + " -> InsertDz" + StringUtil.escapeSortName(ss.getName()) + "\n");

        sdf.append("\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("     K CastTypeDz \"" + s.getName() + "\"    -> VariableDz    {cons(\"" + StringUtil.escapeSortName(s.getName()) + "1Cast\")}\n");
                sdf.append("     K CastTypeDz \"" + s.getName() + "{\" TagListDz \"}\"    -> VariableDz    {cons(\"" + StringUtil.escapeSortName(s.getName()) + "1CastAttr\")}\n");
            }
        }
        sdf.append("     K CastTypeDz \"K\"        -> VariableDz    {cons(\"K1Cast\")}\n");
        sdf.append("     K CastTypeDz \"KItem\"    -> VariableDz    {cons(\"KItem1Cast\")}\n");
        sdf.append("     K CastTypeDz \"K{\" TagListDz \"}\"        -> VariableDz    {cons(\"K1CastAttr\")}\n");
        sdf.append("     K CastTypeDz \"KItem{\" TagListDz \"}\"    -> VariableDz    {cons(\"KItem1CastAttr\")}\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
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
            sdf.append("    " + p.getItems().get(0) + " -> Dz" + StringUtil.escapeSortName(p.getSort().getName()) + "\n");
        }

        sdf.append("\n\n%% sort predicates\n");
        // print is<Sort> predicates (actually KLabel)
        for (NonTerminal sort : psdfv.userSorts) {
            if (!sort.getSort().isKSort()) {
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

        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
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
            lexerSorts.add(p.getSort().getName());
            sdf.append("    " + l.getLexicalRule() + " -> " + StringUtil.escapeSortName(p.getSort().getName()) + "Dz\n");
            if (l.getFollow() != null && !l.getFollow().equals("")) {
                psdfv.restrictions.add(new Restrictions(new NonTerminal(p.getSort()), null, l.getFollow()));
            }

            if (!p.containsAttribute("noAutoReject")) {
                // reject all terminals that match the regular expression of the lexical production
                if (p.containsAttribute("regex")) {
                    Pattern pat = Pattern.compile(p.getAttribute("regex"));
                    for (Terminal t : terminals.terminals) {
                        Matcher m = pat.matcher(t.getTerminal());
                        if (m.matches())
                            sdf.append("    " + t.toString() + " -> " + StringUtil.escapeSortName(p.getSort().getName()) + "Dz {reject}\n");
                    }
                } else {
                    // if there is no regex attribute, then do it the old fashioned way, but way more inefficient
                    // add rejects for all possible combinations
                    for (Terminal t : terminals.terminals) {
                        sdf.append("    " + t.toString() + " -> " + StringUtil.escapeSortName(p.getSort().getName()) + "Dz {reject}\n");
                    }
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
                sdf.append("    " + StringUtil.enquoteCString(r.getTerminal().getTerminal()) + " -/- " + r.getPattern() + "\n");
            else
                sdf.append("    " + StringUtil.escapeSortName(r.getSort().getName()) + " -/- " + r.getPattern() + "\n");
        }

        return sdf;
    }
}
