// Copyright (c) 2014-2015 K Team. All Rights Reserved.
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
        CollectTerminalsVisitor terminals = new CollectTerminalsVisitor();
        psdfv.visitNode(def);
        terminals.visitNode(def);

        for (Production p1 : psdfv.listProds)
            for (Production p2 : psdfv.listProds)
                if (p1 != p2) {
                    Sort srt1 = ((UserList) p1.getItems().get(0)).getSort();
                    Sort srt2 = ((UserList) p2.getItems().get(0)).getSort();
                    if (psdfv.subsorts.contains(new Subsort(srt1, srt2)))
                        psdfv.subsorts.add(new Subsort(p1.getSort(), p2.getSort()));
                }

        sdf.append(psdfv.sdf);

        sdf.append("%% subsorts 1\n");
        sdf.append("context-free priorities\n{\n");
        // 1
        // print Sort -> K > A -> B > K -> Sort
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSort(s) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSort(s) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (Subsort subs : psdfv.subsorts) {
            Sort s1 = subs.getSmallSort();
            Sort s2 = subs.getBigSort();
            if (!s1.isBaseSort() && !s2.isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSort(s1) + " -> " + StringUtil.escapeSort(s2));
                // sdf.append(" {cons(\"" + StringUtil.escapeSort(s2) + "12" + StringUtil.escapeSort(s1) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSort(s));
                // sdf.append(" {cons(\"" + StringUtil.escapeSort(s) + "12K\")}");
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
                sdf.append("    " + StringUtil.escapeSort(s) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSort(s) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSort(s));
                // sdf.append(" {cons(\"" + StringUtil.escapeSort(s) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n\n");

        sdf.append("%% subsorts 2\n");
        // print K -> Sort > Sort -> K
        sdf.append("context-free priorities\n{\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    K -> " + StringUtil.escapeSort(s));
                // sdf.append(" {cons(\"" + StringUtil.escapeSort(s) + "12K\")}");
                sdf.append("\n");
            }
        }
        sdf.append("} .> {\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSort(s) + " -> K");
                // sdf.append(" {cons(\"K12" + StringUtil.escapeSort(s) + "\")}");
                sdf.append("\n");
            }
        }
        sdf.append("}\n");

        sdf.append("context-free syntax\n");

        for (Production p : psdfv.outsides) {
            if (p.isListDecl()) {
                UserList si = (UserList) p.getItems().get(0);
                sdf.append("    " + StringUtil.escapeSort(si.getSort()) + " " + StringUtil.enquoteCString(si.getSeparator()) + " " + StringUtil.escapeSort(p.getSort()) + " -> "
                        + StringUtil.escapeSort(p.getSort()));
                sdf.append(" {cons(\"" + context.getConses().inverse().get(p) + "\")}\n");
                sdf.append("    \"." + p.getSort() + "\" -> " + StringUtil.escapeSort(p.getSort()));
                sdf.append(" {cons(\"" + StringUtil.escapeSort(p.getSort()) + "1Empty\")}\n");
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
                            sdf.append(StringUtil.escapeSort(srt) + " ");
                        } else {
                            // if this sort should be inserted to avoid the priority filter, then add it to the list
                            psdfv.insertSorts.add(srt);
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
        for (NonTerminal ss : psdfv.insertSorts)
            sdf.append("    " + StringUtil.escapeSort(ss) + " -> InsertDz" + StringUtil.escapeSort(ss) + "\n");

        sdf.append("\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("     K CastTypeDz \"" + s.toString() + "\"    -> VariableDz    {cons(\"" + StringUtil.escapeSort(s) + "1Cast\")}\n");
                sdf.append("     K CastTypeDz \"" + s.toString() + "{\" TagListDz \"}\"    -> VariableDz    {cons(\"" + StringUtil.escapeSort(s) + "1CastAttr\")}\n");
            }
        }
        sdf.append("     K CastTypeDz \"K\"        -> VariableDz    {cons(\"K1Cast\")}\n");
        sdf.append("     K CastTypeDz \"KItem\"    -> VariableDz    {cons(\"KItem1Cast\")}\n");
        sdf.append("     K CastTypeDz \"K{\" TagListDz \"}\"        -> VariableDz    {cons(\"K1CastAttr\")}\n");
        sdf.append("     K CastTypeDz \"KItem{\" TagListDz \"}\"    -> VariableDz    {cons(\"KItem1CastAttr\")}\n");
        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("     " + StringUtil.escapeSort(s) + "DzVar   -> " + StringUtil.escapeSort(s) + "\n");
            }
        }

        sdf.append("\n");
        sdf.append("    VariableDz -> K\n");

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

        sdf.append("lexical syntax\n");
        for (Production p : psdfv.constants) {
            sdf.append("    " + p.getItems().get(0) + " -> Dz" + StringUtil.escapeSort(p.getSort()) + "\n");
        }

        sdf.append("\n\n%% sort predicates\n");
        // print is<Sort> predicates (actually KLabel)
        for (NonTerminal sort : psdfv.userSorts) {
            if (!sort.getSort().isKSort()) {
                sdf.append("    \"" + AddPredicates.syntaxPredicate(sort.getSort()) + "\"      -> DzKLabel\n");
            }
            if (AddSymbolicK.allowKSymbolic(sort.getSort())) {
                sdf.append("    \"" + AddPredicates.symbolicPredicate(sort.getSort()) + "\"      -> DzKLabel\n");
                sdf.append("    \"" + AddSymbolicK.symbolicConstructor(sort.getSort()) + "\"      -> DzKLabel\n");
            }
        }

        sdf.append("\n\n");

        sdf.append("\n%% terminals reject\n");
        sdf.append(SDFHelper.getFollowRestrictionsForTerminals(terminals.terminals));

        sdf.append("context-free restrictions\n");

        for (NonTerminal s : psdfv.userSorts) {
            if (!s.getSort().isBaseSort()) {
                sdf.append("    " + StringUtil.escapeSort(s) + "DzVar -/- [a-zA-Z0-9\\{]\n");
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
                    for (Terminal t : terminals.terminals) {
                        Matcher m = pat.matcher(t.getTerminal());
                        if (m.matches())
                            sdf.append("    " + t.toString() + " -> " + StringUtil.escapeSort(p.getSort()) + "Dz {reject}\n");
                    }
                } else {
                    // if there is no regex attribute, then do it the old fashioned way, but way more inefficient
                    // add rejects for all possible combinations
                    for (Terminal t : terminals.terminals) {
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
