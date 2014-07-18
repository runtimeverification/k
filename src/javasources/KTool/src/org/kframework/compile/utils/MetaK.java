// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Collection;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.GenericToken;
import org.kframework.kil.Hole;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSort;
import org.kframework.kil.KSorts;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class MetaK {

    public static final String cellSort = "CellSort";
    public static final String cellFragment = "CellFragment";

    public static Term incrementCondition(Term condition, Term kresultCnd) {
        if (condition == null) {
            return kresultCnd;
        }
        return KApp.of(KLabelConstant.ANDBOOL_KLABEL, condition, kresultCnd);
    }

    public static boolean isCellSort(String bigSort) {
        return (bigSort.endsWith(cellSort)
                ||bigSort.endsWith(cellFragment));
    }

    public static boolean isCellFragment(String bigSort) {
        return (bigSort.endsWith(cellFragment));
    }

    public static String cellSort(String cellName) {
        return StringUtil.makeProper(cellName) + cellSort;
    }

    public static String cellFragment(String cellName) {
        return StringUtil.makeProper(cellName) + cellFragment;
    }

    public static String cellUnit(String cellName) {
        return "." + cellFragment(cellName);
    }

    public static class Constants {
        public static final String anyVarSymbol = "_";
        public static final String heatingTag = "heat";
        public static final String coolingTag = "cool";
        public static final String hole = "[]";
        @Deprecated
        public static final String freshCons = "Bool1FreshSyn";
        public static final String plusIntCons = "Int1PlusSyn";
        public static final String generatedTopCellLabel = "generatedTop";
        public static final String pathCondition = "path-condition";
        public static final String generatedCfgAbsTopCellLabel =
                "___CONTEXT_ABSTRACTION_TOP_CELL___";
    }

    public static Set<String> kModules = new HashSet<String>();
    static {
        kModules.add("K-BUILTINS");
        kModules.add("K-CONDITION-SEARCH");
        kModules.add("K-CONTEXTS");
        kModules.add("K-RULES");
        kModules.add("K-SENTENCE");
        kModules.add("K-STRICNESS");
        kModules.add("K-TECHNIQUE");
        kModules.add("K-WHERE");
        kModules.add("K-WRAPPERS-LABELS");
    };

    public static Set<Attribute> anywheres = new HashSet<Attribute>();
    static {
        anywheres.add(new Attribute("anywhere", ""));
        anywheres.add(new Attribute("macro", ""));
        anywheres.add(new Attribute("predicate", ""));
        anywheres.add(new Attribute("function", ""));
    }

    public static boolean isKModule(String key) {
        return kModules.contains(key);
    }

    public static boolean isBuiltinModule(String key) {
        return key.startsWith("#");
    }

    public static Configuration getConfiguration(Definition node, org.kframework.kil.loader.Context context) {
        final List<Configuration> result = new LinkedList<Configuration>();
        new BasicVisitor(context) {
            @Override
            public Void visit(Configuration node, Void _) {
                result.add(node);
                return null;
            }

            @Override
            public Void visit(org.kframework.kil.Context node, Void _) {
                return null;
            }

            @Override
            public Void visit(Rule node, Void _) {
                return null;
            }

            @Override
            public Void visit(Syntax node, Void _) {
                return null;
            }
        }.visitNode(node);
        if (result.size() == 0) {
            GlobalSettings.kem
                    .register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Internal compiler error --- Cannot find configuration.", node.getFilename(), node.getLocation()));
        }
        return result.get(0);
    }

    public static Term defaultTerm(Term v, org.kframework.kil.loader.Context context) {
        String sort = v.getSort();
        KSort ksort = KSort.getKSort(sort).mainSort();
        if (ksort.isDefaultable())
            return new ListTerminator(ksort.toString(), null);
        GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Don't know the default value for term " + v.toString() + ". Assuming .K", v.getFilename(), v
                .getLocation()));
        return KSequence.EMPTY;
    }

    /**
     * Checks if the specified sort has been defined in {@link KSort}.
     *
     * @param sort
     *            the specified sort
     * @return {@code true} if the specified sort has been defined in
     *         {@code KSort}; otherwise, false
     */
    public static boolean isKSort(String sort) {
        try {
            KSort.valueOf(sort);
        } catch (IllegalArgumentException e) {
            // TODO(YilongL): I think we can return false for sure, since we
            // have KList defined in KSort
//            return sort.equals(KSorts.KLIST);
            return false;
        }
        return true;
    }

    public static boolean isAnywhere(Rule r) {
        if (null == r.getAttributes())
            return false;
        for (Attribute any : anywheres) {
            if (any.getValue().equals(r.getAttribute(any.getKey())))
                return true;
        }
        return false;
    }

    public static Term kWrap(Term t, String komputationCellName) {
        return wrap(t, komputationCellName, Ellipses.RIGHT);
    }

    public static Term wrap(Term t, String label, Ellipses ellipses) {
        Cell cell = new Cell(t.getLocation(),t.getFilename());
        cell.setLabel(label);
        cell.setEllipses(ellipses);
        cell.setContents(t);
        return cell;
    }

    public static int countRewrites(Term t, org.kframework.kil.loader.Context context) {
        final List<Integer> count = new ArrayList<Integer>();
        count.add(0);
        BasicVisitor countVisitor = new BasicVisitor(context) {
            @Override public Void visit(Rewrite rewrite, Void _) {
                count.set(0, count.get(0) + 1);
                super.visit(rewrite, _);
                return null;
            }
        };

        countVisitor.visitNode(t);
        return count.get(0);
    }

    public static int countHoles(Term t, org.kframework.kil.loader.Context context) {
        final List<Integer> count = new ArrayList<Integer>();
        count.add(0);
        BasicVisitor countVisitor = new BasicVisitor(context) {
            @Override public Void visit(Hole hole, Void _) {
                count.set(0, count.get(0) + 1);
                super.visit(hole, _);
                return null;
            }
        };

        countVisitor.visitNode(t);
        return count.get(0);
    }

    public static boolean hasCell(Term t, org.kframework.kil.loader.Context context) {
        BasicVisitor cellFinder = new BasicVisitor(context) {
            @Override
            public Void visit(KSequence node, Void _) { return null; }

            @Override
            public Void visit(TermCons node, Void _) { return null; }

            @Override
            public Void visit(KApp node, Void _) { return null; }

            @Override
            public Void visit(KList node, Void _) { return null; }

            @Override
            public Void visit(UserList node, Void _) { return null; }

            @Override
            public Void visit(Cell node, Void _) {
                NonLocalExit.RETURN();
                return null;
            }
        };
        try {
            cellFinder.visitNode(t);
        } catch (NonLocalExit e) {
            return true;
        }
        return false;
    }

    public static Term getTerm(Production prod, org.kframework.kil.loader.Context context) {
        if (prod.isSubsort()) {
            final Variable freshVar = Variable.getFreshVar(prod.getItems().get(0).toString());
            if (prod.containsAttribute("klabel")) {
                return KApp.of(KLabelConstant.of(prod.getKLabel(), context), freshVar);
            }
            return freshVar;
        }
        if (prod.isConstant()) {
            String terminal = ((Terminal) prod.getItems().get(0)).getTerminal();
            if (prod.getSort().equals(KSorts.KLABEL)) {
                return KLabelConstant.of(terminal, context);
            } else if (prod.getSort().equals(BoolBuiltin.SORT_NAME)) {
                return BoolBuiltin.kAppOf(terminal);
            } else if (prod.getSort().equals(IntBuiltin.SORT_NAME)) {
                return IntBuiltin.kAppOf(terminal);
            } else if (prod.getSort().equals(StringBuiltin.SORT_NAME)) {
                return StringBuiltin.kAppOf(terminal);
            } else {
                return GenericToken.kAppOf(prod.getSort(), terminal);
            }
        }
        if (prod.isLexical()) {
            return KApp.of(KLabelConstant.of("#token", context),
                           StringBuiltin.kAppOf(prod.getSort()),
                           Variable.getFreshVar("String"));
        }
        TermCons t = new TermCons(prod.getSort(), prod.getCons(), context);
        if (prod.isListDecl()) {
            t.getContents().add(Variable.getFreshVar(((UserList) prod.getItems().get(0)).getSort()));
            t.getContents().add(Variable.getFreshVar(prod.getSort()));
            return t;
        }
        for (ProductionItem item : prod.getItems()) {
            if (item instanceof Sort) {
                t.getContents().add(Variable.getFreshVar(((Sort) item).getName()));
            }
        }
        return t;
    }

    public static boolean isAnonVar(Variable node) {
        return node.getName().startsWith(Constants.anyVarSymbol);
    }

    public static boolean isBuiltinSort(String sort) {
        /* TODO: replace with a proper table of builtins */
        return sort.equals(BoolBuiltin.SORT_NAME)
               || sort.equals(IntBuiltin.SORT_NAME)
               || sort.equals(StringBuiltin.SORT_NAME)
               || sort.equals(FloatBuiltin.SORT_NAME)
               /* LTL builtin sorts */
//               || sort.equals("#LtlFormula")
               || sort.equals("#Prop")
               || sort.equals("#ModelCheckerState")
               || sort.equals("#ModelCheckResult");
    }

    public static boolean isDataSort(String sort) {
        return sort.equals(BoolBuiltin.SORT_NAME)
                || sort.equals(IntBuiltin.SORT_NAME)
                || sort.equals(StringBuiltin.SORT_NAME);
    }

    /**
     * Checks if the specified sort is a computation sort, that is, K, KItem, or
     * any sort other than those defined in {@link KSort}.
     *
     * @param sort
     *            the specified sort
     * @return {@code true} if the specified sort is K, KItem, or any sort other
     *         than those defined in {@code KSort}; otherwise, {@code false}
     */
    public static boolean isComputationSort(String sort) {
        return sort.equals(KSorts.K) || sort.equals(KSorts.KITEM) || !MetaK.isKSort(sort);
    }

    public static String getListUnitLabel(String sep) {
        return  "'.List{\"" + sep + "\"}";
    }

    public static List<Cell> getTopCells(Term t, org.kframework.kil.loader.Context context) {
        final List<Cell> cells = new ArrayList<Cell>();
        new BasicVisitor(context) {
            @Override
            public Void visit(Cell node, Void _) {
                cells.add(node);
                return null;
            }
        }.visitNode(t);
        return cells;
    }

    public static List<String> getAllCellLabels(Term t, org.kframework.kil.loader.Context context) {
        final List<String> cells = new ArrayList<String>();
        new BasicVisitor(context) {
            @Override
            public Void visit(Cell node, Void _) {
                cells.add(node.getLabel());
                return super.visit(node, _);
            }
        }.visitNode(t);
        return cells;
    }

    public static Collection createCollection(Term contents, KSort sort) {
        List<Term> col = new ArrayList<Term>();
        col.add(contents);
        switch (sort) {
            case Bag:
                return new Bag(col);
            case K:
                return new KSequence(col);
            default:
                return null;
        }
    }

}
