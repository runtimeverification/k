// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.SMTLibTerm;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Production;
import org.kframework.kil.UserList;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;


public class KILtoSMTLib extends CopyOnWriteTransformer {

    public static final ImmutableSet<Sort> SMTLIB_BUILTIN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.BIT_VECTOR,
            Sort.of("IntSet"), Sort.of("MIntSet"),
            Sort.of("IntSeq"));
    public static final ImmutableSet<Sort> RESERVED_Z3_SORTS = ImmutableSet.of(
            Sort.LIST,
            Sort.SET,
            Sort.of("Seq"));
    public static final ImmutableSet<String> SMTLIB_BUILTIN_FUNCTIONS = ImmutableSet.of(
            "forall",
            "exists",
            /* core theory */
            "not",
            "and",
            "or",
            "xor",
            "=>",
            "=",
            "distinct",
            "ite",
            /* int theory */
            "+",
            "-",
            "*",
            "div",
            "mod",
            "abs",
            "<=",
            "<",
            ">=",
            ">",
            /* extra int theory */
            "int_max",
            "int_min",
            "int_abs",
            /* extra float theory */
            "remainder",
            "min",
            "max",
            "==",
            /* bit vector theory */
            "concat",
            "extract",
            "bvnot",
            "bvneg",
            "bvand",
            "bvor",
            "bvadd",
            "bvmul",
            "bvudiv",
            "bvurem",
            "bvshl",
            "bvlshr",
            "bvult",
            /* z3-specific bit vector theory */
            "bvsub",
            "bvxor",
            "bvslt",
            "bvule",
            "bvsle",
            "bvugt",
            "bvsgt",
            "bvuge",
            "bvsge",
            "bv2int",
            /* bit vector extras */
            "mint_signed_of_unsigned",
            /* set theory */
            "smt_set_mem", "smt_miset_mem",
            "smt_set_add", "smt_miset_add",
            "smt_set_emp", "smt_miset_emp",
            "smt_set_cup", "smt_miset_cup",
            "smt_set_cap", "smt_miset_cap",
            "smt_set_com", "smt_miset_com",
            "smt_set_ele", "smt_miset_ele",
            "smt_set_dif", "smt_miset_dif",
            "smt_set_sub", "smt_miset_sub",
            "smt_set_lt", "smt_miset_lt",
            "smt_set_le", "smt_miset_le",
            /* associative sequence theory */
            "smt_seq_concat",
            "smt_seq_elem",
            "smt_seq_nil",
            "smt_seq_len",
            "smt_seq2set",
            "smt_seq_sorted",
            "smt_seq_filter",
            /* bool2int */
            "smt_bool2int");

    /**
     * Flag set to true if it is sounds to skip equalities that cannot be translated.
     */
    private final boolean skipEqualities;
    private final HashSet<Variable> variables;

    public static String translateConstraint(SymbolicConstraint constraint) {
        KILtoSMTLib transformer = new KILtoSMTLib(true, constraint.termContext());
        String expression = ((SMTLibTerm) constraint.accept(transformer)).expression();
        return getSortAndFunctionDeclarations(constraint.termContext().definition(), transformer.variables())
             + getAxioms(constraint.termContext())
             + getConstantDeclarations(transformer.variables())
             + "(assert " + expression + ")";
    }

    public static String translateImplication(
            SymbolicConstraint leftHandSide,
            SymbolicConstraint rightHandSide,
            Set<Variable> rightHandSideOnlyVariables) {
        KILtoSMTLib leftTransformer = new KILtoSMTLib(true, leftHandSide.termContext());
        KILtoSMTLib rightTransformer = new KILtoSMTLib(false, rightHandSide.termContext());
        String leftExpression = ((SMTLibTerm) leftHandSide.accept(leftTransformer)).expression();
        String rightExpression = ((SMTLibTerm) rightHandSide.accept(rightTransformer)).expression();
        StringBuilder sb = new StringBuilder();
        sb.append(getSortAndFunctionDeclarations(
                leftHandSide.termContext().definition(),
                Sets.union(leftTransformer.variables(), rightTransformer.variables())));
        sb.append(getAxioms(leftHandSide.termContext()));
        sb.append(getConstantDeclarations(Sets.difference(
                Sets.union(leftTransformer.variables(), rightTransformer.variables()),
                rightHandSideOnlyVariables)));
        sb.append("(assert (and ");
        sb.append(leftExpression);
        sb.append(" (not ");
        rightHandSideOnlyVariables = Sets.intersection(
                rightTransformer.variables(),
                rightHandSideOnlyVariables);
        if (!rightHandSideOnlyVariables.isEmpty()) {
            sb.append("(exists (");
            sb.append(getQuantifiedVariables(rightHandSideOnlyVariables));
            sb.append(") ");
        }
        sb.append(rightExpression);
        if (!rightHandSideOnlyVariables.isEmpty()) {
            sb.append(")");
        }
        sb.append(")))");
        return sb.toString();
    }

    private static String getSortAndFunctionDeclarations(Definition definition, Set<Variable> variables) {
        Set<Sort> sorts = new HashSet<>();
        List<Production> functions = new ArrayList<>();
        for (Production production : definition.context().productions) {
            String smtlib = production.getAttribute(Attribute.SMTLIB_KEY);
            if (smtlib != null && !SMTLIB_BUILTIN_FUNCTIONS.contains(smtlib) && !smtlib.startsWith("(")) {
                functions.add(production);
                sorts.add(renameSort(Sort.of(production.getSort())));
                for (int i = 0; i < production.getArity(); ++i) {
                    sorts.add(renameSort(Sort.of(production.getChildSort(i))));
                }
            }
        }
        for (Variable variable : variables) {
            sorts.add(renameSort(variable.sort()));
        }

        if (!Sets.intersection(sorts, RESERVED_Z3_SORTS).isEmpty()) {
            throw new UnsupportedOperationException("do not use sorts " + RESERVED_Z3_SORTS);
        }

        StringBuilder sb = new StringBuilder();

        for (Sort sort : Sets.difference(sorts, SMTLIB_BUILTIN_SORTS)) {
            sb.append("(declare-sort ");
            sb.append(sort);
            sb.append(")\n");
        }

        for (Production production : functions) {
            sb.append("(declare-fun ");
            sb.append(production.getAttribute(Attribute.SMTLIB_KEY));
            sb.append(" (");
            List<String> childrenSorts = new ArrayList<>();
            for (int i = 0; i < production.getArity(); ++i) {
                childrenSorts.add(getSortName(production.getChildNode(i)));
            }
            Joiner.on(" ").appendTo(sb, childrenSorts);
            sb.append(") ");
            sb.append(getSortName(production));
            sb.append(")\n");
        }

        return sb.toString();
    }

    private static String getAxioms(TermContext context) {
        StringBuilder sb = new StringBuilder();
        for (Rule rule : context.definition().functionRules().values()) {
            if (rule.containsAttribute(Attribute.SMT_LEMMA_KEY)) {
                try {
                    KILtoSMTLib transformer = new KILtoSMTLib(false, context);
                    String leftExpression = ((SMTLibTerm) rule.leftHandSide().accept(transformer)).expression();
                    String rightExpression = ((SMTLibTerm) rule.rightHandSide().accept(transformer)).expression();
                    sb.append("(assert ");
                    if (!transformer.variables().isEmpty()) {
                        sb.append("(forall (");
                        sb.append(getQuantifiedVariables(transformer.variables()));
                        sb.append(") ");
                        //sb.append(") (! ");
                    }
                    sb.append("(= ");
                    sb.append(leftExpression);
                    sb.append(" ");
                    sb.append(rightExpression);
                    sb.append(")");
                    //sb.append(" :pattern(");
                    //sb.append(leftExpression);
                    //sb.append(")");
                    if (!transformer.variables().isEmpty()) {
                        sb.append(")");
                    }
                    sb.append(")\n");
                } catch (UnsupportedOperationException e) { }
            }
        }
        return sb.toString();
    }

    private static String getConstantDeclarations(Set<Variable> variables) {
        StringBuilder sb = new StringBuilder();
        for (Variable variable : variables) {
            sb.append("(declare-fun ");
            // TODO(AndreiS): make sure variable names are SMTLib compliant
            sb.append(variable.name());
            sb.append(" () ");
            String sortName;
            sortName = getSortName(variable);
            sb.append(sortName);
            sb.append(")\n");
        }
        return sb.toString();
    }

    private static String getQuantifiedVariables(Set<Variable> variables) {
        StringBuilder sb = new StringBuilder();
        for (Variable variable : variables) {
            sb.append("(");
            // TODO(AndreiS): make sure variable names are SMTLib compliant
            sb.append(variable.name());
            sb.append(" ");
            String sortName;
            sortName = getSortName(variable);
            sb.append(sortName);
            sb.append(")");
        }
        return sb.toString();
    }

    private static String getSortName(ASTNode node) {
        Sort s;
        if (node instanceof NonTerminal) {
            s = Sort.of(((NonTerminal) node).getSort());
        } else if (node instanceof UserList) {
            s = Sort.of(((UserList) node).getSort());
        } else if (node instanceof Production) {
            s = Sort.of(((Production) node).getSort());
        } else if (node instanceof Variable) {
            s = ((Variable) node).sort();
        } else {
            assert false : "getSortName should be called with a sorted node";
            return null;
        }

        s = renameSort(s);
        if (s == Sort.BIT_VECTOR) {
            return "(_ BitVec " + BitVector.getBitwidthOrDie(node) + ")";
        } else if (s == Sort.FLOAT) {
            Pair<Integer, Integer> pair = FloatToken.getExponentAndSignificandOrDie(node);
            return "(_ FP " + pair.getLeft() + " " + pair.getRight() + ")";
        } else {
            return s.name();
        }
    }

    private static Sort renameSort(Sort sort) {
        if (sort == Sort.LIST) {
            return Sort.of("IntSeq");
        } else {
            return sort;
        }
    }

    public KILtoSMTLib(boolean skipEqualities, TermContext context) {
        super(context);
        this.skipEqualities = skipEqualities;
        variables = new HashSet<>();
    }

    /**
     * Returns an unmodifiable view of the sets of variables occurring during the translation.
     */
    public Set<Variable> variables() {
        return Collections.unmodifiableSet(variables);
    }

    /**
     * Translates the equalities of the given symbolic constraint into SMTLib format.
     * Ignores the substitution of the symbolic constraint.
     */
    @Override
    public ASTNode transform(SymbolicConstraint constraint) {
        Set<Equality> equalities = Sets.newHashSet(constraint.equalities());
        if (!skipEqualities) {
            constraint.substitution().entrySet().stream()
                    .map(entry -> new Equality(entry.getKey(), entry.getValue(), context))
                    .forEach(equalities::add);

        }

        if (equalities.isEmpty()) {
            return new SMTLibTerm("true");
        }

        StringBuilder sb = new StringBuilder();
        sb.append("(and");
        boolean isEmptyAdd = true;
        for (Equality equality : equalities) {
            try {
                String left = ((SMTLibTerm) equality.leftHandSide().accept(this)).expression();
                String right = ((SMTLibTerm) equality.rightHandSide().accept(this)).expression();
                sb.append(" (= ");
                sb.append(left);
                sb.append(" ");
                sb.append(right);
                sb.append(")");
                isEmptyAdd = false;
            } catch (UnsupportedOperationException e) {
                // TODO(AndreiS): fix this translation and the exceptions
                if (skipEqualities){
                    /* it is sound to skip the equalities that cannot be translated */
                    e.printStackTrace();
                } else {
                    throw e;
                }
            }
        }
        if (isEmptyAdd) {
            sb.append(" true");
        }
        sb.append(")");
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(KItem kItem) {
        if (!(kItem.kLabel() instanceof KLabelConstant)) {
            throw new UnsupportedOperationException();
        }
        KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

        if (!(kItem.kList() instanceof KList)) {
            throw new UnsupportedOperationException();
        }
        KList kList = (KList) kItem.kList();

        if (kList.hasFrame()) {
            throw new UnsupportedOperationException();
        }

        String label = kLabel.smtlib();
        if (label == null) {
            throw new UnsupportedOperationException("missing SMTLib translation for " + kLabel);
        }

        if (label.startsWith("(")) {
            // smtlib expression instead of operator
            String expression = label;
            for (int i = 0; i < kList.getContents().size(); i++) {
                expression = expression.replaceAll("\\#" + (i + 1) + "(?![0-9])", ((SMTLibTerm) kList.get(i).accept(this)).expression());
            }
            return new SMTLibTerm(expression);
        }

        List<Term> arguments;
        switch (label) {
            case "exists":
                Variable variable = (Variable) kList.get(0);
                label = "exists ((" + variable.name() + " " + variable.sort() + ")) ";
                arguments = ImmutableList.of(kList.get(1));
                break;
            case "extract":
                int beginIndex = ((IntToken) kList.get(1)).intValue();
                int endIndex = ((IntToken) kList.get(2)).intValue() - 1;
                label = "(_ extract " + endIndex + " " + beginIndex + ")";
                arguments = ImmutableList.of(kList.get(0));
                break;
            default:
                arguments = kList.getContents();
        }

        if (!arguments.isEmpty()) {
            StringBuilder sb = new StringBuilder();
            sb.append("(");
            sb.append(label);
            for (Term argument : arguments) {
                sb.append(" ");
                sb.append(((SMTLibTerm) argument.accept(this)).expression());
            }
            sb.append(")");
            return new SMTLibTerm(sb.toString());
        } else {
            return new SMTLibTerm(label);
        }
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return new SMTLibTerm(Long.toString(intToken.longValue()));
    }

    @Override
    public ASTNode transform(FloatToken floatToken) {
        StringBuilder sb = new StringBuilder();
        sb.append(String.format(
                "((_ asFloat %d %d) roundNearestTiesToEven %s 0)",
                floatToken.exponent(), floatToken.bigFloatValue().precision(),
                floatToken.bigFloatValue().toString("%f")));
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        StringBuilder sb = new StringBuilder();
        sb.append("#b");
        for (int i = bitVector.bitwidth() - 1; i >= 0; --i) {
            BigInteger value = bitVector.unsignedValue();
            sb.append(value.testBit(i) ? "1" : "0");
        }
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        return builtinList.toK(context).accept(this);
    }

    @Override
    public ASTNode transform(Variable variable) {
        variables.add(variable);
        return new SMTLibTerm(variable.name());
    }

}
