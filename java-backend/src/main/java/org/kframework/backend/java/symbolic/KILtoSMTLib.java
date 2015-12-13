// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.SMTLibTerm;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.SortSignature;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Production;
import org.kframework.kil.UserList;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import org.kframework.krun.KRunOptions;


public class KILtoSMTLib extends CopyOnWriteTransformer {

    public static final ImmutableSet<Sort> SMTLIB_BUILTIN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.BIT_VECTOR,
            Sort.of("Float"),
            Sort.of("String"),
            Sort.of("IntSet"),
            Sort.of("MIntSet"),
            Sort.of("FloatSet"),
            Sort.of("StringSet"),
            Sort.of("IntSeq"),
            Sort.of("MIntSeq"),
            Sort.of("FloatSeq"),
            Sort.of("StringSeq"));
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
            /* string theory */
            "string_lt",
            "string_le",
            "string_gt",
            "string_ge",
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
            /* float set theory */
            "float_set_mem",
            "float_set_add",
            "float_set_emp",
            "float_set_cup",
            "float_set_cap",
            "float_set_com",
            "float_set_ele",
            "float_set_dif",
            "float_set_sub",
            "float_set_lt",
            "float_set_le",
            /* string set theory */
            "string_set_mem",
            "string_set_add",
            "string_set_emp",
            "string_set_cup",
            "string_set_cap",
            "string_set_com",
            "string_set_ele",
            "string_set_dif",
            "string_set_sub",
            "string_set_lt",
            "string_set_le",
            /* associative sequence theory */
            "smt_seq_concat",
            "smt_seq_elem",
            "smt_seq_nil",
            "smt_seq_len",
            "smt_seq_sum",
            "smt_seq2set",
            "smt_seq_sorted",
            "smt_seq_filter",
            /* bool2int */
            "smt_bool2int");

    public static String translateConstraint(ConjunctiveFormula constraint) {
        KILtoSMTLib kil2SMT = new KILtoSMTLib(true, constraint.globalContext());
        String expression = kil2SMT.translate(constraint).expression();
        return kil2SMT.getSortAndFunctionDeclarations(kil2SMT.variables())
                + kil2SMT.getAxioms()
                + kil2SMT.getConstantDeclarations(kil2SMT.variables())
                + "(assert " + expression + ")";
    }

    public static String translateImplication(
            ConjunctiveFormula leftHandSide,
            ConjunctiveFormula rightHandSide,
            Set<Variable> rightHandSideOnlyVariables) {
        KILtoSMTLib leftTransformer = new KILtoSMTLib(true, leftHandSide.globalContext());
        KILtoSMTLib rightTransformer = new KILtoSMTLib(false, rightHandSide.globalContext());
        String leftExpression = leftTransformer.translate(leftHandSide).expression();
        String rightExpression = rightTransformer.translate(rightHandSide).expression();
        StringBuilder sb = new StringBuilder();
        sb.append(leftTransformer.getSortAndFunctionDeclarations(
                Sets.union(leftTransformer.variables(), rightTransformer.variables())));
        sb.append(leftTransformer.getAxioms());
        sb.append(leftTransformer.getConstantDeclarations(Sets.difference(
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
            sb.append(leftTransformer.getQuantifiedVariables(rightHandSideOnlyVariables));
            sb.append(") ");
        }
        sb.append(rightExpression);
        if (!rightHandSideOnlyVariables.isEmpty()) {
            sb.append(")");
        }
        sb.append(")))");
        return sb.toString();
    }

    private final Definition definition;

    private final KRunOptions krunOptions;

    /**
     * Flag set to true if it is sounds to skip equalities that cannot be translated.
     */
    private final boolean skipEqualities;
    private final HashSet<Variable> variables;
    private final HashMap<Term, Variable> termAbstractionMap = Maps.newHashMap();
    private final HashMap<UninterpretedToken, Integer> tokenEncoding;

    public KILtoSMTLib(boolean skipEqualities, GlobalContext global) {
        this(skipEqualities, global.getDefinition(), global.krunOptions);
    }

    private KILtoSMTLib(boolean skipEqualities, Definition definition, KRunOptions krunOptions) {
        this.definition = definition;
        this.krunOptions = krunOptions;
        this.skipEqualities = skipEqualities;
        variables = new HashSet<>();
        tokenEncoding = new HashMap<>();
    }

    private SMTLibTerm translate(JavaSymbolicObject object) {
        ASTNode astNode = object.accept(this);
        if (astNode instanceof SMTLibTerm) {
            return (SMTLibTerm) astNode;
        } else {
            throw new SMTTranslationFailure();
        }
    }

    private String getSortAndFunctionDeclarations(Set<Variable> variables) {
        Set<Sort> sorts = new HashSet<>();
        List<KLabelConstant> functions = new ArrayList<>();
        for (KLabelConstant kLabel : definition.kLabels()) {
            String smtlib = kLabel.getAttr(Attribute.SMTLIB_KEY);
            if (smtlib != null && !SMTLIB_BUILTIN_FUNCTIONS.contains(smtlib) && !smtlib.startsWith("(")) {
                functions.add(kLabel);
                assert kLabel.signatures().size() == 1;
                SortSignature signature = kLabel.signatures().iterator().next();
                sorts.add(renameSort(signature.result()));
                signature.parameters().stream()
                        .map(this::renameSort)
                        .forEach(sorts::add);
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

        for (KLabelConstant kLabel : functions) {
            sb.append("(declare-fun ");
            sb.append(kLabel.getAttr(Attribute.SMTLIB_KEY));
            sb.append(" (");
            List<String> childrenSorts = new ArrayList<>();
            for (Sort sort : kLabel.signatures().iterator().next().parameters()) {
                childrenSorts.add(renameSort(sort).name());
            }
            Joiner.on(" ").appendTo(sb, childrenSorts);
            sb.append(") ");
            sb.append(renameSort(kLabel.signatures().iterator().next().result()).name());
            sb.append(")\n");
        }

        return sb.toString();
    }

    private String getAxioms() {
        StringBuilder sb = new StringBuilder();
        for (Rule rule : definition.functionRules().values()) {
            if (rule.containsAttribute(Attribute.SMT_LEMMA_KEY)) {
                try {
                    KILtoSMTLib kil2SMT = new KILtoSMTLib(false, definition, krunOptions);
                    String leftExpression = kil2SMT.translate(rule.leftHandSide()).expression();
                    String rightExpression = kil2SMT.translate(rule.rightHandSide()).expression();
                    sb.append("(assert ");
                    if (!kil2SMT.variables().isEmpty()) {
                        sb.append("(forall (");
                        sb.append(kil2SMT.getQuantifiedVariables(kil2SMT.variables()));
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
                    if (!kil2SMT.variables().isEmpty()) {
                        sb.append(")");
                    }
                    sb.append(")\n");
                } catch (UnsupportedOperationException e) { }
            }
        }
        return sb.toString();
    }

    private String getConstantDeclarations(Set<Variable> variables) {
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

    private String getQuantifiedVariables(Set<Variable> variables) {
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

    private String getSortName(ASTNode node) {
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
        } else if (s == Sort.FLOAT && !krunOptions.experimental.smt.floatsAsPO) {
            Pair<Integer, Integer> pair = FloatToken.getExponentAndSignificandOrDie(node);
            return "(_ FP " + pair.getLeft() + " " + pair.getRight() + ")";
        } else {
            return s.name();
        }
    }

    private Sort renameSort(Sort sort) {
        sort = definition.smtSortFlattening().getOrDefault(sort, sort);
        if (sort == Sort.LIST) {
            return Sort.of("IntSeq");
        } else if (sort == Sort.of("Id")) {
            return Sort.INT;
        } else {
            return sort;
        }
    }

    /**
     * Returns an unmodifiable view of the set of variables occurring during the translation.
     */
    public Set<Variable> variables() {
        return Sets.union(variables, ImmutableSet.copyOf(termAbstractionMap.values()));
    }

    /**
     * Translates the equalities of the given symbolic constraint into SMTLib format.
     * Ignores the substitution of the symbolic constraint.
     */
    @Override
    public ASTNode transform(ConjunctiveFormula constraint) {
        assert constraint.disjunctions().isEmpty() : "disjunctions are not supported by SMT translation";
        Set<Equality> equalities = Sets.newHashSet(constraint.equalities());
        if (!skipEqualities) {
            constraint.substitution().entrySet().stream()
                    .map(entry -> new Equality(entry.getKey(), entry.getValue(), constraint.globalContext()))
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
                String left = translateTerm(equality.leftHandSide());
                String right = translateTerm(equality.rightHandSide());
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

    public String translateTerm(Term term) {
        try {
            return translate(term).expression();
        } catch (UnsupportedOperationException e) {
            if (skipEqualities){
                Variable variable = termAbstractionMap.get(term);
                if (variable == null) {
                    variable = Variable.getAnonVariable(term.sort());
                    termAbstractionMap.put(term, variable);
                }
                return variable.name();
            } else {
                throw e;
            }
        }
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

        if (krunOptions.experimental.smt.floatsAsPO) {
            switch (kLabel.label()) {
                case "'_<Float_":
                    label = "float_lt";
                    break;
                case "'_<=Float_":
                    label = "float_le";
                    break;
                case "'_>Float_":
                    label = "float_gt";
                    break;
                case "'_>=Float_":
                    label = "float_ge";
                    break;
                case "'maxFloat":
                    label = "float_max";
                    break;
                case "'minFloat":
                    label = "float_min";
                    break;
                case "'_==Float_":
                    label = "=";
                    break;
                case "'_=/=Float_":
                    label = "(not (= #1 #2))";
                    break;
                case "'isNaN":
                    label = "(= #1 float_nan)";
                    break;
            }
        }

        if (label.startsWith("(")) {
            // smtlib expression instead of operator
            String expression = label;
            for (int i = 0; i < kList.getContents().size(); i++) {
                expression = expression.replaceAll("#" + (i + 1) + "(?![0-9])", translate(kList.get(i)).expression());
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
                sb.append(translate(argument).expression());
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
        if (krunOptions.experimental.smt.floatsAsPO
                && (floatToken.bigFloatValue().isPositiveZero() || floatToken.bigFloatValue().isNegativeZero())) {
            return new SMTLibTerm("float_zero");
        }
        assert !krunOptions.experimental.smt.floatsAsPO;

        return new SMTLibTerm(String.format(
                "((_ asFloat %d %d) roundNearestTiesToEven %s 0)",
                floatToken.exponent(), floatToken.bigFloatValue().precision(),
                floatToken.bigFloatValue().toString("%f")));
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
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        if (tokenEncoding.get(uninterpretedToken) == null) {
            tokenEncoding.put(uninterpretedToken, tokenEncoding.size());
        }
        return new SMTLibTerm(Integer.toString(tokenEncoding.get(uninterpretedToken)));
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        //return builtinList.toKore().accept(this);
        return ((BuiltinList) BuiltinList.concatenate(builtinList.globalContext(), builtinList)).toKore().accept(this);
    }

    @Override
    public ASTNode transform(Variable variable) {
        variables.add(variable);
        return new SMTLibTerm(variable.name());
    }

}
