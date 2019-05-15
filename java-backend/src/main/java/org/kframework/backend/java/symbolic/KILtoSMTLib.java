// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
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
import org.kframework.builtin.Sorts;
import org.kframework.kil.Attribute;
import org.kframework.kore.KORE;
import org.kframework.krun.KRunOptions;
import org.kframework.utils.errorsystem.KEMException;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Formatter;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;


public class    KILtoSMTLib extends CopyOnWriteTransformer {

    public static final ImmutableSet<Sort> SMTLIB_BUILTIN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.BIT_VECTOR,
            Sort.of(Sorts.Float()),
            Sort.of(Sorts.String()),
            Sort.of(KORE.Sort("IntSet")),
            Sort.of(KORE.Sort("MIntSet")),
            Sort.of(KORE.Sort("FloatSet")),
            Sort.of(KORE.Sort("StringSet")),
            Sort.of(KORE.Sort("IntSeq")),
            Sort.of(KORE.Sort("MIntSeq")),
            Sort.of(KORE.Sort("FloatSeq")),
            Sort.of(KORE.Sort("StringSeq")));
    public static final ImmutableSet<String> SMTLIB_BUILTIN_FUNCTIONS = ImmutableSet.of(
            "forall",
            "exists",
            /* array theory */
            "select",
            "store",
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
            "^",
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

    public static CharSequence translateConstraint(ConjunctiveFormula constraint) {
        KILtoSMTLib kil2SMT = new KILtoSMTLib(true, constraint.globalContext());

        //this line has side effects used later
        CharSequence expression = kil2SMT.translate(constraint).expression();

        StringBuilder sb = new StringBuilder(1024);
        kil2SMT.appendSortAndFunctionDeclarations(sb, kil2SMT.variables());
        kil2SMT.appendAxioms(sb);
        kil2SMT.appendConstantDeclarations(sb, kil2SMT.variables());
        sb.append("(assert ")
                .append(expression)
                .append(")");
        return sb;
    }

    /**
     * Generates the z3 query for "left /\ !right".
     * left -> right <==> !(left /\ !right)
     * => this query should be unsat for implication to be proven.
     */
    public static CharSequence translateImplication(
            ConjunctiveFormula leftHandSide,
            ConjunctiveFormula rightHandSide,
            Set<Variable> existentialQuantVars) {
        KILtoSMTLib leftTransformer = new KILtoSMTLib(true, leftHandSide.globalContext());
        // termAbstractionMap is shared between transformers
        KILtoSMTLib rightTransformer = new KILtoSMTLib(false,
                rightHandSide.globalContext().getDefinition(),
                rightHandSide.globalContext().krunOptions,
                rightHandSide.globalContext(), leftTransformer.termAbstractionMap);

        CharSequence leftExpression = leftTransformer.translate(leftHandSide).expression();
        String rightExpression = rightTransformer.translate(rightHandSide).expression().toString();
        StringBuilder sb = new StringBuilder(1024);
        Sets.SetView<Variable> allVars = Sets.union(leftTransformer.variables(), rightTransformer.variables());
        Set<Variable> usedExistentialQuantVars = Sets.intersection(existentialQuantVars, rightTransformer.variables());
        leftTransformer.appendSortAndFunctionDeclarations(sb, allVars);
        leftTransformer.appendAxioms(sb);
        leftTransformer.appendConstantDeclarations(sb, Sets.difference(allVars, usedExistentialQuantVars));

        sb.append("(assert (and\n  ");
        sb.append(leftExpression);
        sb.append("\n  (not ");
        if (!usedExistentialQuantVars.isEmpty()) {
            sb.append("(exists (");
            leftTransformer.appendQuantifiedVariables(sb, usedExistentialQuantVars);
            sb.append(") ");
        }
        sb.append(rightExpression);
        if (!usedExistentialQuantVars.isEmpty()) {
            sb.append(")");
        }
        sb.append(")\n))");
        return sb;
    }

    private final Definition definition;

    private final GlobalContext globalContext;
    private final KRunOptions krunOptions;

    /**
     * Flag indicating whether KItem terms and equalities that cannot be translated can be abstracted away into
     * fresh variables. If the flag is false and untranslatable term is encountered, an exception will be thrown instead.
     */
    private final boolean allowNewVars;
    //All sets/maps are LinkedHashXXX, to avoid non-determinism when iterated and produce consistent logs.
    private final LinkedHashSet<Variable> variables;
    private final LinkedHashMap<Term, Variable> termAbstractionMap;
    private final LinkedHashMap<UninterpretedToken, Integer> tokenEncoding;

    private KILtoSMTLib(boolean allowNewVars, GlobalContext global) {
        this(allowNewVars, global.getDefinition(), global.krunOptions, global, new LinkedHashMap<>());
    }

    private KILtoSMTLib(boolean allowNewVars, Definition definition, KRunOptions krunOptions,
                        GlobalContext global) {
        this(allowNewVars, definition, krunOptions, global, new LinkedHashMap<>());
    }

    /**
     * @param allowNewVars If true, untranslatable terms not present in {@code termAbstractionMap} will be
     *                     substituted with fresh vars. If false, only terms already present in the map will be
     *                     substituted. Also, if true, substitutions will be translated into Z3 as equalities.
     */
    private KILtoSMTLib(boolean allowNewVars, Definition definition, KRunOptions krunOptions,
                        GlobalContext global, LinkedHashMap<Term, Variable> termAbstractionMap) {
        this.allowNewVars = allowNewVars;
        this.definition = definition;
        this.krunOptions = krunOptions;
        this.globalContext = global;
        this.termAbstractionMap = termAbstractionMap;
        variables = new LinkedHashSet<>();
        tokenEncoding = new LinkedHashMap<>();
    }

    private SMTLibTerm translate(JavaSymbolicObject object) {
        JavaSymbolicObject astNode = object.accept(this);
        if (astNode instanceof SMTLibTerm) {
            return (SMTLibTerm) astNode;
        } else {
            throw new SMTTranslationFailure("Attempting to translate an unsupported term of type " + object.getClass());
        }
    }

    private StringBuilder appendSortAndFunctionDeclarations(StringBuilder sb, Set<Variable> variables) {
        Set<Sort> sorts = new LinkedHashSet<>();
        List<KLabelConstant> functions = new ArrayList<>();
        for (KLabelConstant kLabel : definition.kLabels()) {
            String smtlib = kLabel.getAttr(Attribute.SMTLIB_KEY);
            Boolean inSmtPrelude = kLabel.getAttr(Attribute.SMT_PRELUDE_KEY) != null;
            if (smtlib != null && !inSmtPrelude && !SMTLIB_BUILTIN_FUNCTIONS.contains(smtlib) && !smtlib.startsWith("(")) {
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

        for (Sort sort : Sets.difference(sorts, Sets.union(SMTLIB_BUILTIN_SORTS, definition.smtPreludeSorts()))) {
            if (sort.equals(Sort.MAP) && krunOptions.experimental.smt.mapAsIntArray) {
                sb.append("(define-sort Map () (Array Int Int))");
            } else {
                sb.append("(declare-sort ");
                sb.append(renameSort(sort).name());
                sb.append(")\n");
            }
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

        return sb;
    }

    private CharSequence appendAxioms(StringBuilder sb) {
        for (Rule rule : definition.functionRules().values()) {
            if (rule.att().contains(Attribute.SMT_LEMMA_KEY)) {
                try {
                    KILtoSMTLib kil2SMT = new KILtoSMTLib(false, globalContext);
                    CharSequence leftExpression = kil2SMT.translate(rule.leftHandSide()).expression();
                    CharSequence rightExpression = kil2SMT.translate(rule.rightHandSide()).expression();
                    sb.append("(assert ");
                    if (!kil2SMT.variables().isEmpty()) {
                        sb.append("(forall (");
                        kil2SMT.appendQuantifiedVariables(sb, kil2SMT.variables());
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
        return sb;
    }

    private CharSequence appendConstantDeclarations(StringBuilder sb, Set<Variable> variables) {
        for (Variable variable : variables) {
            sb.append("(declare-fun ");
            sb.append("|").append(variable.longName()).append("|");
            sb.append(" () ");
            String sortName;
            sortName = getSortName(variable);
            sb.append(sortName);
            sb.append(")\n");
        }
        return sb;
    }

    private CharSequence appendQuantifiedVariables(StringBuilder sb, Set<Variable> variables) {
        for (Variable variable : variables) {
            sb.append("(");
            sb.append("|").append(variable.longName()).append("|");
            sb.append(" ");
            String sortName;
            sortName = getSortName(variable);
            sb.append(sortName);
            sb.append(")");
        }
        return sb;
    }

    private String getSortName(Variable variable) {
        return getParametricSortName(variable.att(), variable.sort());
    }

    private String getParametricSortName(Att att, Sort s) {
        s = renameSort(s);
        if (s == Sort.BIT_VECTOR) {
            return "(_ BitVec " + BitVector.getBitwidthOrDie(att) + ")";
        } else if (s == Sort.FLOAT && !krunOptions.experimental.smt.floatsAsPO) {
            Pair<Integer, Integer> pair = FloatToken.getExponentAndSignificandOrDie(att);
            return "(_ FP " + pair.getLeft() + " " + pair.getRight() + ")";
        } else {
            return s.name();
        }
    }

    private Sort renameSort(Sort sort) {
        sort = definition.smtSortFlattening().getOrDefault(sort, sort);
        if (sort == Sort.LIST) {
            return Sort.of(KORE.Sort("IntSeq"));
        } else if (sort == Sort.of(Sorts.Id())) {
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
    public SMTLibTerm transform(ConjunctiveFormula constraint) {
        if (!constraint.disjunctions().isEmpty()) {
            throw KEMException.criticalError(
                    "disjunctions are not supported by SMT translation for:\n" + constraint.toStringMultiline());
        }
        Set<Equality> equalities = Sets.newLinkedHashSet(constraint.equalities());
        if (!allowNewVars) {
            constraint.substitution().entrySet().stream()
                    .map(entry -> new Equality(entry.getKey(), entry.getValue(), constraint.globalContext()))
                    .forEach(equalities::add);
        }

        if (equalities.isEmpty()) {
            return new SMTLibTerm(Boolean.TRUE.toString());
        }

        StringBuilder sb = new StringBuilder();
        sb.append("(and");
        boolean isEmptyAdd = true;
        for (Equality equality : equalities) {
            try {
                CharSequence left = translateTerm(equality.leftHandSide());
                CharSequence right = translateTerm(equality.rightHandSide());
                sb.append("\n\t(= ");
                sb.append(left);
                sb.append(" ");
                sb.append(right);
                sb.append(")");
                isEmptyAdd = false;
            } catch (UnsupportedOperationException e) {
                // TODO(AndreiS): fix this translation and the exceptions
                if (allowNewVars){
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
        return new SMTLibTerm(sb);
    }

    public CharSequence translateTerm(Term term) {
        try {
            return translate(term).expression();
        } catch (SMTTranslationFailure | UnsupportedOperationException e) {
            return abstractThroughAnonVariable(term, e);
        }
    }

    private String abstractThroughAnonVariable(Term term, RuntimeException e) {
        Variable variable = termAbstractionMap.get(term);
        if (variable == null) {
            if (allowNewVars) {
                variable = Variable.getAnonVariable(term.sort());
                termAbstractionMap.put(term, variable);
                if (globalContext.javaExecutionOptions.debugZ3Queries) {
                    globalContext.log().format("\t%s ::= %s\n", variable.longName(), term);
                }
            } else {
                throw e;
            }
        }
        return variable.longName();
    }

    @Override
    public SMTLibTerm transform(KItem kItem) {
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
        if (kLabel.label().equals("Map:lookup") && krunOptions.experimental.smt.mapAsIntArray) {
            label = "select";
        }
        if (kLabel.label().equals("_[_<-_]") && krunOptions.experimental.smt.mapAsIntArray) {
            label = "store";
        }
        if (label == null) {
            return new SMTLibTerm(abstractThroughAnonVariable(kItem,
                    new SMTTranslationFailure("missing SMTLib translation for " + kLabel)));
        }

        if (krunOptions.experimental.smt.floatsAsPO) {
            switch (kLabel.label()) {
                case "_<Float_":
                    label = "float_lt";
                    break;
                case "_<=Float_":
                    label = "float_le";
                    break;
                case "_>Float_":
                    label = "float_gt";
                    break;
                case "_>=Float_":
                    label = "float_ge";
                    break;
                case "maxFloat":
                    label = "float_max";
                    break;
                case "minFloat":
                    label = "float_min";
                    break;
                case "_==Float_":
                    label = "=";
                    break;
                case "_=/=Float_":
                    label = "(not (= #1 #2))";
                    break;
                case "isNaN":
                    label = "(= #1 float_nan)";
                    break;
            }
        }

        if (label.startsWith("(")) {
            // smtlib expression instead of operator
            String expression = label;
            for (int i = 0; i < kList.getContents().size(); i++) {
                expression = expression.replaceAll("#" + (i + 1) + "(?![0-9])",
                        translate(kList.get(i)).expression().toString());
            }
            return new SMTLibTerm(expression);
        }

        List<Term> arguments;
        switch (label) {
            case "exists":
                Variable variable = (Variable) kList.get(0);
                label = "exists ((" + variable.longName() + " " + variable.sort() + ")) ";
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
            return new SMTLibTerm(sb);
        } else {
            return new SMTLibTerm(label);
        }
    }

    @Override
    public JavaSymbolicObject transform(BuiltinMap builtinMap) {
        return new SMTLibTerm(abstractThroughAnonVariable(builtinMap,
                new SMTTranslationFailure("BuiltinMap can be translated to Z3 only through fresh var")));
    }

    @Override
    public SMTLibTerm transform(BoolToken boolToken) {
        return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
    }

    @Override
    public SMTLibTerm transform(IntToken intToken) {
        return new SMTLibTerm(intToken.javaBackendValue());
    }

    @Override
    public SMTLibTerm transform(FloatToken floatToken) {
        if (krunOptions.experimental.smt.floatsAsPO
                && (floatToken.bigFloatValue().isPositiveZero() || floatToken.bigFloatValue().isNegativeZero())) {
            return new SMTLibTerm("float_zero");
        }
        assert !krunOptions.experimental.smt.floatsAsPO;

        StringBuilder sb = new StringBuilder();
        new Formatter(sb).format(
                "((_ asFloat %d %d) roundNearestTiesToEven %s 0)",
                floatToken.exponent(), floatToken.bigFloatValue().precision(),
                floatToken.bigFloatValue().toString("%f"));

        return new SMTLibTerm(sb);
    }

    @Override
    public SMTLibTerm transform(BitVector bitVector) {
        StringBuilder sb = new StringBuilder();
        sb.append("#b");
        for (int i = bitVector.bitwidth() - 1; i >= 0; --i) {
            BigInteger value = bitVector.unsignedValue();
            sb.append(value.testBit(i) ? "1" : "0");
        }
        return new SMTLibTerm(sb);
    }

    @Override
    public SMTLibTerm transform(UninterpretedToken uninterpretedToken) {
        if (tokenEncoding.get(uninterpretedToken) == null) {
            tokenEncoding.put(uninterpretedToken, tokenEncoding.size());
        }
        return new SMTLibTerm(Integer.toString(tokenEncoding.get(uninterpretedToken)));
    }

    @Override
    public JavaSymbolicObject transform(BuiltinList builtinList) {
        return builtinList.toKore().accept(this);
    }

    @Override
    public SMTLibTerm transform(Variable variable) {
        variables.add(variable);
        return new SMTLibTerm("|" + variable.longName() + "|");
    }

}
