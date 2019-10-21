// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.Collections;
import org.kframework.attributes.Location;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kil.Attribute;
import org.kframework.kore.Sort;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KEMException;

import scala.collection.Seq;
import scala.collection.Set;
import scala.Tuple2;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

public class TypeInferencer implements AutoCloseable {

  public static enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    UNKNOWN
  }

  private Status status = null;

  private final Process process;
  private final PrintStream z3;
  private final BufferedReader output;
  private final Module mod;
  private final java.util.Set<Sort> sorts;

  private static final String PRELUDE1 = 
    "(set-option :timeout 5000)\n" +
    "(define-sort Head () Int)\n" +
    "(declare-datatypes () ((Lst nil (cons (hd Sort) (tl Lst)))\n" +
    "                       (Sort (mkSort (head Head) (params Lst)))))\n" +
    "(define-fun s ((h Head)) Sort (mkSort h nil))\n";

  private static final String PRELUDE2 =
    "(define-fun <=Sort ((s1 Sort) (s2 Sort)) Bool (or (<Sort s1 s2) (= s1 s2)))\n";

  public TypeInferencer(Module mod) {
    try {
      process = new ProcessBuilder().command("z3", "-in").redirectError(ProcessBuilder.Redirect.INHERIT).start();
    } catch (IOException e) {
      throw KEMException.criticalError("Could not start z3 process", e);
    }
    z3 = new PrintStream(process.getOutputStream());
    output = new BufferedReader(new InputStreamReader(process.getInputStream()));
    println(PRELUDE1);
    this.mod = mod;
    this.sorts = stream(mod.definedSorts()).filter(this::isRealSort).collect(Collectors.toSet());
    push(mod);
  }

  public boolean isRealSort(Sort s) {
    return !RuleGrammarGenerator.isParserSort(s) || s.equals(Sorts.K()) || s.equals(Sorts.KItem()) || s.equals(Sorts.KLabel());
  }

  public Module module() {
    return mod;
  }

  public void push(Module mod) {
    for (Sort s : sorts) {
      println("(declare-const Sort" + s.name() + " Head)");
    }
    print("(assert (distinct ");
    for (Sort s : sorts) {
      print("Sort" + s.name() + " ");
    }
    println("))");
    println("(define-fun <Sort ((s1 Sort) (s2 Sort)) Bool");
    int parens = 0;
    for (Tuple2<Sort, Set<Sort>> relation : iterable(mod.subsorts().relations())) {
      if (!isRealSort(relation._1())) {
        continue;
      }
      for (Sort s2 : iterable(relation._2())) {
        if (!isRealSort(s2)) {
          continue;
        }
        print("  (ite (and (= s1 ");
        printSort(relation._1());
        print(") (= s2 ");
        printSort(s2);
        println(")) true");
        parens++;
      }
    }
    println("  false");
    print("  ");
    for (int i = 0; i < parens; i++) {
      print(")");
    }
    println(")");
    print("(define-fun isValid ((sort Sort)) Bool (or ");
    for (Sort s : sorts) {
      print("(= sort ");
      printSort(s);
      print(")");
    }
    println("))");
    println(PRELUDE2);
  }

  private final List<String> variables = new ArrayList<>();
  private int nextId = 0;
  private int nextVarId = 0;
  private final List<List<String>> variablesById = new ArrayList<>();

  public void push(Term t, Sort topSort, boolean isAnywhere) {
    level++;
    println("(push)");
    ExpectedSortsVisitor viz = new ExpectedSortsVisitor(topSort, isAnywhere);
    viz.apply(t);
    if (variables.isEmpty()) {
        return;
    }
    for (String var : variables) {
      println("(declare-const |" + var + "| Sort)");
    }
    print("(define-fun constraints (");
    for (String var : variables) {
      print("(|" + var + "_| Sort) ");
    }
    println(") Bool (and ");
    for (String var : variables) {
      println("(isValid |" + var + "_|)");
    }
    println(viz.toString());
    println("))");
    print("(define-fun maximal (");
    for (String var : variables) {
      print("(|" + var + "_| Sort) ");
    }
    print(") Bool (not (exists (");
    for (String var : variables) {
      print("(|" + var + "__| Sort) ");
    }
    print(") (and (constraints ");
    for (String var : variables) {
      print("|" + var + "__| ");
    }
    print(") (or ");
    for (String var : variables) {
      print("(<Sort |" + var + "_| |" + var + "__|) ");
    }
    println(")))))");
    print("(assert (constraints ");
    for (String var : variables) {
      print("|" + var + "| ");
    }
    println("))");
    print("(assert (maximal ");
    for (String var : variables) {
      print("|" + var + "| ");
    }
    println("))");
  }

  private static Optional<ProductionReference> getFunction(Term t) {
    if (!(t instanceof ProductionReference)) {
      return Optional.empty();
    }
    ProductionReference child = (ProductionReference)t;
    while (child.production().att().contains("bracket")) {
      if (((TermCons)child).get(0) instanceof Ambiguity) {
        return Optional.empty();
      }
      child = (ProductionReference)((TermCons)child).get(0);
    }
    if (child.production().klabel().isDefined() && child.production().klabel().get().head().equals(KLabels.KREWRITE)) {
      if (((TermCons)child).get(0) instanceof Ambiguity) {
        return Optional.empty();
      }
      child = (ProductionReference)((TermCons)child).get(0);
    }
    while (child.production().att().contains("bracket")) {
      if (((TermCons)child).get(0) instanceof Ambiguity) {
        return Optional.empty();
      }
      child = (ProductionReference)((TermCons)child).get(0);
    }
    return Optional.of(child);
  }

  private static boolean isFunction(Term t, boolean isAnywhere) {
    return getFunction(t).map(pr -> pr.production().att()).orElse(Att()).contains(Attribute.FUNCTION_KEY) || isAnywhere;
  }

  private static Sort getFunctionSort(Term t) {
    return getFunction(t).get().production().sort();
  }

  public class ExpectedSortsVisitor extends SafeTransformer {
    private Sort expectedSort;
    private Optional<ProductionReference> expectedParams = Optional.empty();
    private boolean isStrictEquality = false;
    private final StringBuilder sb = new StringBuilder();
    private final boolean isAnywhere;

    public ExpectedSortsVisitor(Sort topSort, boolean isAnywhere) {
      this.expectedSort = topSort;
      this.isAnywhere = isAnywhere;
    }

    @Override
    public Term apply(Term t) {
      if (t instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)t;
        sb.append("(or ");
        for (Term i : amb.items()) {
            sb.append("(and true ");
            apply(i);
            sb.append(") ");
        }
        sb.append(") ");
        return amb;
      }
      ProductionReference pr = (ProductionReference)t;
 
      boolean isTopSort = expectedSort.equals(Sorts.RuleContent()) || expectedSort.name().equals("#RuleBody");
      int id = nextId;
      if (pr.production().params().nonEmpty()) {
        nextId++;
        variablesById.add(new ArrayList<>());
        pr.setId(Optional.of(id));
      }
      for (Sort param : iterable(pr.production().params())) {
        String name = "FreshVar" + param.name() + (nextVarId++);
        variables.add(name);
        variablesById.get(id).add(name);
      }
      if (pr instanceof TermCons) {
        boolean wasStrict = isStrictEquality;
        Sort oldExpectedSort = expectedSort;
        Optional<ProductionReference> oldExpectedParams = expectedParams;
        TermCons tc = (TermCons)pr;
        for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
          if (tc.production().items().apply(i) instanceof NonTerminal) {
            NonTerminal nt = (NonTerminal)tc.production().items().apply(i);
            expectedSort = nt.sort();
            expectedParams = Optional.of(tc);
            isStrictEquality = false;
            if (tc.production().klabel().isDefined()
                  && (tc.production().klabel().get().name().equals("#SyntacticCast")
                  || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                  || tc.production().klabel().get().name().equals("#InnerCast"))) {
              isStrictEquality = true;
              apply(tc.get(j));
            } else if (isTopSort && j == 0 && isFunction(tc.get(j), isAnywhere)) {
              expectedSort = getFunctionSort(tc.get(j));
              expectedParams = Optional.of(getFunction(tc.get(j)).get());
              apply(tc.get(j));
            } else {
              apply(tc.get(j));
            }
            j++;
          }
        }
        isStrictEquality = wasStrict;
        expectedSort = oldExpectedSort;
        expectedParams = oldExpectedParams;
      }
      if (pr.production().params().nonEmpty()) {
        for (String name : variablesById.get(id)) {
          pushConstraint(name);
        }
      }
      if (pr instanceof Constant && pr.production().sort().equals(Sorts.KVariable())) {
        nextId++;
        variablesById.add(new ArrayList<>());
        pr.setId(Optional.of(id));
        String name;
        if (isAnonVar((Constant)pr)) {
          Location loc = pr.location().get();
          name = "FreshVar" + ((Constant)pr).value() + "_" + loc.startLine() + "_" + loc.startColumn() + "_" + loc.endLine() + "_" + loc.endColumn();
        } else {
          name = "Var" + ((Constant)pr).value();
        }
        if (!variables.contains(name)) {
          variables.add(name);
        }
        variablesById.get(id).add(name);
        pushConstraint(name);
      }
      return pr;
    }

    public boolean isAnonVar(Constant var) {
      return var.value().equals(ResolveAnonVar.ANON_VAR.name()) || var.value().equals(ResolveAnonVar.FRESH_ANON_VAR.name());
    }

    private void pushConstraint(String name) {
      if (isStrictEquality) {
        sb.append("(= ");
      } else {
        sb.append("(<=Sort ");
      }
      sb.append("|").append(name).append("_| ");
      if (mod.subsorts().lessThan(Sorts.K(), expectedSort)) {
          expectedSort = Sorts.K();
      }
      printSort(expectedSort, expectedParams);
      sb.append(") ");
    }

    private void printSort(Sort s, Optional<ProductionReference> t) {
      Map<Sort, String> params = new HashMap<>();
      if (t.isPresent()) {
        if (t.get().production().params().nonEmpty()) {
          int id = t.get().id().get();
          List<String> names = variablesById.get(id);
          Seq<Sort> formalParams = t.get().production().params();
          assert(names.size() == formalParams.size());
          for (int i = 0; i < names.size(); i++) {
            params.put(formalParams.apply(i), names.get(i));
          }
        }
      }
      printSort(s, params);
    }

    private void printSort(Sort s, Map<Sort, String> params) {
      if (params.containsKey(s)) {
        sb.append("|").append(params.get(s)).append("_|");
        return;
      }
      if (s.params().isEmpty()) {
        sb.append("(s Sort" + s.name() + ")");
        return;
      }
      sb.append("(mkSort Sort" + s.name() + " ");
      for (Sort param : iterable(s.params())) {
        sb.append("(cons ");
        printSort(param, params);
      }
      sb.append(" nil");
      for (Sort ignored : iterable(s.params())) {
        sb.append(")");
      }
      sb.append(")");
    }
    
    @Override
    public String toString() {
      return sb.toString();
    }
  }

  private void printSort(Sort s) {
    if (s.params().isEmpty()) {
      print("(s Sort" + s.name() + ")");
    } else {
      print("(mkSort Sort" + s.name() + " ");
      for (Sort param : iterable(s.params())) {
        print("(cons ");
        printSort(param);
      }
      print(" nil");
      for (Sort ignored : iterable(s.params())) {
        print(")");
      }
      print(")");
    }
  }

  private Status computeStatus() {
    println("(check-sat)");
    try {
      String result = output.readLine();
      StringBuilder old = null;
      if (result.equals("sat")) {
        return Status.SATISFIABLE;
      } else if (result.equals("unsat")) {
        return Status.UNSATISFIABLE;
      } else if (result.equals("unknown")) {
        return status.UNKNOWN;
      } else {
        throw KEMException.internalError("Unexpected result from z3: " + result);
      }
    } catch (IOException e) {
      throw KEMException.internalError("Could not read from z3 process", e);
    }
  }

  public Status status() {
    if (status == null) {
     status = computeStatus(); 
    }
    return status;
  }

  public String errorMessage() {
    //TODO: get from Z3
    return "Type inference failed.";
  }

  public void computeModel() {
    for (String var : variables) {
      model.put(var, computeValue(var));
    }
  }

  public void pushNotModel(Term typed) {
    new PrintNotModel().apply(typed);
    print("(assert (not (or (and ");
    for (String var : variables) {
      print("(= |" + var + "| ");
      printSort(model.get(var));
      print(") ");
    }
    print(") ");
    for (String var : variables) {
      print("(");
      if (model.get(var).equals(Sorts.KLabel())) {
        print("distinct");
      } else {
        print("=");
      }
      print(" |" + var + "| ");
      printSort(Sorts.KLabel());
      print(") ");
    }
    println(")))");
    status = null;
  }

  public class PrintNotModel extends SafeTransformer {
    private java.util.Set<String> variables = new HashSet<>();

    @Override
    public Term apply(Term term) {
      if (term instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)term;
        return super.apply(amb);
      }
      ProductionReference pr = (ProductionReference)term;
      if (pr.id().isPresent()) {
        for (String name : variablesById.get(pr.id().get())) {
          variables.add(name);
        }
      }
      return super.apply(pr);
    }
  }

  public Seq<Sort> getArgs(ProductionReference pr) {
    if (pr.id().isPresent()) {
      int id = pr.id().get();
      List<String> names = variablesById.get(id);
      return names.stream().map(this::getValue).collect(Collections.toList());
    } else {
      return Seq();
    }
  }

  private Map<Integer, String> heads;

  private void ensureHeads() {
    if (heads != null)
      return;
    heads = new HashMap<>();
    for (Sort s : sorts) {
      println("(get-value (Sort" + s.name() + "))");
      try {
        String result = output.readLine();
        int startIdx = result.indexOf(' ') + 1;
        int endIdx = result.indexOf(')');
        int value = Integer.parseInt(result.substring(startIdx, endIdx));
        heads.put(value, s.name());
      } catch (IOException e) {
        throw KEMException.internalError("Could not read from z3 process", e);
      }
    }
  }

  private final Map<String, Sort> model = new HashMap<>();

  private Sort getValue(String name) {
    return model.get(name);
  }

  private Sort computeValue(String name) {
    ensureHeads();
    println("(get-value (|" + name + "|))");
    try {
      String result = output.readLine();
      int startIdx = result.indexOf(' ');
      int endIdx = result.length() - 2;
      return new SmtSortParser(new StringReader(result.substring(startIdx, endIdx))).Sort(heads);
    } catch (IOException e) {
      throw KEMException.internalError("Could not read from z3 process", e);
    } catch (ParseException e) {
      throw KEMException.internalError("Failed to parse z3 sort", e);
    }
  }

  public boolean hasNoVariables() {
    return variables.isEmpty();
  }

  public void close() {
    reset();
    z3.close();
    process.destroy();
  }

  private void reset() {
    if (level > 0)
      return;
    if (DEBUG) {
      System.err.print(sb.toString());
      sb = new StringBuilder();
    }
    status = null;
    heads = null;
    model.clear();
    variables.clear();
    variablesById.clear();
    nextId = 0;
    nextVarId = 0;
  }

  static final boolean DEBUG = false;

  private StringBuilder sb = new StringBuilder();

  private void println(String s) {
    if (DEBUG) {
      sb.append(s).append('\n');
    }
    z3.println(s);
    z3.flush();
  }

  private void print(String s) {
    if (DEBUG) {
      sb.append(s);
    }
    z3.print(s);
  }

  int level = 0;

  public void pop() {
    println("(pop)");
    status = null;
    level--;
    if (level == 0) {
      reset();
    }
  }
}
