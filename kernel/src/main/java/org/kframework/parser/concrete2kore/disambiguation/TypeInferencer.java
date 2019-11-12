// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.Collections;
import org.kframework.TopologicalSort;
import org.kframework.attributes.Location;
import org.kframework.attributes.HasLocation;
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
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.ParseFailedException;

import com.google.common.collect.SetMultimap;
import com.google.common.collect.HashMultimap;

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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
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
    "(set-option :timeout 30000)\n" +
    "(set-logic QF_DT)\n";

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
    return !RuleGrammarGenerator.isParserSort(s) || s.equals(Sorts.K()) || s.equals(Sorts.KItem()) || s.equals(Sorts.KLabel()) || s.equals(Sorts.RuleTag());
  }

  public Module module() {
    return mod;
  }

  public void push(Module mod) {
    int i = 0;
    for (Sort s : iterable(TopologicalSort.tsort(mod.syntacticSubsorts().directRelations()))) {
      if (!isRealSort(s)) {
        continue;
      }
      ordinals.put(s, i++);
    }

    print("(declare-datatypes () ((Sort ");
    for (Sort s : sorts) {
      println("|Sort" + s.name() + "| ");
    }
    println(")))");
    println("(define-fun <=Sort ((s1 Sort) (s2 Sort)) Bool (or");
    for (Tuple2<Sort, Set<Sort>> relation : stream(mod.syntacticSubsorts().relations()).sorted(Comparator.comparing(t -> -ordinals.getOrDefault(t._1(), 0))).collect(Collectors.toList())) {
      if (!isRealSort(relation._1())) {
        continue;
      }
      for (Sort s2 : iterable(relation._2())) {
        if (!isRealSort(s2)) {
          continue;
        }
        print("  (and (= s1 ");
        printSort(relation._1());
        print(") (= s2 ");
        printSort(s2);
        println("))");
      }
    }
    for (Sort s : iterable(mod.definedSorts())) {
      if (!isRealSort(s)) {
        continue;
      }
      print("  (and (= s1 ");
      printSort(s);
      print(") (= s2 ");
      printSort(s);
      println("))");
    }
    println("))");
  }

  private final Map<Sort, Integer> ordinals = new HashMap<>();
  private final List<String> variables = new ArrayList<>();
  private final List<String> variableNames = new ArrayList<>();
  private final List<String> parameters = new ArrayList<>();
  private final List<List<String>> variablesById = new ArrayList<>();
  private final List<java.util.Set<String>> cacheById = new ArrayList<>();
  private int nextId = 0;
  private int nextVarId = 0;
  private Term currentTerm;
  private Sort currentTopSort;
  private boolean isAnywhere;

  private static class LocalizedError extends RuntimeException {
    private final Term loc;
    public LocalizedError(String message, Term loc) {
      super(message);
      this.loc = loc;
    }

    public Term getLocation() {
      return loc;
    }
  }

  private void replayConstraints(List<Constraint> constraints) {
    for (Constraint constraint : constraints) {
      println("(push)");
      print("(assert (and ");
      print(constraint.smt);
      println("))");
      status = null;
      Status status = status();
      switch(status) {
      case SATISFIABLE:
        println("(pop)");
        print("(assert (and ");
        print(constraint.smt);
        println("))");
        break;
      case UNKNOWN:
        throw KEMException.internalError("Could not solve sort constraints.", currentTerm);
      case UNSATISFIABLE:
        println("(pop)");
        computeStatus();
        if (constraint.isVar()) {
          Sort actualSort = computeValue(constraint.name);
          Sort expectedSort = eval(constraint.expectedSort, constraint.expectedParams);
          throw new LocalizedError("Unexpected sort " + actualSort + " for variable " + constraint.loc.value() + ". Expected: " + expectedSort, constraint.loc);
        } else {
          Sort actualSort = eval(constraint.actualSort, constraint.actualParams);
          Sort expectedSort = eval(constraint.expectedSort, constraint.expectedParams);
          throw new LocalizedError("Unexpected sort " + actualSort + " for term parsed as production " + constraint.actualParams.get().production() + ". Expected: " + expectedSort, constraint.actualParams.get());
        }
      }
    }
  }

  private void assertNotKLabel() {
    if (!sorts.contains(Sorts.KLabel()))
      return;
    for (String param : parameters) {
      print("(distinct |" + param + "| ");
      printSort(Sorts.KLabel());
      print(") ");
    }
  }

  private KException push() {
    level++;
    println("(push)");
    ExpectedSortsVisitor viz = new ExpectedSortsVisitor(currentTopSort, isAnywhere, true);
    viz.apply(currentTerm);
    for (String var : variables) {
      println("(declare-const |" + var + "| Sort)");
    }
    print("(assert (and true ");
    assertNotKLabel();
    println("))");
    try {
      java.util.Collections.sort(viz.constraints, Comparator.comparing(c -> !c.isVar()));
      replayConstraints(viz.constraints);
      throw KEMException.internalError("Unknown sort inference error.", currentTerm);
    } catch (LocalizedError e) {
      return new KException(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, e.getMessage(), e.getLocation().source().orElse(null), e.getLocation().location().orElse(null));
    }
  }

  public void push(Term t, Sort topSort, boolean isAnywhere) {
    currentTerm = t;
    currentTopSort = topSort;
    this.isAnywhere = isAnywhere;
    level+=2;
    println("(push)");
    ExpectedSortsVisitor viz = new ExpectedSortsVisitor(topSort, isAnywhere, false);
    String id = viz.apply(t);
    if (variables.isEmpty()) {
        return;
    }
    for (String var : variables) {
      println("(declare-const |" + var + "| Sort)");
    }
    print("(assert (and true ");
    assertNotKLabel();
    println("))");
    println(viz.toString());
    println("(assert " + id + ")");
    println("(push)");
    for (String var : variables) {
      if (mod.definedSorts().contains(Sorts.K()))
        println("(assert-soft (= SortK |" + var + "|) :weight 2 :id A)");
      if (mod.definedSorts().contains(Sorts.KItem()))
        println("(assert-soft (= SortKItem |" + var + "|) :weight 1 :id A)");
      if (mod.definedSorts().contains(Sorts.Bag()))
        println("(assert-soft (<=Sort SortBag |" + var + "|) :weight 1 :id A)");
    }
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

  private static Sort getSortOfCast(TermCons tc) {
    switch (tc.production().klabel().get().name()) {
    case "#SyntacticCast":
    case "#OuterCast":
      return tc.production().sort();
    case "#InnerCast":
      return ((NonTerminal)tc.production().items().apply(1)).sort();
    default:
      if (tc.production().klabel().get().name().startsWith("#SemanticCastTo")) {
        return tc.production().sort();
      }
      throw new AssertionError("Unexpected cast type");
    }
  }

  public static class Constraint {
    public final String smt;
    public final String name;
    public final Constant loc;
    public final Sort expectedSort;
    public final Optional<ProductionReference> expectedParams;
    public final Sort actualSort;
    public final Optional<ProductionReference> actualParams;

    public Constraint(String smt, String name, Constant loc, Sort expectedSort, Optional<ProductionReference> expectedParams) {
      this.smt = smt;
      this.name = name;
      this.loc = loc;
      this.expectedSort = expectedSort;
      this.expectedParams = expectedParams;
      this.actualSort = null;
      this.actualParams = null;
    }

    public Constraint(String smt, Sort actualSort, Optional<ProductionReference> actualParams, Sort expectedSort, Optional<ProductionReference> expectedParams) {
      this.smt = smt;
      this.name = null;
      this.loc = null;
      this.actualSort = actualSort;
      this.actualParams = actualParams;
      this.expectedSort = expectedSort;
      this.expectedParams = expectedParams;
    }

    public boolean isVar() {
      return name != null || actualParams.get().production().params().contains(actualSort);
    }
  }

  public class ExpectedSortsVisitor {
    private Sort expectedSort;
    private Optional<ProductionReference> expectedParams = Optional.empty();
    private boolean isStrictEquality = false;
    private StringBuilder sb = new StringBuilder();
    private final boolean isAnywhere;
    private final boolean isIncremental;

    private int ambId = 0;

    private Map<Ambiguity, Map<String, Integer>> ambCache = new IdentityHashMap<>();

    public ExpectedSortsVisitor(Sort topSort, boolean isAnywhere, boolean isIncremental) {
      this.expectedSort = topSort;
      this.isAnywhere = isAnywhere;
      this.isIncremental = isIncremental;
    }

    public String apply(Term t) {
      if (t instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)t;
        if (isIncremental) {
          return apply(amb.items().iterator().next());
        }
        String expected = printSort(expectedSort, expectedParams, false).replace("|", "");
        Map<String, Integer> contexts = ambCache.computeIfAbsent(amb, amb2 -> new HashMap<>());
        int id = contexts.computeIfAbsent(expected, expected2 -> ambId);
        boolean cached = id != ambId;
        if (!cached) {
          ambId++;
          List<String> ids = new ArrayList<>();
          for (Term i : amb.items()) {
            ids.add(apply(i));
          }
          sb.append("(define-fun amb").append(id).append(" () Bool (or ");
          for (String i : ids) {
            sb.append(i).append(" ");
          }
          sb.append("))\n");
        }
        return "amb" + id;
      }
      ProductionReference pr = (ProductionReference)t;
      List<String> ids = new ArrayList<>();
      boolean isTopSort = expectedSort.equals(Sorts.RuleContent()) || expectedSort.name().equals("#RuleBody");
      int id = nextId;
      boolean shared = pr.id().isPresent() && variablesById.size() > pr.id().get();
      if (!shared) {
        nextId++;
        variablesById.add(new ArrayList<>());
        cacheById.add(new HashSet<>());
        pr.setId(Optional.of(id));
        for (Sort param : iterable(pr.production().params())) {
          String name = "FreshVar" + param.name() + (nextVarId++);
          if (!variables.contains(name)) {
            variables.add(name);
            variableNames.add(param.name() + " in production " + pr.production().toString());
            parameters.add(name);
          }
          variablesById.get(id).add(name);
        }
      } else {
        id = pr.id().get();
      }
      if (pr instanceof TermCons) {
        boolean wasStrict = isStrictEquality;
        Sort oldExpectedSort = expectedSort;
        Optional<ProductionReference> oldExpectedParams = expectedParams;
        TermCons tc = (TermCons)pr;
        for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
          if (tc.production().items().apply(i) instanceof NonTerminal) {
            NonTerminal nt = (NonTerminal)tc.production().items().apply(i);
            expectedParams = Optional.of(tc);
            isStrictEquality = false;
            if (tc.production().klabel().isDefined()
                  && (tc.production().klabel().get().name().equals("#SyntacticCast")
                  || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                  || tc.production().klabel().get().name().equals("#InnerCast"))) {
              expectedSort = getSortOfCast(tc);
              isStrictEquality = tc.production().klabel().get().name().equals("#SyntacticCast")
                  || tc.production().klabel().get().name().equals("#InnerCast");
              ids.add(apply(tc.get(j)));
            } else if (isTopSort && j == 0 && isFunction(tc.get(j), isAnywhere)) {
              expectedSort = getFunctionSort(tc.get(j));
              expectedParams = Optional.of(getFunction(tc.get(j)).get());
              ids.add(apply(tc.get(j)));
            } else {
              expectedSort = nt.sort();
              ids.add(apply(tc.get(j)));
            }
            j++;
          }
        }
        isStrictEquality = wasStrict;
        expectedSort = oldExpectedSort;
        expectedParams = oldExpectedParams;
      }
      String expected = printSort(expectedSort, expectedParams, false).replace("|", "");
      boolean cached = !cacheById.get(id).add(expected);
      if (!isIncremental && (!shared || !cached)) {
        sb.append("(define-fun |constraint").append(id).append("_").append(expected).append("| () Bool (and true ");
      }
      if (isIncremental || !shared || !cached) {
        if (pr instanceof Constant && (pr.production().sort().equals(Sorts.KVariable()) || pr.production().sort().equals(Sorts.KConfigVar()))) {
          Constant c = (Constant) pr;
          String name;
          if (!shared) {
            nextId++;
            variablesById.add(new ArrayList<>());
            cacheById.add(new HashSet<>());
            pr.setId(Optional.of(id));
            if (isAnonVar(c)) {
              name = "Var" + c.value() + (nextVarId++);
            } else {
              name = "Var" + c.value();
            }
            if (!variables.contains(name)) {
              variables.add(name);
              variableNames.add(c.value());
            }
            variablesById.get(id).add(name);
          } else {
            name = variablesById.get(id).get(0);
          }
          Sort actualSort = null;
          pushConstraint(name, c);
        } else if (isRealSort(pr.production().sort())) {
          pushConstraint(pr.production().sort(), Optional.of(pr));
        }
      }
      if (!isIncremental && (!shared ||  !cached)) {
        for (String i : ids) {
          sb.append(i).append(" ");
        }
        sb.append("))\n");
      }
      return "|constraint" + id + "_" + expected + "|";
    }

    public boolean isAnonVar(Constant var) {
      return var.value().equals(ResolveAnonVar.ANON_VAR.name()) || var.value().equals(ResolveAnonVar.FRESH_ANON_VAR.name());
    }

    private void pushConstraint(Sort actualSort, Optional<ProductionReference> actualParams) {
      if (mod.subsorts().lessThanEq(actualSort, Sorts.KBott()) || mod.subsorts().lessThan(Sorts.K(), actualSort)) {
        return;
      }
      if (isStrictEquality) {
        sb.append("(= ");
      } else {
        sb.append("(<=Sort ");
      }
      sb.append(printSort(actualSort, actualParams, isIncremental));
      sb.append(" ");
      if (mod.subsorts().lessThan(Sorts.K(), expectedSort)) {
        expectedSort = Sorts.K();
      }
      sb.append(printSort(expectedSort, expectedParams, isIncremental));
      sb.append(") ");
      if (isIncremental) {
        saveConstraint(actualSort, actualParams);
      }
    }

    private void pushConstraint(String name, Constant loc) {
      if (isStrictEquality) {
        sb.append("(= ");
      } else {
        sb.append("(<=Sort ");
      }
      sb.append("|").append(name).append("| ");
      if (mod.subsorts().lessThan(Sorts.K(), expectedSort)) {
          expectedSort = Sorts.K();
      }
      sb.append(printSort(expectedSort, expectedParams, isIncremental));
      sb.append(") ");
      if (isIncremental) {
        saveConstraint(name, loc);
      }
    }

    List<Constraint> constraints = new ArrayList<>();

    private void saveConstraint(String name, Constant loc) {
      constraints.add(new Constraint(sb.toString(), name, loc, expectedSort, expectedParams));
      sb = new StringBuilder();
    }

    private void saveConstraint(Sort actualSort, Optional<ProductionReference> actualParams) {
      constraints.add(new Constraint(sb.toString(), actualSort, actualParams, expectedSort, expectedParams));
      sb = new StringBuilder();
    }

    @Override
    public String toString() {
      return sb.toString();
    }
  }

  private String printSort(Sort s, Optional<ProductionReference> t, boolean isIncremental) {
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
    return printSort(s, params, isIncremental);
  }

  private String printSort(Sort s, Map<Sort, String> params, boolean isIncremental) {
    StringBuilder sb = new StringBuilder();
    if (params.containsKey(s)) {
      sb.append("|").append(params.get(s)).append("|");
      return sb.toString();
    }
    if (s.params().isEmpty()) {
      sb.append("|Sort" + s.name() + "|");
      return sb.toString();
    }
    sb.append("(|Sort" + s.name() + "|");
    for (Sort param : iterable(s.params())) {
      sb.append(" ");
      sb.append(printSort(param, params, isIncremental));
    }
    sb.append(")");
    return sb.toString();
  }

  private void printSort(Sort s) {
    if (s.params().isEmpty()) {
      print("|Sort" + s.name() + "|");
    } else {
      print("(|Sort" + s.name() + "|");
      for (Sort param : iterable(s.params())) {
        print(" ");
        printSort(param);
      }
      print(")");
    }
  }

  private Status computeStatus() {
    println("(check-sat)");
    try {
      String result;
      do {
        result = output.readLine();
      } while (!result.equals("sat") && !result.equals("unsat") && !result.equals("unknown") && !result.startsWith("(error"));
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

  public java.util.Set<ParseFailedException> error(List<Map<String, Sort>> models) {
    SetMultimap<String, Sort> grouped = HashMultimap.create();
    for (Map<String, Sort> model : models) {
      for (Map.Entry<String, Sort> entry : model.entrySet()) {
        grouped.put(entry.getKey(), entry.getValue());
      }
    }
    java.util.Set<ParseFailedException> result = new HashSet<>();
    int i = 0;
    for (String var : variables) {
      if (grouped.get(var).size() > 1) {
        result.add(new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, "Could not infer a unique sort for variable " + variableNames.get(i) + ". Possible sorts: " + grouped.get(var), currentTerm.source().orElse(null), currentTerm.location().orElse(null))));
      }
      i++;
    }
    if(!result.isEmpty()) {
      return result;
    }
    throw KEMException.internalError("Unknown sort inference error.", currentTerm);
  }

  public java.util.Set<ParseFailedException> error() {
    pop();
    return java.util.Collections.singleton(new ParseFailedException(push()));
  }

  public void computeModel() {
    for (String var : variables) {
      model.put(var, computeValue(var));
    }
  }

  public void selectModel(Map<String, Sort> model) {
    this.model.clear();
    this.model.putAll(model);
  }

  public Map<String, Sort> getModel() {
    return new HashMap<>(model);
  }

  public void pushNotModel() {
    print("(assert (not (and true");
    java.util.Set<String> realVariables = new HashSet<>(variables);
    realVariables.removeAll(parameters);
    for (String var : realVariables) {
      print("(<=Sort   |" + var + "| ");
      printSort(model.get(var));
      print(") ");
    }
    print(")))");
    status = null;
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

  private final Map<String, Sort> model = new HashMap<>();

  private Sort getValue(String name) {
    return model.get(name);
  }

  private Sort eval(Sort s, Optional<ProductionReference> params) {
    print("(eval ");
    print(printSort(s, params, true));
    println(")");
    return readSort(false);
  }

  private Sort computeValue(String name) {
    println("(get-value (|" + name + "|))");
    return readSort(true);
  }

  private Sort readSort(boolean trim) {
    try {
      String result = output.readLine();
      if (trim) {
        int startIdx = result.indexOf(' ');
        int endIdx = result.length() - 2;
        result = result.substring(startIdx, endIdx);
      }
      return new SmtSortParser(new StringReader(result)).Sort();
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
    model.clear();
    variables.clear();
    variableNames.clear();
    parameters.clear();
    variablesById.clear();
    cacheById.clear();
    ordinals.clear();
    nextId = 0;
    nextVarId = 0;
  }

  private static final String locStr(ProductionReference pr) {
    String suffix = "";
    if (pr.production().klabel().isDefined()) {
      suffix = "_" + pr.production().klabel().get().name().replace("|","");
    }
    if (pr.location().isPresent()) {
      Location l = pr.location().get();
      return "_" + l.startLine() + "_" + l.startColumn() + "_" + l.endLine() + "_" + l.endColumn() + suffix;
    }
    return Integer.toString(pr.id().get()) + suffix;
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
