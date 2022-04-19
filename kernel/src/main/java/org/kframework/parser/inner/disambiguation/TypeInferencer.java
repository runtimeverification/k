// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import org.kframework.POSet;
import org.kframework.attributes.Att;
import org.kframework.Collections;
import org.kframework.TopologicalSort;
import org.kframework.attributes.Location;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KEMException;

import scala.collection.Seq;
import scala.collection.Set;
import scala.Tuple2;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.PrintStream;
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

/**
 * Class to manage communication with z3 for the purposes of type inference. This class is driven by
 * {@link TypeInferenceVisitor} and handles all the communication to/from z3 as well as construction of constraints.
 *
 * For a description of the algorithm, see the companion class's javadoc.
 */
public class TypeInferencer implements AutoCloseable {

  public enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    UNKNOWN
  }

  private Status status = null;

  private Process process;
  private PrintStream z3;
  private BufferedReader output;
  private final Module mod;
  private final java.util.Set<SortHead> sorts;

  // logic QF_DT is best if it exists as it will be faster than ALL. However, some z3 versions do not have this logic.
  // Fortunately, z3 ignores unknown logics.
  private static final String PRELUDE1 =
    "(set-logic QF_DT)\n";

  private final boolean destroyOnReset;

  private void initProcess() {
    try {
      File NULL = new File(OS.current() == OS.WINDOWS ? "NUL" : "/dev/null");
      process = new ProcessBuilder().command("z3", "-in").redirectError(NULL).start();
    } catch (IOException e) {
      throw KEMException.criticalError("Could not start z3 process", e);
    }
    z3 = new PrintStream(process.getOutputStream());
    output = new BufferedReader(new InputStreamReader(process.getInputStream()));
  }

  /**
   * Create a new z3 process and write the sorts and subsort relation to it.
   * @param mod the module to create an inferencer for.
   */
  public TypeInferencer(Module mod) {
    initProcess();
    println("(get-info :version)");
    try {
        String version = output.readLine();
        version = version.substring("(:version \"".length());
        version = version.substring(0, version.indexOf('"'));
        String[] parts = version.split("\\.");
        // example of version string:
        // "4.8.8 - build hashcode ad55a1f1c617"
        int major = Integer.valueOf(parts[0]);
        int minor = Integer.valueOf(parts[1]);
        int patch = Integer.valueOf(parts[2].split(" ")[0]);
        if (major < 4 || (major == 4 && minor < 6) || (major == 4 && minor == 8 && patch == 9)) {
          destroyOnReset = true;
        } else {
          destroyOnReset = false;
        }
    } catch (IOException e) {
      throw KEMException.internalError("Could not read from z3 process", e);
    }
    println(PRELUDE1);
    this.mod = mod;
    this.sorts = stream(mod.definedSorts()).filter(this::isRealSort).collect(Collectors.toSet());
    push(mod);
  }

  // returns whether a particular sort should be written to z3 and thus be a possible sort for variables.
  private boolean isRealSort(SortHead head) {
    if (head.params() > 0) {
      return true;
    }
    Sort s = Sort(head);
    return !RuleGrammarGenerator.isParserSort(s) || s.equals(Sorts.K()) || s.equals(Sorts.KItem()) || s.equals(Sorts.KLabel()) || s.equals(Sorts.RuleTag()) || s.isNat();
  }

  public Module module() {
    return mod;
  }

  /**
   * Writes the prelude for a particular module.
   * @param mod
   */
  private void push(Module mod) {
    // declare Sort datatype
    print("(declare-datatypes () ((Sort ");
    for (SortHead s : sorts) {
      print("(|Sort" + s.name() + "| ");
      for (int i = 0; i < s.params(); i++) {
        print("(|Sort" + s.name() + "_" + i++ + "| Sort) ");
      }
      println(")");
    }
    println(")))");
    makeSubsorts(mod, "<=Sort", mod.subsorts());
    makeSubsorts(mod, "<=SortSyntax", mod.syntacticSubsorts());

    if (DEBUG) {
      debugPrelude = sb.toString();
    }
  }

  private void makeSubsorts(Module mod, String name, POSet<Sort> relations) {
    // map from each sort to an integer representing the topological sorting of the sorts. higher numbers mean greater
    // sorts
    Map<SortHead, Integer> ordinals = new HashMap<>();
    int i = 0;

    for (Sort s : iterable(relations.sortedElements())) {
      if (!isRealSort(s.head())) {
        continue;
      }
      ordinals.put(s.head(), i++);
    }
    // provide fixed interpretation of subsort relation
    println("(define-fun " + name + " ((s1 Sort) (s2 Sort)) Bool (or");
    for (Tuple2<Sort, Set<Sort>> relation : stream(relations.relations()).sorted(Comparator.comparing(t -> -ordinals.getOrDefault(t._1().head(), 0))).collect(Collectors.toList())) {
      if (!isRealSort(relation._1().head())) {
        continue;
      }
      for (Sort s2 : iterable(relation._2())) {
        if (!isRealSort(s2.head())) {
          continue;
        }
        print("  (and (= s1 ");
        printSort(relation._1());
        print(") (= s2 ");
        printSort(s2);
        println("))");
      }
    }
    // reflexive relations
    for (Sort s : iterable(mod.allSorts())) {
      if (!isRealSort(s.head())) {
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

  private String debugPrelude;

  // list of names for variables and sort parameters in z3
  private final List<String> variables = new ArrayList<>();
  // list of names for sort parameters only in z3
  private final List<String> parameters = new ArrayList<>();
  // array mapping from integer id of terms to the list of names of their variable or sort parameters in z3
  private final List<List<String>> variablesById = new ArrayList<>();
  // array mapping from integer id of terms to the expected sorts they have appeared under so far
  private final List<java.util.Set<String>> cacheById = new ArrayList<>();
  private int nextId = 0;
  private Term currentTerm;
  private Sort currentTopSort;
  private boolean isAnywhere;

  private static class LocalizedError extends RuntimeException {
    private final Term loc;
    LocalizedError(String message, Term loc) {
      super(message);
      this.loc = loc;
    }

    public Term getLocation() {
      return loc;
    }
  }

  /**
   * Replays a list of {@link Constraint} one at a time and throws an exception with the error message explaining
   * why the constraints are not satisfied.
   * @param constraints
   */
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
        if (constraint.name != null) {
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

  /**
   * Asserts that none of the sort parameters are of the KLabel sort.
   */
  private void assertNotKLabel() {
    if (!sorts.contains(Sorts.KLabel().head()))
      return;
    for (String param : parameters) {
      print("(distinct |" + param + "| ");
      printSort(Sorts.KLabel());
      print(") ");
    }
  }

  /**
   * Uses z3 to compute the error message associated with a badly typed term.
   * @return
   */
  private KEMException push() {
    level++;
    println("(push)");
    // compute constraints in incremental mode
    ExpectedSortsVisitor viz = new ExpectedSortsVisitor(currentTopSort, isAnywhere, true);
    viz.apply(currentTerm);
    // declare variables
    for (String var : variables) {
      println("(declare-const |" + var + "| Sort)");
    }
    //assert sort parameters are not sort KLabel.
    print("(assert (and true ");
    assertNotKLabel();
    println("))");
    try {
      // sort constraints with upper bounds first
      viz.constraints.sort(Comparator.comparing(c -> !c.isVar()));
      replayConstraints(viz.constraints);
      // should not reach here.
      throw KEMException.internalError("Unknown sort inference error.", currentTerm);
    } catch (LocalizedError e) {
      return KEMException.innerParserError(e.getMessage(), e.getLocation());
    }
  }

  /**
   * write constraints to z3 for a term.
   * @param t The term to compute constraints for.
   * @param topSort The expected sort at the top of the term.
   * @param isAnywhere Whether the term is an anywhere rule.
   */
  public void push(Term t, Sort topSort, boolean isAnywhere) {
    currentTerm = t;
    currentTopSort = topSort;
    this.isAnywhere = isAnywhere;
    level+=2;
    println("(push)");
    // compute constraints in non-incremental mode
    ExpectedSortsVisitor viz = new ExpectedSortsVisitor(topSort, isAnywhere, false);
    String id = viz.apply(t);
    if (variables.isEmpty()) {
        // there are no variables. so return as there is nothing to infer.
        return;
    }
    // declare variables and sort parameters
    for (String var : variables) {
      println("(declare-const |" + var + "| Sort)");
    }
    // assert sort parameters are not KLabel
    print("(assert (and true ");
    assertNotKLabel();
    println("))");
    // write constraint declarations
    println(viz.toString());
    // assert top constraint
    println("(assert " + id + ")");
    println("(push)");
    // soft assertions to cut down search space
    for (String var : variables) {
      if (mod.allSorts().contains(Sorts.K()))
        println("(assert-soft ( <=Sort SortK |" + var + "|) :id A)");
      if (mod.allSorts().contains(Sorts.KItem()))
        println("(assert-soft ( <=Sort SortKItem |" + var + "|) :id A)");
      if (mod.allSorts().contains(Sorts.Bag()))
        println("(assert-soft (<=Sort SortBag |" + var + "|) :id A)");
    }
  }

  /**
   * Returns the top term on the lhs of a rule, if one exists.
   * @param t
   * @return
   */
  private static Optional<ProductionReference> getFunction(Term t) {
    if (!(t instanceof ProductionReference)) {
      return Optional.empty();
    }
    ProductionReference child = (ProductionReference)t;
    while (child.production().att().contains(Att.BRACKET())) {
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
    while (child.production().att().contains(Att.BRACKET())) {
      if (((TermCons)child).get(0) instanceof Ambiguity) {
        return Optional.empty();
      }
      child = (ProductionReference)((TermCons)child).get(0);
    }
    return Optional.of(child);
  }

  /**
   * Returns true if a rule is a function or anywhere rule.
   * @param t
   * @param isAnywhere
   * @return
   */
  private static boolean isFunction(Term t, boolean isAnywhere) {
    return getFunction(t).map(pr -> pr.production().att()).orElse(Att()).contains(Att.FUNCTION()) || isAnywhere;
  }

  /**
   * Returns return sort of a function or anywhere rule.
   * @param t
   * @return
   */
  private static Sort getFunctionSort(Term t) {
    return getFunction(t).get().production().sort();
  }

  /**
   * Returns the declared of a cast.
   * @param tc
   * @return
   */
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

  /**
   * A z3 constraint to be replayed later.
   */
  public static class Constraint {
    public final String smt;
    public final String name;
    public final Constant loc;
    public final Sort expectedSort;
    final Optional<ProductionReference> expectedParams;
    final Sort actualSort;
    final Optional<ProductionReference> actualParams;

    /**
     * Creates an upper bound constraint on a variable.
     * @param smt The smtlib of the constraint
     * @param name The name of the variable
     * @param loc The variable
     * @param expectedSort The upper bound on the variable.
     * @param expectedParams The term that provided that upper bound.
     */
    public Constraint(String smt, String name, Constant loc, Sort expectedSort, Optional<ProductionReference> expectedParams) {
      this.smt = smt;
      this.name = name;
      this.loc = loc;
      this.expectedSort = expectedSort;
      this.expectedParams = expectedParams;
      this.actualSort = null;
      this.actualParams = null;
    }

    /**
     * Creates a constraint that an actual sort is less than or equal to an expected sort.
     * @param smt The smtlib of the constraint
     * @param actualSort The actual sort of the term.
     * @param actualParams The term
     * @param expectedSort The expected sort of the term.
     * @param expectedParams The term that provided that expected sort.
     */
    public Constraint(String smt, Sort actualSort, Optional<ProductionReference> actualParams, Sort expectedSort, Optional<ProductionReference> expectedParams) {
      this.smt = smt;
      this.name = null;
      this.loc = null;
      this.actualSort = actualSort;
      this.actualParams = actualParams;
      this.expectedSort = expectedSort;
      this.expectedParams = expectedParams;
    }

    /**
     * Returns true if a constraint is an upper bound on a variable.
     * @return
     */
    public boolean isVar() {
      return name != null || actualParams.get().production().params().contains(actualSort);
    }
  }

  /**
   * Computes the smtlib constraints for a term by traversing it and creating a set of declarations that capture the
   * sort constraints.
   */
  public class ExpectedSortsVisitor {
    private Sort expectedSort;
    private Optional<ProductionReference> expectedParams = Optional.empty();
    private boolean isStrictEquality = false;
    private StringBuilder sb = new StringBuilder();
    private final boolean isAnywhere;
    private final boolean isIncremental;

    private int ambId = 0;

    // cache for sharing ambiguity nodes
    private Map<Ambiguity, Map<String, Integer>> ambCache = new IdentityHashMap<>();

    /**
     *
     * @param topSort Expected sort at top of term.
     * @param isAnywhere true if the term is an anywhere rule.
     * @param isIncremental true if we should compute the constraints as a list of {@link Constraint}
     */
    ExpectedSortsVisitor(Sort topSort, boolean isAnywhere, boolean isIncremental) {
      this.expectedSort = topSort;
      this.isAnywhere = isAnywhere;
      this.isIncremental = isIncremental;
    }

    /**
     * Generate constraints for a term and accumulate them either in sb if in non-incremental mode, or in constraints
     * if in incremental model.
     * @param t The term to generate constraints for.
     * @return the name of the function generated by this term in non-incremental mode that captures the constraints of
     * this term.
     */
    public String apply(Term t) {
      if (t instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)t;
        if (isIncremental) {
          // we are error checking an ill typed term, so we pick just one branch of the ambiguity and explain why it is
          // ill typed.
          return apply(amb.items().iterator().next());
        }
        // compute name of expected sort for use in cache.
        String expected = printSort(expectedSort, expectedParams, false).replace("|", "");
        Map<String, Integer> contexts = ambCache.computeIfAbsent(amb, amb2 -> new HashMap<>());
        int id = contexts.computeIfAbsent(expected, expected2 -> ambId);
        boolean cached = id != ambId;
        if (!cached) {
          // if this is the first time reaching this ambiguity node with this expected sort, define a new function
          // with a disjunction of each of the children of the ambiguity.
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
        // return name of created or cached function
        return "amb" + id;
      }
      ProductionReference pr = (ProductionReference)t;
      List<String> ids = new ArrayList<>();
      boolean isTopSort = expectedSort.equals(Sorts.RuleContent()) || expectedSort.name().equals("#RuleBody");
      int id = nextId;
      boolean shared = pr.id().isPresent() && variablesById.size() > pr.id().get();
      if (!shared) {
        // if this is the first time reaching this term, initialize data structures with the variables associated with
        // this term.
        nextId++;
        variablesById.add(new ArrayList<>());
        cacheById.add(new HashSet<>());
        pr.setId(Optional.of(id));
        for (Sort param : iterable(pr.production().params())) {
          String name = "FreshVar" + param.name() + locStr(pr);
          if (!variables.contains(name)) {
            variables.add(name);
            parameters.add(name);
          }
          variablesById.get(id).add(name);
        }
      } else {
        // get cached id
        id = pr.id().get();
      }
      if (pr instanceof TermCons) {
        boolean wasStrict = isStrictEquality;
        Sort oldExpectedSort = expectedSort;
        Optional<ProductionReference> oldExpectedParams = expectedParams;
        TermCons tc = (TermCons)pr;
        // traverse children
        for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
          if (tc.production().items().apply(i) instanceof NonTerminal) {
            NonTerminal nt = (NonTerminal)tc.production().items().apply(i);
            expectedParams = Optional.of(tc);
            isStrictEquality = false;
            // compute expected sort and whether this is a cast
            if (tc.production().klabel().isDefined()
                  && (tc.production().klabel().get().name().equals("#SyntacticCast")
                  || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                  || tc.production().klabel().get().name().equals("#InnerCast"))) {
              expectedSort = getSortOfCast(tc);
              isStrictEquality = tc.production().klabel().get().name().equals("#SyntacticCast")
                  || tc.production().klabel().get().name().equals("#InnerCast");
              if (tc.get(0) instanceof Constant) {
                Constant child = (Constant)tc.get(0);
                if (child.production().sort().equals(Sorts.KVariable()) || child.production().sort().equals(Sorts.KConfigVar())) {
                  isStrictEquality = true;
                }
              }
            } else if (isTopSort && j == 0 && isFunction(tc.get(j), isAnywhere)) {
              expectedSort = getFunctionSort(tc.get(j));
              expectedParams = Optional.of(getFunction(tc.get(j)).get());
            } else {
              expectedSort = nt.sort();
            }
            // recurse and add name of function generated by child to the current children of this constraint.
            ids.add(apply(tc.get(j)));
            j++;
          }
        }
        isStrictEquality = wasStrict;
        expectedSort = oldExpectedSort;
        expectedParams = oldExpectedParams;
      }
      // compute name of expected sort for use in cache.
      String expected = printSort(expectedSort, expectedParams, false).replace("|", "");
      boolean cached = !cacheById.get(id).add(expected);
      if (!isIncremental && (!shared || !cached)) {
        // if we are in non-incremental mode and this is the first time reaching this term under this expected sort,
        // define a new function with a conjunction of each of the children of the term and the constraints of the
        // current term.
        sb.append("(define-fun |constraint").append(id).append("_").append(expected).append("| () Bool (and true ");
      }
      if (isIncremental || !shared || !cached) {
        // if we are in incremental mode or this is the first time reaching this term under this expected sort,
        // compute the local constraints of this term and add them to the current constraint.
        if (pr instanceof Constant && (pr.production().sort().equals(Sorts.KVariable()) || pr.production().sort().equals(Sorts.KConfigVar()))) {
          Constant c = (Constant) pr;
          String name;
          boolean oldStrictEquality = isStrictEquality;
          if (!shared) {
            nextId++;
            variablesById.add(new ArrayList<>());
            cacheById.add(new HashSet<>());
            pr.setId(Optional.of(id));
            if (isAnonVar(c)) {
              name = "Var" + c.value() + locStr(c);
              isStrictEquality = true;
            } else {
              name = "Var" + c.value();
            }
            if (!variables.contains(name)) {
              variables.add(name);
            }
            variablesById.get(id).add(name);
          } else {
            name = variablesById.get(id).get(0);
          }
          pushConstraint(name, c);
          isStrictEquality = oldStrictEquality;
        } else if (isRealSort(pr.production().sort().head())) {
          pushConstraint(pr.production().sort(), Optional.of(pr));
        }
      }
      if (!isIncremental && (!shared ||  !cached)) {
        for (String i : ids) {
          sb.append(i).append(" ");
        }
        sb.append("))\n");
      }
      // return name of created or cached constraint.
      return "|constraint" + id + "_" + expected + "|";
    }

    boolean isAnonVar(Constant var) {
      return ResolveAnonVar.isAnonVarOrNamedAnonVar(KVariable(var.value()));
    }

    /**
     * Add a constraint that an actual sort is less than an expected sort.
     * @param actualSort
     * @param actualParams
     */
    private void pushConstraint(Sort actualSort, Optional<ProductionReference> actualParams) {
      if (mod.subsorts().lessThanEq(actualSort, Sorts.KBott()) || mod.subsorts().lessThan(Sorts.K(), actualSort)) {
        return;
      }
      if (isBadNatSort(actualSort)) {
        sb.append("false ");
      } else {
        if (isStrictEquality || actualParams.get().production().params().contains(actualSort)) {
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
      }
      if (isIncremental) {
        saveConstraint(actualSort, actualParams);
      }
    }

    /**
     * Add a constraint that a variable is less than an expected sort.
     * @param name
     * @param loc
     */
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

  private boolean isBadNatSort(Sort actualSort) {
    if (actualSort.isNat() && !mod.definedSorts().contains(actualSort.head())) return true;
    return stream(actualSort.params()).anyMatch(this::isBadNatSort);
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
      sb.append("|Sort").append(s.name()).append("|");
      return sb.toString();
    }
    sb.append("(|Sort").append(s.name()).append("|");
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

  /**
   * Check satisfiability of current assertions and return status.
   * @return
   */
  private Status computeStatus() {
    println("(check-sat)");
    try {
      String result;
      do {
        result = output.readLine();
        if (result == null) {
            throw KEMException.internalError("Unexpected EOF reached while waiting for response from z3.", currentTerm);
        }
      } while (!result.equals("sat") && !result.equals("unsat") && !result.equals("unknown") && !result.equals("timeout") && !result.startsWith("(error"));
      switch (result) {
      case "sat":
        return Status.SATISFIABLE;
      case "unsat":
        return Status.UNSATISFIABLE;
      case "unknown":
      case "timeout":
        return Status.UNKNOWN;
      default:
        throw KEMException.internalError("Unexpected result from z3: " + result, currentTerm);
      }
    } catch (IOException e) {
      throw KEMException.internalError("Could not read from z3 process", e, currentTerm);
    }
  }

  /**
   * Check satisfiability of current assertions and return status, cached if called multiple times.
   * @return
   */
  public Status status() {
    if (status == null) {
     status = computeStatus();
    }
    return status;
  }

  public java.util.Set<KEMException> error() {
    pop();
    return java.util.Collections.singleton(push());
  }

  void computeModel() {
    for (String var : variables) {
      model.put(var, computeValue(var));
    }
  }

  void selectModel(Map<String, Sort> model) {
    this.model.clear();
    this.model.putAll(model);
  }

  public Map<String, Sort> getModel() {
    return new HashMap<>(model);
  }

  void pushNotModel() {
    print("(assert (not (and true");
    java.util.Set<String> realVariables = new HashSet<>(variables);
    realVariables.removeAll(parameters);
    for (String var : realVariables) {
      print("(<=SortSyntax   |" + var + "| ");
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
    if (isBadNatSort(s)) return s;
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
      Sort r = new SmtSortParser(new StringReader(result)).Sort();
      if (DEBUG)
        sb.append("; ").append(r).append("\n");
      return r;
    } catch (IOException e) {
      throw KEMException.internalError("Could not read from z3 process", e, currentTerm);
    } catch (ParseException e) {
      throw KEMException.internalError("Failed to parse z3 sort", e, currentTerm);
    }
  }

  boolean hasNoVariables() {
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
    parameters.clear();
    variablesById.clear();
    cacheById.clear();
    nextId = 0;
    if (destroyOnReset) {
      z3.close();
      process.destroy();
      initProcess();
      println(PRELUDE1);
      push(mod);
    }
  }

  private static String locStr(ProductionReference pr) {
    String suffix = "";
    if (pr.production().klabel().isDefined()) {
      suffix = "_" + pr.production().klabel().get().name().replace("|","");
    }
    if (pr.location().isPresent()) {
      Location l = pr.location().get();
      return "_" + l.startLine() + "_" + l.startColumn() + "_" + l.endLine() + "_" + l.endColumn() + suffix;
    }
    return pr.id().get() + suffix;
  }

  private static final boolean DEBUG = false;

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

  private int level = 0;

  public void pop() {
    println("(pop)");
    status = null;
    level--;
    if (level == 0) {
      reset();
    }
  }
}
