// Copyright (c) 2022 K Team. All Rights Reserved.
package org.kframework.parser.inner.kernel;

import org.apache.commons.codec.binary.StringUtils;
import org.jetbrains.annotations.NotNull;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Terminal;
import org.kframework.definition.TerminalLike;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import org.pcollections.PStack;

import java.util.Arrays;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * A parser for general context-free grammars based on the Earley recognizer algorithm found in
 * Jay Earley's paper
 * <a href="https://doi.org/10.1145%2F362007.362035">"An efficient context-free parsing algorithm"</a>
 * with some adaptations from Elizabeth Scott's paper
 * <a href="https://doi.org/10.1016%2Fj.entcs.2008.03.044">"SPPF-Style Parsing from Earley Recognizers"</a>.
 * and a minor fix relating to nullability taken from Aycock and Horspool's
 * <a href="https://doi.org/10.1093/comjnl/45.6.620">"Practical Earley Parsing"</a>
 *
 * The algorithm is not _quite_ the one described in section 5 of Scott's paper. For one thing, we use a single-token
 * lookahead during prediction to cut down on the number of states we need to process. For another, we don't use quite
 * the same approach for constructing parse forests. Finally, there was an issue with Scott's implementation of nullable
 * non-terminals, and so we implement the prediction step from Aycock and Horspool's implementation when predicting a
 * nullable non-terminal. Due to the difference in the parse forests, this algorithm is unbounded-polynomial-order in
 * space usage. It would be theoretically possible to modify the way we generate parse forests to more closely follow
 * Scott's paper, which would give us a parser which uses cubic space, but this would require us to modify the Term type
 * rather substantially in order to binarize the TermCons nodes so that each has at most two children. This would be a
 * change that requires a much more substantial rewriting of the algorithm we use to process parse forests. It is
 * definitely worth considering however as it would dramatically improve the worst-case space usage of the algorithm on
 * ambiguous sentences.
 */
public class EarleyParser {

  /**
   * A single item of an {@link EarleyProduction}. Can be either an {@link EarleyTerminal} or an
   * {@link EarleyNonTerminal}.
   */
  private interface EarleyProductionItem {
    /**
     * @return true if the production item is a nonterminal, false otherwise.
     */
    boolean isNonTerminal();

    /**
     * @param nullable a {@link BitSet} where each index corresponds to a sort.
     * @return true if this production item can be parsed as the empty string according to the BitSet, false otherwise.
     * @apiNote Do not use this to check whether a sort or production is nullable. It exists solely to facilitate the
     * code which computes nullability.
     */
    boolean isNullable(BitSet nullable);
  }

  /**
   * A single non-terminal in an {@link EarleyProduction}.
   *
   * The sort is represented as an index within the `sorts` field.
   */
  private static final class EarleyNonTerminal implements EarleyProductionItem {
    public EarleyNonTerminal(int sort, List<Sort> sorts) {
      this.sort = sort;
      this.sorts = sorts;
    }

    final int sort;
    final List<Sort> sorts;

    public boolean isNonTerminal() { return true; }
    public boolean isNullable(BitSet nullable) { return nullable.get(sort); }

    public String toString() {
      return sorts.get(sort).toString();
    }
  }

  /**
   * A single terminal in an {@link EarleyProduction}.
   *
   * The terminal is represented by a particular token kind as informed by the provided {@link Scanner}.
   * Token 0 is always the EOF token, which should appear only in the production used by the start state of the parser.
   */
  private static final class EarleyTerminal implements EarleyProductionItem {
    public EarleyTerminal(Scanner scanner, int kind) {
      this.scanner = scanner;
      this.kind = kind;
    }

    private final Scanner scanner;
    final int kind;

    public boolean isNonTerminal() { return false; }
    public boolean isNullable(BitSet ignored) { return false; }

    public String toString() {
      if (kind == 0) {
        return "<EOS>";
      }
      return scanner.getTokenByKind(kind).toString();
    }
  }

  /**
   * A single production as represented by the parser.
   */
  private static final class EarleyProduction {
    /**
     * @param index the index of the production within the `productions` field. Index 0 is reserved for the production
     *              `syntax ENTRY ::= STARTSYMBOL "EOF", where ENTRY is sort 0, STARTSYMBOL is the start symbol of the
     *              parser, and "EOF" is the EOF token, token 0.
     * @param prod The {@link Production} to use to construct a {@link org.kframework.parser.ProductionReference} from
     *             a completed parse state. Use null in the case of production 0.
     * @param sort The sort of the production, as an index in the `sorts` field.
     * @param items The production's production items.
     * @param sorts The list of all sorts used by the parser in canonical order.
     */
    public EarleyProduction(int index, Production prod, int sort, List<EarleyProductionItem> items, List<Sort> sorts) {
      this.index = index;
      this.prod = prod;
      this.sort = sort;
      this.items = items;
      this.sorts = sorts;
      if (prod == null) {
        this.isToken = false;
        this.needsLabel = false;
        this.isMInt = false;
      }
    }

    final int index;
    final Production prod;
    final int sort;
    final List<EarleyProductionItem> items;
    final List<Sort> sorts;
    private Boolean isToken, needsLabel, isMInt;

    public String toString() {
      return "syntax " + sorts.get(sort) + " ::= " +
              items.stream().map(EarleyProductionItem::toString).reduce((s1, s2) -> s1 + " " + s2).orElse("");
    }

    /**
     * @return true if prod has the token attribute, false otherwise.
     */
    public boolean isToken() {
      Boolean isToken = this.isToken;
      if (isToken == null) {
        isToken = prod.att().contains("token");
        this.isToken = isToken;
      }
      return isToken;
    }

    /**
     * @return true if the production should have a klabel, false otherwise.
     */
    public boolean needsLabel() {
      Boolean needsLabel = this.needsLabel;
      if (needsLabel == null) {
        needsLabel = prod.klabel().isDefined() || !prod.isSyntacticSubsort();
        this.needsLabel = needsLabel;
      }
      return needsLabel;
    }

    /**
     * @return true if the production is the production for MInt literals, false otherwise.
     */
    public boolean isMInt() {
      Boolean isMInt = this.isMInt;
      if (isMInt == null) {
        isMInt = prod.att().getOptional(Att.HOOK()).orElse("").equals("MINT.literal");
        this.isMInt = isMInt;
      }
      return isMInt;
    }
  }

  /**
   * An LR(0) parsing item. I.e., a production and a "dot", representing an index within the production up to which
   * parsing has completed.
   *
   * This class is only used to facilitate nullability computations. However, conceptually, the `prod` and `item` fields
   * of an {@link EarleyState} also represent an LR(0) parsing item.
   */
  private static final class LRItem {
    public LRItem(EarleyProduction prod, int item) {
      this.prod = prod;
      this.item = item;
    }

    final EarleyProduction prod;
    int item;

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      LRItem lrItem = (LRItem) o;
      return item == lrItem.item && prod.equals(lrItem.prod);
    }

    @Override
    public int hashCode() {
      return Objects.hash(prod, item);
    }

    public String toString() {
      return "(" + prod.toString() + ", " + item + ")";
    }
  }

  /**
   * An Earley parser parse state. Consists of an inlined LR(0) item (see {@link LRItem}) and an index within the
   * sentence being parsed where the parse state began.
   *
   * Each parse state also has a parse tree associated with it, in the form of a Set<PStack<Term>> object.
   * Each element in the set represents a single possible parse at this state, with one element in the PStack for each
   * non-terminal left of the "dot" on the right-hand-side of the production.
   *
   * Additionally, we compute the value `ntItem` which corresponds to the number of non-terminals left of the "dot" in
   * the LR(0) item this state corresponds to.
   */
  private static final class EarleyState {
    public EarleyState(EarleyProduction prod, int item, int start) {
      this.prod = prod;
      this.item = item;
      this.start = start;
      int ntItem = 0;
      for (int k = 0; k < item; k++) {
        if (prod.items.get(k).isNonTerminal()) {
          ntItem++;
        }
      }
      this.ntItem = ntItem;
    }

    final EarleyProduction prod;
    final int item;
    final int start;
    final int ntItem;
    Set<PStack<Term>> parseTree;

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      EarleyState that = (EarleyState) o;
      return item == that.item && start == that.start && prod.equals(that.prod);
    }

    @Override
    public int hashCode() {
      return Objects.hash(prod, item, start);
    }

    public String toString() {
      return "(" + prod.toString() + ", " + item + ", " + start + ")";
    }

    public Set<PStack<Term>> parseTree() {
      if (parseTree == null) {
        return EMPTY_PARSE_TREE;
      }
      return parseTree;
    }
  }

  /**
   * A wrapper around a {@link Set<Term>} representing the parse trees that can be parsed for a particular non-terminal
   * over a particular range of the input. This information is deduplicated across multiple parse states in order to
   * preserve sharing in the resulting parse forest.
   */
  private static final class CompleteParseTreeNode {
    Set<Term> derivations;

    public CompleteParseTreeNode() {
      derivations = new HashSet<>();
    }
  }

  /**
   * Compute the CompleteParseTreeNode for a non-terminal and an input range from a parse tree that is
   * part of an {@link EarleyState} which has parsed an entire production.
   *
   * @param parses The set of parses to add new derivations to.
   * @param parseTree The parse tree of the {@link EarleyState} being processed.
   * @param eprod The {@link EarleyProduction} that was just parsed.
   * @param start The start-index of the input range that was parsed.
   * @param end The end-index of the input range that was parsed.
   * @param data The {@link ParserMetadata} about the current sentence being parsed.
   */
  private static void wrapState(Set<Term> parses, Set<PStack<Term>> parseTree, EarleyProduction eprod, int start, int end, ParserMetadata data) {
    for (PStack<Term> children : parseTree) {
      Production prod = eprod.prod;
      Term result;

      // compute the Location
      int startLoc = data.words[start].startLoc;
      int endLoc;
      if (start != end) {
        endLoc = data.words[end-1].endLoc;
      } else {
        endLoc = data.words[end].endLoc;
      }
      int startLine = data.lines[startLoc];
      int startColumn = data.columns[startLoc];
      int endLine = data.lines[endLoc];
      int endColumn = data.columns[endLoc];
      Location loc = new Location(startLine, startColumn, endLine, endColumn);

      if (eprod.isToken()) {
        // it's a token, so create a Constant.
        String value = data.input.substring(startLoc, endLoc);
        if (eprod.isMInt()) {
          // it's an MInt token, so make sure to add the correct bit-length to the production before creating the
          // Constant
          int index = value.indexOf('p');
          if (index == -1) {
            index = value.indexOf('P');
          }
          assert index != -1;
          String param = value.substring(index + 1);
          prod = prod.substitute(Seq(Sort(param)));
        }
        result = Constant.apply(value, prod, Optional.of(loc), Optional.of(data.source));
      } else if (eprod.needsLabel()) {
        // it's a regular symbol, so create a TermCons
        result = TermCons.apply(children, prod, loc, data.source);
      } else {
        // either a bracket or a subsort, therefore, create no node at all.
        result = children.get(0);
      }
      parses.add(result);
    }
  }

  /**
   * A set of {@link EarleyState EarleyStates}.
   *
   * Each set corresponds to a particular end-index within the sentence being parsed, and contains all states that end
   * at that index. Being a set, duplicate states are combined. For the purposes of deduplication, we only consider the
   * production, start index, and "dot" of a state. We use a list of mappings from states to themselves in order to
   * deduplicate states. When a state is re-added, the parse tree is merged with the one already in the set.
   *
   * Each set also stores a 2D array of {@link CompleteParseTreeNode CompleteParseTreeNodes} which are used to
   * deduplicate the parse trees from parse states that have finished processing a production. This implements the
   * invariant that a tuple (S, i, j) for a particular sort, start-index, and end-index must exist only once in the
   * parse forest.
   *
   * Finally, each set also stores a mapping from sorts to lists of states that is used by the complete function of
   * the parser in order to identify which states need to be advanced past a particular non-terminal when a production
   * is completed (i.e., the "dot" reaches the end of the production).
   *
   * EarleySet implements a concurrent iterator for states. i.e., as long as states are only ever added to the end of
   * the list, it is possible to iterate over the entire set one element at a time even if elements are added during
   * the iteration process. This invariant is preserved by the code.
   */
  private static final class EarleySet implements Iterable<EarleyState> {
    private final List<EarleyState> states = new ArrayList<>();
    private List<Map<EarleyState, EarleyState>> membership;
    private final List<List<EarleyState>> completor = new ArrayList<>();
    private CompleteParseTreeNode[][] completedParseTrees;
    private final int index;
    private final int nsorts;

    /**
     * @param index The end-index this set corresponds to.
     * @param nsorts The total number of sorts in the grammar being parsed.
     */
    public EarleySet(int index, int nsorts) {
      this.index = index;
      this.nsorts = nsorts;
      membership = new ArrayList<>(index+1);
      for (int i = 0; i <= index; i++) {
        membership.add(new HashMap<>());
      }
      for (int i = 0; i <= nsorts; i++) {
        completor.add(new ArrayList<>());
      }
    }

    @NotNull
    public Iterator<EarleyState> iterator() {
      return new EarleySetIterator();
    }

    private class EarleySetIterator implements Iterator<EarleyState> {
      int idx = 0;
      public boolean hasNext() {
        return idx < states.size();
      }

      public EarleyState next() {
        return states.get(idx++);
      }
    }

    /**
     * Obtain the parse tree associated with a tuple (S, i, j) of sort, start-index, and end-index.
     * @param sort The sort that was just parsed.
     * @param start The start-index that the production was parsed from.
     * @return The unique parse tree node associated with that sort, start-index, and end-index.
     */
    private Set<Term> completedParses(int sort, int start) {
      CompleteParseTreeNode[][] nodes = completedParseTrees;
      if (nodes == null) {
        nodes = new CompleteParseTreeNode[index+1][nsorts];
        completedParseTrees = nodes;
      }
      CompleteParseTreeNode node = nodes[start][sort];
      if (node == null) {
        node = new CompleteParseTreeNode();
        nodes[start][sort] = node;
      }
      return node.derivations;
    }

    /**
     * Combine the parse trees of two states.
     *
     * @param prevState The state to add new derivations to.
     * @param state The state that contains the derivations to add
     */
    private void unionParseTree(EarleyState prevState, EarleyState state) {
      if (state.parseTree != null) {
        if (prevState.parseTree == null) {
          prevState.parseTree = state.parseTree;
        } else {
          prevState.parseTree.addAll(state.parseTree);
        }
      }
    }

    /**
     * Adds an {@link EarleyState} to the set.
     *
     * @param state The state to be added.
     * @param data The {@link ParserMetadata} about the current sentence being parsed.
     */
    public void add(EarleyState state, ParserMetadata data) {
      EarleyState prevState = membership.get(state.start).get(state);
      if (prevState != null) { // if the state already exists in the set
        // merge previous and current state's parse tree.
        unionParseTree(prevState, state);
        if (state.item == state.prod.items.size()) {
          // if the state is complete, add the proper derivations to the CompleteParseTreeNode
          Set<Term> parses = completedParses(state.prod.sort, state.start);
          wrapState(parses, state.parseTree(), state.prod, state.start, index, data);
        }
        return;
      }
      // add state to set
      states.add(state);
      // compute metadata about new state
      membership.get(state.start).put(state, state);
      if (state.item != state.prod.items.size() && state.prod.items.get(state.item).isNonTerminal()) {
        EarleyNonTerminal nt = (EarleyNonTerminal)state.prod.items.get(state.item);
        completor.get(nt.sort).add(state);
      } else if (state.item == state.prod.items.size()) {
        // if the state is complete, add the proper derivations to the CompleteParseTreeNode
        Set<Term> parses = completedParses(state.prod.sort, state.start);
        wrapState(parses, state.parseTree(), state.prod, state.start, index, data);
      }
    }

    /**
     * @return true if the set is empty.
     */
    public boolean empty() {
      return states.isEmpty();
    }

    /**
     * @param sort The sort to look up states to complete for as an index in the `sorts` field.
     * @return The states that need to be advanced during completion.
     */
    public List<EarleyState> completor(int sort) {
      return completor.get(sort);
    }

    /**
     * Finalize the set by cleaning up, after all states have been added to it.
     */
    public void finish() {
      membership = null;
      completedParseTrees = null;
    }
  }

  /**
   * Metadata about the state of the sentence being parsed. We collect this all in a single place in order to simplify
   * the type signatures of many methods.
   */
  private static class ParserMetadata {
    /**
     * @param input The sentence being parsed
     * @param scanner The scanner to use to tokenize the sentence
     * @param source The {@link Source} of the sentence.
     * @param startLine The line the sentence started on.
     * @param startColumn The column the sentence started on.
     */
    public ParserMetadata(String input, Scanner scanner, Source source, int startLine, int startColumn) {
      // compute location info
      byte[] utf8 = StringUtils.getBytesUtf8(input);
      int[] lines = new int[utf8.length+1];
      int[] columns = new int[utf8.length+1];
      int l = startLine;
      int c = startColumn;
      int length = input.codePointCount(0, input.length());
      for (int offset = 0, utf8offset = 0, codepoint, numBytes; offset < length; offset += Character.charCount(codepoint),
          utf8offset += numBytes) {
        codepoint = input.codePointAt(offset);
        numBytes = StringUtils.getBytesUtf8(new String(Character.toChars(codepoint))).length;
        for (int i = 0; i < numBytes; i++) {
          lines[utf8offset + i] = l;
          columns[utf8offset + i] = c;
        }

        switch (input.codePointAt(offset)) {
          case '\r' :
            if (offset+1 < input.length()) {
              if (input.charAt(offset+1) == '\n') {
                lines[offset+1] = l;
                columns[offset+1] = c + 1;
                offset++;
                utf8offset++;
              }
            }
          case '\n'      :
          case  '\u000B' :
          case  '\u000C' :
          case  '\u0085' :
          case  '\u2028' :
          case  '\u2029' :
            l++; c = 1; break;
          default :
            c++;
        }
      }
      lines[utf8.length] = l;
      columns[utf8.length] = c;

      //initialize
      this.words = scanner.tokenize(input, source, lines, columns);
      this.lines = lines;
      this.columns = columns;
      this.source = source;
      this.input = input;
    }

    // the list of tokens in the sentence
    Scanner.Token[] words;
    // an array containing the line of each character in the input sentence
    int[] lines;
    // an array containing the column of each character in the input sentence
    int[] columns;
    // a Source containing the file the sentence was parsed from
    Source source;
    // the original un-tokenized input sentence
    String input;
  }

  /**
   * @param m The module representing the grammar to use for parsing
   * @param scanner The scanner used to tokenize strings over this grammar.
   * @param startSymbol The start symbol to start parsing at.
   */
  public EarleyParser(Module m, Scanner scanner, Sort startSymbol) {
    this.scanner = scanner;

    // compute metadata about grammar
    sorts = getSorts(m);
    productions = getProductions(m, scanner, startSymbol);
    predictor = getPredictor();

    //compute nullability
    Set<LRItem> nullable = new HashSet<>();
    List<Set<LRItem>> callers = getCallers();
    this.nullable = new BitSet(sorts.size());
    for (EarleyProduction prod : productions) {
      markNullable(new LRItem(prod, 0), nullable, callers);
    }

    //compute first set
    first = computeFirstSet();
  }

  private Map<Sort, Integer> getSorts(Module m) {
    Map<Sort, Integer> sorts = new HashMap<>(m.allSorts().size());
    Sort entrySort = Sort("<ENTRY>");
    sorts.put(entrySort, 0);
    sortList.add(entrySort);
    Sort nullSort = Sort("<null>");
    sorts.put(nullSort, 1);
    sortList.add(nullSort);
    int i = 2;
    // some weirdness that turns out to be necessary due to how we implement MInt in RuleGrammarGenerator
    for (SortHead sortHead : iterable(m.definedInstantiations().keySet())) {
      Sort nonsenseSort = Sort(sortHead.name(), Seq(Sorts.K()));
      if (!m.allSorts().contains(nonsenseSort)) {
        sorts.put(nonsenseSort, i++);
        sortList.add(nonsenseSort);
      }
    }
    for (Sort s : iterable(m.allSorts())) {
      sorts.put(s, i++);
      sortList.add(s);
    }
    return sorts;
  }

  private List<EarleyProduction> getProductions(Module m, Scanner scanner, Sort startSymbol) {
    final List<EarleyProduction> productions;
    productions = new ArrayList<>(m.productions().size());
    productions.add(new EarleyProduction(0, null, 0, Arrays.asList(new EarleyNonTerminal(sorts.get(startSymbol), sortList), new EarleyTerminal(scanner, 0)), sortList));
    int index = 1;
    for (Production prod : iterable(m.productions())) {
      if (prod.params().size() != 0) {
        continue;
      }
      List<EarleyProductionItem> items = new ArrayList<>(prod.items().size());
      for (ProductionItem item : iterable(prod.items())) {
        if (item instanceof Terminal) {
          Terminal t = (Terminal) item;
          if (t.value().isEmpty()) {
            continue;
          }
        }
        items.add(toEarley(item, scanner));
      }
      Optional<Production> original = prod.att().getOptional(Att.ORIGINAL_PRD(), Production.class);
      Production prodToUse = prod;
      if (original.isPresent()) {
        prodToUse = original.get();
      }
      productions.add(new EarleyProduction(index++, prodToUse, sorts.get(prod.sort()), items, sortList));

    }
    return productions;
  }

  private EarleyProductionItem toEarley(ProductionItem item, Scanner scanner) {
    if (item instanceof NonTerminal) {
      Integer sort = sorts.get(((NonTerminal)item).sort());
      // sort may be null because private module imports may cause sort declarations to be missing
      if (sort == null) {
        sort = 1; // <NULL>, a sort with no productions
      }
      return new EarleyNonTerminal(sort, sortList);
    } else {
      return new EarleyTerminal(scanner, scanner.resolve((TerminalLike)item));
    }
  }

  private List<List<EarleyProduction>> getPredictor() {
    final List<List<EarleyProduction>> predictor = new ArrayList<>(sorts.size());
    for (int i = 0; i < sorts.size(); i++) {
      predictor.add(new ArrayList<>());
    }
    for (EarleyProduction prod : productions) {
      predictor.get(prod.sort).add(prod);
    }
    return predictor;
  }

  private List<Set<LRItem>> getCallers() {
    final List<Set<LRItem>> callers;
    callers = new ArrayList<>();
    for (int sort = 0; sort < sorts.size(); sort++) {
      callers.add(new HashSet<>());
    }
    for (EarleyProduction prod : productions) {
      for (int i = 0; i < prod.items.size(); i++) {
        EarleyProductionItem item = prod.items.get(i);
        if (item.isNonTerminal()) {
          EarleyNonTerminal nt = (EarleyNonTerminal) item;
          callers.get(nt.sort).add(new LRItem(prod, i));
        }
      }
    }
    return callers;
  }

  private void markNullable(LRItem state, Set<LRItem> nullable, List<Set<LRItem>> callers) {
    if (!nullable.contains(state)) {
      nullable.add(state);
      if (state.item < state.prod.items.size()) {
        if (state.prod.items.get(state.item).isNullable(this.nullable)) {
          markNullable(new LRItem(state.prod, state.item+1), nullable, callers);
        }
      } else {
        this.nullable.set(state.prod.sort);
        for (LRItem s : callers.get(state.prod.sort)) {
          if (nullable.contains(s)) {
            markNullable(new LRItem(s.prod, s.item+1), nullable, callers);
          }
        }
      }
    }
  }

  private BitSet[] computeFirstSet() {
    final BitSet[] first = new BitSet[sorts.size()];
    int arraySize = scanner.getMaxToken() + 1;
    for (int i = 0; i < sorts.size(); i++) {
      first[i] = new BitSet(arraySize);
    }
    boolean dirty;
    boolean once = true;
    do {
      dirty = false;
      for (int sort = 0; sort < sorts.size(); sort++) {
production:
        for (EarleyProduction prod : predictor.get(sort)) {
          if (!prod.items.isEmpty()) {
            for (int i = 0; i < prod.items.size(); i++) {
              EarleyProductionItem item = prod.items.get(i);
              if (item.isNonTerminal()) {
                EarleyNonTerminal nt = (EarleyNonTerminal)item;
                BitSet old = new BitSet(arraySize);
                BitSet curr = first[sort];
                old.or(curr);
                curr.or(first[nt.sort]);
                dirty = dirty || !old.equals(curr);
                if (!this.nullable.get(nt.sort)) {
                  continue production;
                }
              } else if (once) {
                EarleyTerminal t = (EarleyTerminal)item;
                dirty = dirty || !first[sort].get(t.kind);
                first[sort].set(t.kind);
                continue production;
              }
            }
          }
        }
      }
      once = false;
    } while (dirty);
    return first;
  }

  // ordered list of productions in grammar
  private final List<EarleyProduction> productions;
  // map from sorts to index of sort in various arrays
  private final Map<Sort, Integer> sorts;
  // ordered list of sorts in grammar
  private final List<Sort> sortList = new ArrayList<>();
  // logically, a Map<Sort, List<EarleyProduction>> mapping sorts to their productions
  private final List<List<EarleyProduction>> predictor;
  // logically, a Map<Sort, Map<Scanner.Token, Boolean>> representing the FIRST set of the grammar
  private final BitSet[] first;
  // logically, a Set<Sort> representing the NULLABLE set of the grammar.
  private final BitSet nullable;
  // the scanner to use to tokenize sentences before parsing them
  private final Scanner scanner;

  /**
   * Parse a sentence according to the grammar represented by this parser.
   * @param input The sentence to parse.
   * @param source The {@link Source} representing the file the string comes from.
   * @param startLine The line the sentence starts on.
   * @param startColumn The column the sentence starts on.
   * @return A {@link Term} representing the parse forest
   * @throws KEMException if parsing fails
   */
  public Term parse(String input, Source source, int startLine, int startColumn) {
    // compute metadata about sentence
    ParserMetadata data = new ParserMetadata(input, scanner, source, startLine, startColumn);

    // initialize Earley sets
    List<EarleySet> S = new ArrayList<>(data.words.length + 1);
    for (int k = 0; k <= data.words.length; k++) {
      S.add(new EarleySet(k, sorts.size()));
    }

    // initialize initial state of algorithm
    EarleyState startState = new EarleyState(productions.get(0), 0, 0);
    // add initial state to S[0]
    S.get(0).add(startState, data);
    // Q' is initially empty
    EarleySet Qprime = new EarleySet(0, sorts.size());

    for (int k = 0; k < data.words.length; k++) {
      // for each position in the tokenized sentence, compute S[k] and Q
      EarleySet Q = Qprime;
      Qprime = new EarleySet(k+1, sorts.size());
      // loop through S[k] and process each state, predicting and completing it
      for (EarleyState state : S.get(k)) {
        if (state.item != state.prod.items.size() && state.prod.items.get(state.item).isNonTerminal()) {
          // state is ready to process a non-terminal, therefore predict
          predict(S, Q, state, k, data);
        } else {
          // state is finished with a production, therefore complete
          complete(S, Q, state, k, data);
        }
        // states ready to process a terminal are added to Q and thus do not appear in S
      }
      S.get(k).finish();

      // loop through Q and process each state, scanning it
      for (EarleyState state : Q) {
        scan(S, Qprime, state, k, data);
      }

      // this loop condition is a bit tricky because we want to stop at the exact loop iteration that parsing failed
      // in order to generate the correct error message. Nominally speaking, parsing succeeds if after all loop
      // iterations, S[data.words.length] contains the state (productions.get(0), 2, 0). However, if S[k+1] is empty and
      // Q is empty at this point, then Qprime must also be empty. Thus, if k+1==data.words.length, S[data.words.length]
      // is empty, which means it's a parse error. And if k+1<data.words.length, then in the next loop iteration,
      // S[k] and Q will both start out empty, which means that no more states can ever be added at any point. As a
      // result, it will eventually be a parse error. Thus, the following condition is sufficient to prove that a
      // parse error will occur, and we can therefore report it now. The condition is not necessary, so we check for
      // a parse error after the outer loop finishes also.
      if (S.get(k+1).empty() && Q.empty()) {
        // no more states to process, so it must be a parse error
        parseError(data, k);
      }
    }
    if (S.get(data.words.length).empty()) {
      parseError(data, data.words.length-1);
    }
    // finished parsing successfully, so return the final parse forest
    return Ambiguity.apply(S.get(data.words.length).states.get(0).parseTree().stream().map(list -> list.get(0)).collect(Collectors.toSet()));
  }

  /**
   * @param data The {@link ParserMetadata} about the sentence being parsed
   * @param k The end-index at which a parse error occurred. In other words, the index just prior to the first token that
   *          did not parse.
   */
  private void parseError(ParserMetadata data, int k) {
    int startLine, startColumn, endLine, endColumn;
    if (data.words.length == 1) {
      startLine = data.lines[0];
      startColumn = data.columns[0];
      endLine = data.lines[0];
      endColumn = data.columns[0];
    } else {
      Scanner.Token t = data.words[k];
      startLine = data.lines[t.startLoc];
      startColumn = data.columns[t.startLoc];
      endLine = data.lines[t.endLoc];
      endColumn = data.columns[t.endLoc];
    }
    String msg = data.words.length-1 == k ?
        "Parse error: unexpected end of file" :
        "Parse error: unexpected token '" + data.words[k].value + "'";
    if (k != 0) {
      msg = msg + " following token '" + data.words[k - 1].value + "'.";
    } else {
      msg = msg + ".";
    }
    Location loc = new Location(startLine, startColumn,
            endLine, endColumn);
    throw KEMException.innerParserError(msg, data.source, loc);
  }

  private static final Set<PStack<Term>> EMPTY_PARSE_TREE = new HashSet<>();
  static {
    EMPTY_PARSE_TREE.add(ConsPStack.empty());
  }

  /**
   * Perform the "Predict" step of the Earley algorithm.
   *
   * @param S The {@link EarleySet EarleySets} for completion and prediction
   * @param Q The {@link EarleySet} for scanning
   * @param state The {@link EarleyState} to process
   * @param k the current end-index being parsed
   * @param data The {@link ParserMetadata} about the sentence being parsed
   */
  private void predict(List<EarleySet> S, EarleySet Q, EarleyState state, int k, ParserMetadata data) {
    EarleyNonTerminal nt = (EarleyNonTerminal)state.prod.items.get(state.item);
    // first, use lookahead to check if we need to predict this sort at all
    if (nullable.get(nt.sort) || first[nt.sort].get(data.words[k].kind)) {
      List<EarleyProduction> prods = predictor.get(nt.sort);
      for (EarleyProduction next : prods) {
        // for each production for the sort being predicted, add it to the appropriate set
        if (next.items.size() != 0 && !next.items.get(0).isNonTerminal()) {
          // if it's a terminal, add it to be scanned only if the next token matches
          EarleyTerminal t = (EarleyTerminal)next.items.get(0);
          if (t.kind == data.words[k].kind) {
            // if it matches, add (next, 0, k) to Q
            EarleyState nextState = new EarleyState(next, 0, k);
            Q.add(nextState, data);
          }
        } else {
          // state is either now complete or at a non-terminal, therefore add it to S[k]
          EarleyState nextState = new EarleyState(next, 0, k);
          S.get(k).add(nextState, data);
        }
      }
    }
    if (nullable.get(nt.sort)) {
      // non-terminal is nullable, so complete the state by advancing past the nullable sort.
      // see Aycock and Horspool
      EarleyState nextState = new EarleyState(state.prod, state.item+1, state.start);
      nextState.parseTree = new HashSet<>();
      wrapAndAppend(nt.sort, k, nextState, state, S.get(k));
      addStateToSet(S, Q, state, nextState, k, data);
    }
  }

  /**
   * Perform the "scan" step of the Earley algorithm
   *
   * @param S The {@link EarleySet EarleySets} for completion and prediction
   * @param Qprime The {@link EarleySet} for scanning
   * @param state The {@link EarleyState} to process
   * @param k the current end-index being parsed
   * @param data The {@link ParserMetadata} about the sentence being parsed
   */
  private void scan(List<EarleySet> S, EarleySet Qprime, EarleyState state, int k, ParserMetadata data) {
    // construct next state
    EarleyState nextState = new EarleyState(state.prod, state.item+1, state.start);
    nextState.parseTree = state.parseTree;
    addStateToSet(S, Qprime, state, nextState, k+1, data);
  }

  /**
   * Add a state to either S or Q depending on whether the next production item to parse is a terminal or a
   * non-terminal. May be added to neither if the next state expects a terminal not found next in the input.
   *
   * @param S The {@link EarleySet EarleySets} for completion and prediction.
   * @param Q The {@link EarleySet} for scanning
   * @param state The state that is being processed.
   * @param nextState The state that is being added to either S or Q.
   * @param k the current end-index being parsed.
   * @param data The {@link ParserMetadata} about the sentence being parsed.
   */
  private void addStateToSet(List<EarleySet> S, EarleySet Q, EarleyState state, EarleyState nextState, int k, ParserMetadata data) {
    // if the next item in the state is a terminal, scan it and possibly add it to Q'
    if (state.item+1 != state.prod.items.size() && !state.prod.items.get(state.item+1).isNonTerminal()) {
      EarleyTerminal t = (EarleyTerminal) state.prod.items.get(state.item+1);
      if (t.kind == data.words[k].kind) {
        Q.add(nextState, data);
      }
    } else {
      // state is either now complete or at a non-terminal, therefore add it to S[k+1]
      S.get(k).add(nextState, data);
    }
  }

  /**
   * Perform the "complete" step of the Earley algorithm
   *
   * @param S The {@link EarleySet EarleySets} for completion and prediction
   * @param Q The {@link EarleySet} for scanning
   * @param state The {@link EarleyState} to process
   * @param k the current end-index being parsed
   * @param data The {@link ParserMetadata} about the sentence being parsed
   */
  private void complete(List<EarleySet> S, EarleySet Q, EarleyState state, int k, ParserMetadata data) {
    // this state is nullable, therefore we need to compute its parse tree since it was not given one yet
    List<EarleyState> completedStates = S.get(state.start).completor(state.prod.sort);
    // for each state in S[state.start] that is waiting on the non-terminal corresponding to state.prod.sort
    for (EarleyState completed : completedStates) {
      // construct next state
      EarleyState nextState = new EarleyState(completed.prod, completed.item + 1, completed.start);
      nextState.parseTree = new HashSet<>();
      // compute parse tree of next state
      wrapAndAppend(state.prod.sort, state.start, nextState, completed, S.get(k));
      addStateToSet(S, Q, completed, nextState, k, data);
    }
  }

  /**
   * Construct the new parse tree for a state during the "complete" step, or after a nullable non-terminal in the
   * "predict" step.
   *
   * @param sort The sort that was just parsed.
   * @param start The start-index of the state being processed.
   * @param nextState The {@link EarleyState} to add the parse tree derivations to.
   * @param completed The {@link EarleyState} containing the parse tree prior to processing this non-terminal.
   * @param end The {@link EarleySet} representing the end-index being processed by the parser.
   */
  private void wrapAndAppend(int sort, int start, EarleyState nextState, EarleyState completed, EarleySet end) {
    Term newTerm = Ambiguity.apply(end.completedParses(sort, start));
    for (PStack<Term> terms : completed.parseTree()) {
      nextState.parseTree.add(terms.plus(newTerm));
    }
  }
}
