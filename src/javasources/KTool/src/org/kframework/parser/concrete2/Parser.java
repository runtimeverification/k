package org.kframework.parser.concrete2;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Comparator;
import java.util.Set;
import java.util.HashSet;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Deque;
import java.util.ArrayDeque;
import java.util.Map;

/*

rule atomaton
  (auto built in bottom-up tree automaton)

automatic priorities for internal positions is based on whether (dynamic) their are non-null forms

(...)* needs to deal with greedyness
predicates
regex as lookahead (requires single pass (going in reverse) at start)
  (hmm, lazy regexes?)
transitive priorities
allow non-rule resolved in parsing rules
how priorities related to rules (transitivity)

productions are regular expressions

Single tree properties:
  attribute grammars
+ token parsing (e.g. ints)
  brackets
    Conflicts with priorities (b/c they could be errased)
    (maybe set "bracketted" property on output?)
    or maybe rewrite brackets only as a child of another parse
    multi-pass macros
* whitespace
* priorities (positional)
+ associativity
  errors when mixing associativity?
* follow restrictions
  state: <state>...</state>
    indentation
    Cs typedef
    L-attributed grammars
    problem when mixed with non-det
*greedyness
*lexing productions
+prefers/avoids
*casts (?!)
  sort is in the wrong place to be of *any* use to the efficiency of the parser
have a way of analyzing the grammar to identify potential ambiguities
cells in the parser
error messages
  user definable error
  causality tracking

Problem:
  x+amb(y,z) should equal amb(x+y,x+z) but amb rules break that
    this equation is important in case someone disallows x+y and we have amb(x,a)+amb(y,b)
    thus we should behave as if we always expand out the "amb"

<state>...</>
<parse>...</>
<lookahead>...</>
<lookbehind>...</>
<lookhere>...</>
<possible>...</>

attribute to specify what production to use for Tokens (include "none")
function to get * for non-terminal:
  * = string, position, attributes

Problem??? do x; y; z w/ computations
Javascript: [new a.b.c.d()].e()

Fire rules with incomplete ASTs: _+_(2, HOLE)
Left recursion is a problem for when to file rules


Greedy vs non-greedy "*" operators (easy once we implement regex)
  (also include "*" operator that is neigther greedy nor non-greedy)
  make evaluation of parser always be greedy, but then run non-greedy when constructing actual parses

States could give info about how to factor their size

(error if arglist size greater than 10000)
*/

////////////////

/*
state: rule, ordering, owning-nt
  return
  other:
    regex: pattern, lookahead, lookbehind
    call-nt: nt
    lookahead: nt, list of success, list of failure

nt:
  set of states
  set of start states
*/

// TODO: parameters

/*
Terminology:
  entryState/exitState: the first and last states in a non-terminal

  stateCall/stateReturn: records for the entery to or exit from a state
  ntCall/ntReturn: records for the entry to or exit from a non-terminal

  stateBegin/stateEnd: the source positions for the begining and end the span of a state
  ntBegin/ntEnd: the source positions for the begining and end the span of a state

  nextState/previousState: successor/predicesor states in a state machine
*/

////////////////

// Positions are 'int' because CharSequence uses 'int' // Position in the text

class StateId { String name; public StateId(String name) { this.name = name; } } // Used only by rules

class NonTerminalId { String name; public NonTerminalId(String name) { this.name = name; } } // Used only by rules

// smallest states are computed first
class StateReturnComparator implements Comparator<StateReturn> {
  public int compare(StateReturn o1, StateReturn o2) {
      assert false;
      return 0;
/*
       o1.stateEnd <=> o2.stateEnd
    && o1.stateCall.ntCall.ntBegin <=> o2.stateCall.ntCall.ntBegin
    && 
    public final NonTerminal nt;
    public final int ntBegin;

    public final NonTerminalCall ntCall;
    public final int stateBegin;
    public final State state;

    public final StateCall stateCall;
    public final int stateEnd;

// Invarient:
  A state return is committed only if there is no state that
   - is earlier in the state machine,
   - ends earlier in the string, and
   - is on an either more or less general context
*/
  }
}

/*

context-function: context -> set of config

class Function:
  static IDENTITY
  Context -> Set of Results (results include errors?)
  union-functions()
  compose-child-function()
  factor-amb:
    C1 -> {A1*A2,A1*A3}
    C2 -> {B1*B2,B1*B3}
   =>
    C1 -> {A1*amb(A2,A3)}
    C2 -> {B1*amb(B2,B3)}
  compose-rule()
  -----
  Function composeChildFunction(Function)
  void union/add(Function);
  // composition must track which entries are new
*/

class Function {
    public static final Function NULL = new Function(false, null);
    public static final Function IDENTITY = new Function(false, null);

    private final NonTerminalCall ntCall;
    private boolean parses = false;
    public Function(boolean parses, NonTerminalCall ntCall) { this.parses = parses; this.ntCall = ntCall; }
    public void addFunction(Function f) {
        this.parses |= f.parses;
    }
    public boolean addFunctionComposition(Function sibling, Function child) {
        boolean oldParses = this.parses;
        this.parses |= sibling.parses && child.parses;
        return this.parses != oldParses;
    }

    void addFactored(Function that) {
        this.parses |= that.parses;
    }

    void runRule(Function that, StateReturn stateReturn) { // always subjugates
        this.parses |= that.parses;
    }
}

////////////////

class NonTerminal {
  public final NonTerminalId nonTerminalId;
  public final EntryState entryState;
  public final ExitState exitState;
  Set<NextableState> stepStates = new HashSet<NextableState>();
  //states = entryState + exitState + stepStates;

  public NonTerminal(NonTerminalId nonTerminalId,
                     StateId entryStateId, State.OrderingInfo entryOrderingInfo,
                     StateId exitStateId, State.OrderingInfo exitOrderingInfo) {
      this.nonTerminalId = nonTerminalId;
      this.entryState = new EntryState(entryStateId, this, entryOrderingInfo);
      this.exitState = new ExitState(exitStateId, this, exitOrderingInfo);
  }
}

abstract class State {
  final StateId stateId;
  final NonTerminal nt;
  final OrderingInfo orderingInfo;

  static class OrderingInfo { int key; public OrderingInfo(int key) { this.key = key; } }

  public State(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo) {
      this.stateId = stateId; this.nt = nt; this.orderingInfo = orderingInfo;
  }
}

class ExitState extends State {
    public ExitState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo)
    { super(stateId, nt, orderingInfo); }
}

abstract class NextableState extends State {
    public final Set<State> next = new HashSet<State>();
    NextableState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo)
    { super(stateId, nt, orderingInfo); }
}

class EntryState extends NextableState {
    public EntryState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo)
    { super(stateId, nt, orderingInfo); }
}

class NonTerminalState extends NextableState {
  public final NonTerminal nt;
  public final boolean isLookahead;

  public NonTerminalState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, NonTerminal child, boolean isLookahead)
  {
      super(stateId, nt, orderingInfo);
      this.nt = child;
      this.isLookahead = isLookahead;
  }
}

abstract class PrimitiveState extends NextableState {
  public static class MatchResult {
      final public int matchEnd;
      final public Function matchFunction;
      public MatchResult(int matchEnd, Function matchFunction) {
          this.matchEnd = matchEnd;
          this.matchFunction = matchFunction;
      }
  }

  abstract Set<MatchResult> matches(CharSequence text, int startPosition, Function context);

  public PrimitiveState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo)
  { super(stateId, nt, orderingInfo); }
}

class RegExState extends PrimitiveState {
  private final java.util.regex.Pattern pattern;

  public RegExState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, java.util.regex.Pattern pattern)
  {
      super(stateId, nt, orderingInfo);
      this.pattern = pattern;
  }

  Set<MatchResult> matches(CharSequence text, int startPosition, Function context) {
      java.util.regex.Matcher matcher = pattern.matcher(text);
      matcher.region(startPosition, text.length());
      matcher.useAnchoringBounds(false);
      matcher.useAnchoringBounds(false);
      Set<MatchResult> results = new HashSet<MatchResult>();
      if (matcher.lookingAt()) {
          results.add(new MatchResult(matcher.end(), Function.IDENTITY)); //matchFunction(text, matcher.start(), matcher.end())));
      }
      return results;
  }
}

////////////////

class StateCall {
  public final Function function = Function.NULL;
  public StateReturnWorkList workList = null; // top of queue stack when addFunction was last updated called
  public static class Key {
    public final NonTerminalCall ntCall;
    public final int stateBegin;
    public final State state;

//// Boilerplate after this line ////
    public Key(NonTerminalCall ntCall, int stateBegin, State state) {
        this.ntCall = ntCall; this.stateBegin = stateBegin; this.state = state;
    }
  }
  public final Key key;
  private StateCall(Key key) { this.key = key; }
}

class StateReturn {
  public final Function preRuleFunction = Function.NULL; // entries are accumulated
  public final Function factoredFunction = Function.NULL;
  public final Function postRuleFunction = Function.NULL; // entries are immutable once added

  public static class Key {
    public final StateCall stateCall;
    public final int stateEnd;
//// Boilerplate after this line ////
    public Key(StateCall stateCall, int stateEnd) {
        assert (!((stateCall.key.state instanceof NonTerminalState) &&
                  (((NonTerminalState)stateCall.key.state).isLookahead)) ||
                stateCall.key.stateBegin == stateEnd);
        this.stateCall = stateCall; this.stateEnd = stateEnd;
    }
  }
  public final Key key;
  private StateReturn(Key key) { this.key = key; }
}

class NonTerminalCall {
  Set<StateCall> callers = new HashSet<StateCall>();
  public final Set<StateReturn> stateReturns = new HashSet<StateReturn>();
  public final Set<StateReturn> exitStateReturns = new HashSet<StateReturn>();
  //exitStateReturns() // = stateReturns.filter(x.stateCall.state instanceof ReturnState)
  public static class Key {
    public final NonTerminal nt;
    public final int ntBegin;
  // Boilerplate after this line
    public Key(NonTerminal nt, int ntBegin) {
        // assert ntBegin == c.stateBegin for c in callers
        this.nt = nt; this.ntBegin = ntBegin;
    }
  }
  public final Key key;
  private NonTerminalCall(Key key) { this.key = key; }
}

class StateReturnWorkList extends TreeSet<StateReturn> {
  //push
  public void enqueue(StateReturn stateReturn) { this.add(stateReturn); }
  public StateReturn dequeue() { StateReturn stateReturn = this.first(); this.remove(stateReturn); return stateReturn; }     
}

class StateReturnWorkLists {
    private final Deque<StateReturnWorkList> stack = new ArrayDeque<StateReturnWorkList>();
    void push() { stack.addFirst(new StateReturnWorkList()); }
    void pop() { stack.removeFirst(); }
    StateReturnWorkList top() { return stack.peekFirst(); }
}

class ParseState {
  final CharSequence input;
  final public StateReturnWorkLists stateReturnWorkLists = new StateReturnWorkLists();

  public ParseState(CharSequence input) { this.input = input; }

  Map<NonTerminalCall.Key,NonTerminalCall> ntCalls;
  Map<StateCall.Key,StateCall> stateCalls;
  Map<StateReturn.Key,StateReturn> stateReturns;

  private static final Constructor<NonTerminalCall> nonTerminalCallCtor =
      getCtor(NonTerminalCall.class, NonTerminalCall.Key.class);
  private static final Constructor<StateCall> stateCallCtor =
      getCtor(StateCall.class, StateCall.Key.class);
  private static final Constructor<StateReturn> stateReturnCtor =
      getCtor(StateReturn.class, StateReturn.Key.class);
  static <T> Constructor<T> getCtor(Class<T> cls, Class arg) {
      try {
          return cls.getDeclaredConstructor(arg);
      } catch (NoSuchMethodException e) {
          e.printStackTrace();
          System.exit(1);
          return null;
      }
  }

  public NonTerminalCall getNtCall(NonTerminalCall.Key key) { return getValue(key, ntCalls, nonTerminalCallCtor); }
  public StateCall getStateCall(StateCall.Key key) { return getValue(key, stateCalls, stateCallCtor); }
  public StateReturn getStateReturn(StateReturn.Key key) { return getValue(key, stateReturns, stateReturnCtor); }

  // See http://docs.oracle.com/javase/tutorial/java/generics/restrictions.html#createObjects
  private static <V, Key> V getValue(Key key, Map<Key, V> map, Constructor<V> ctor) {
    V value = map.get(key);
    if (value == null) {
        try {
            value = ctor.newInstance(key);
            map.put(key, value);
        } catch (InvocationTargetException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (IllegalAccessException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (InstantiationException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }
    return value;
  }
}

////////////////

class Parser {
  ParseState s;

  public void parse(NonTerminal nt, int position) {
      // TODO: fix
      NonTerminal startNt = new NonTerminal(new NonTerminalId("<start>"),
                                            new StateId("<start-entry>"), new State.OrderingInfo(0),
                                            new StateId("<start-exit>"), new State.OrderingInfo(2)); // TODO: fix
      State state = new NonTerminalState(new StateId("<start>"), startNt, new State.OrderingInfo(1), nt, true);

      activateNtCall(s.getStateCall(new StateCall.Key(s.getNtCall(new NonTerminalCall.Key(nt, position)), position, state)));

      while (s.stateReturnWorkLists.top() != null) {
          StateReturn stateReturn = null;
          while ((stateReturn = s.stateReturnWorkLists.top().dequeue()) != null) {
              this.stateReturn(stateReturn);
          }
          s.stateReturnWorkLists.pop();
      }
  }

  private void unknownStateType() { assert false : "Unkown state type"; }

  /****************
  * State Return
  ****************/
  public void stateReturn(StateReturn stateReturn) {
    // Note that 'addPreRule' also puts the stateReturn in the work list
    // Note that 'addFunction' sets the call to use the top queue when a stateReturn is places
    // Note that 'addCaller' also sets up entry state

    stateReturn.factoredFunction.addFactored(stateReturn.preRuleFunction); // if lookahead, factors all results
    stateReturn.postRuleFunction.runRule(stateReturn.factoredFunction, stateReturn); // always subjugates

    State state = stateReturn.key.stateCall.key.state;
    if (state instanceof ExitState) {
        // add exit state's function to all callers
        for (StateCall stateCall : stateReturn.key.stateCall.key.ntCall.callers) {
            int stateEnd = ((NonTerminalState)stateCall.key.state).isLookahead ? // we know a caller must be a NonTerminalState
                stateReturn.key.stateCall.key.stateBegin :
                stateReturn.key.stateEnd;
            this.addPreRuleFunction(new StateReturn.Key(stateCall, stateEnd),
                                    stateCall.function, stateReturn.postRuleFunction);
        }
    } else if (state instanceof NextableState) {
        // activate all next states
        for (State nextState : ((NextableState)state).next) {
            // activate state. add function and makes call use the top work list
            StateCall stateCall = activateStateCall(
                new StateCall.Key(stateReturn.key.stateCall.key.ntCall, stateReturn.key.stateEnd, nextState),
                stateReturn.postRuleFunction);

            if (nextState instanceof ExitState) {
                // an exit state's preRule is just the stateCall.function
                addPreRuleFunction(new StateReturn.Key(stateCall, stateCall.key.stateBegin),
                                   stateCall.function, Function.IDENTITY);
            } else if (nextState instanceof PrimitiveState) {
                // In order to avoid duplication of work, we must wrap a primitive inside a non-terminal (TODO: explain)
                for (PrimitiveState.MatchResult matchResult : ((PrimitiveState)nextState).matches(s.input, stateCall.key.stateBegin, stateCall.function)) {
                    // a primitive state's preRule just moves the position forward
                    addPreRuleFunction(new StateReturn.Key(stateCall, matchResult.matchEnd),
                                       stateCall.function, matchResult.matchFunction);
                }
            } else if (nextState instanceof NonTerminalState) {
                activateNtCall(stateCall);
            } else { unknownStateType(); }
        }
    } else { unknownStateType(); }
  }

  void activateNtCall(StateCall stateCall) {
      if (((NonTerminalState)stateCall.key.state).isLookahead) { s.stateReturnWorkLists.push(); }

      NonTerminalCall ntCall = s.getNtCall(new NonTerminalCall.Key(stateCall.key.state.nt, stateCall.key.stateBegin));
      ntCall.callers.add(stateCall);

      StateCall entryStateCall = activateStateCall(new StateCall.Key(ntCall, ntCall.key.ntBegin, ntCall.key.nt.entryState), Function.IDENTITY);

      addPreRuleFunction(new StateReturn.Key(entryStateCall, ntCall.key.ntBegin), Function.IDENTITY, Function.IDENTITY);
  }

  // mark state as being in the top queue
  // add function to the state function
  StateCall activateStateCall(StateCall.Key key, Function function) {
      StateCall stateCall = s.getStateCall(key);
      stateCall.workList = s.stateReturnWorkLists.top();
      stateCall.function.addFunction(function);
      return stateCall;
  }

  void addPreRuleFunction(StateReturn.Key key, Function sibling, Function child) { // add stateReturn to queue if preRuleFunction gets new entries (constructor does not queue)
      // add the stateReturn to the nt's stateReturns and exitStateReturns lists
      StateReturn stateReturn = s.getStateReturn(key);
      stateReturn.key.stateCall.key.ntCall.stateReturns.add(stateReturn);
      if (stateReturn.key.stateCall.key.state instanceof ExitState) {
          stateReturn.key.stateCall.key.ntCall.exitStateReturns.add(stateReturn);
      }

      // Enqueue if we creates new data
      if (stateReturn.preRuleFunction.addFunctionComposition(sibling, child)) {
          stateReturn.key.stateCall.workList.enqueue(stateReturn);
      }
  }
}
