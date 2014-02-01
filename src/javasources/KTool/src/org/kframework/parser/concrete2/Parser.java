package org.kframework.parser.concrete2;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.parser.concrete2.Grammar.ExitState;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalId;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.State;
import org.kframework.parser.concrete2.Grammar.StateId;

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
    //private final NonTerminalCall ntCall;
    //private Set<TermRewrites> terms;
    private Set<KList> terms = new HashSet<KList>();
    //private boolean parses;
    private Function(Set<KList> terms) { this.terms = terms; }
    //public Function(NonTerminalCall ntCall, Term ) { this.ntCall = ntCall; }

    public static Function constant(Term term) {
        return new Function(new HashSet<KList>(Arrays.asList(new KList(Arrays.asList(term)))));
    }
    public static Function empty() {
        return new Function(new HashSet<KList>());
    }
    public static Function identity() {
        return new Function(new HashSet<KList>(Arrays.asList(new KList())));
    }

    public void addFunction(Function that) {
        this.terms.addAll(that.terms);
    }

    public boolean addFunctionComposition(Function sibling, Function child) {
        boolean result = false;
        for (KList x : sibling.terms) {
            for (KList y : child.terms) {
                KList z = x.shallowCopy();
                z.getContents().addAll(y.getContents());
                result |= this.terms.add(z);
            }
        }
        return result;
    }

    class Factoring {
        public final KList prefix;
        public final Term suffix;
        public Factoring(KList prefix, Term suffix) {
            this.prefix = prefix; this.suffix = suffix;
        }
    }
    Factoring factor(KList klist) {
        if (klist.getContents().size() == 0) {
            return null;
        } else {
            return new Factoring(new KList(klist.getContents().subList(0, klist.getContents().size()-1)),
                                 klist.getContents().get(klist.getContents().size()-1));
        }
    }

    void addFactoredAndRunRule(Function that, StateReturn stateReturn) { // if lookahead, factors all results; always subjugates
        // this factoring will be wrong once we move to context sensitive functions, but it works for now
        //this.terms.append(new Ambiguity("K", Arrays.asList(that.terms)));

        this.terms.addAll(stateReturn.key.stateCall.key.state.runRule(that.terms));

        /* This code may be no longer useful.  We discovered that factorings are unneeded (we think).
        //A more general algorithm would look roughly like the following:
        Set<KList> unfactorables = new HashSet<KList>();
        HashMultimap<KList,Term> factorings = HashMultimap.create();
        for (KList klist : that.terms) {
            Factoring factoring = factor(klist);
            if (factoring == null) {
                unfactorables.add(klist);
            } else {
                factorings.put(factoring.prefix, factoring.suffix);
            }
        }
        for (KList klist : unfactorables) {
            this.terms.add(stateReturn.key.stateCall.key.state.runRule(klist));
        }
        for (Map.Entry<KList,Collection<Term>> entry : factorings.asMap().entrySet()) {
            KList klist = entry.getKey().shallowCopy();
            klist.getContents().add(new Ambiguity("K", new ArrayList<Term>(entry.getValue()))); // TODO: check result
            this.terms.add(stateReturn.key.stateCall.key.state.runRule(klist));
        }
        */
    }

    Set<KList> applyToNull() { return terms; }
}


class StateCall {
    public final Function function = Function.empty();
    public StateReturnWorkList workList = null; // top of queue stack when addFunction was last updated called
    public static class Key {
        public final NonTerminalCall ntCall;
        public final int stateBegin;
        public final State state;

//// Boilerplate after this line ////
        public Key(NonTerminalCall ntCall, int stateBegin, State state) {
            this.ntCall = ntCall; this.stateBegin = stateBegin; this.state = state;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Key key = (Key) o;

            if (stateBegin != key.stateBegin) return false;
            if (!ntCall.equals(key.ntCall)) return false;
            if (!state.equals(key.state)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = ntCall.key.hashCode();
            result = 31 * result + stateBegin;
            result = 31 * result + state.hashCode();
            return result;
        }
    }
    public final Key key;
    StateCall(Key key) { this.key = key; }
}

class StateReturn implements Comparable<StateReturn> {
    public final Function preRuleFunction = Function.empty(); // entries are accumulated
    public final Function postRuleFunction = Function.empty(); // entries are immutable once added

/* Invarient:
  A state return is committed only if there is no state that
   - is earlier in the state machine,
   - ends earlier in the string, and
   - is on an either more or less general context
*/
    public int compareTo(StateReturn that) {
        int x;
        return
            ((x = Integer.compare(this.key.stateEnd, that.key.stateEnd)) != 0) ? x :
            ((x = Integer.compare(that.key.stateCall.key.ntCall.key.ntBegin,
                                  this.key.stateCall.key.ntCall.key.ntBegin)) != 0) ? x: // note the reversed order
            ((x = this.key.stateCall.key.state.compareTo(that.key.stateCall.key.state)) != 0) ? x :
            Integer.compare(this.key.stateCall.key.stateBegin, that.key.stateCall.key.stateBegin);
    }

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

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Key key = (Key) o;

            if (stateEnd != key.stateEnd) return false;
            if (!stateCall.equals(key.stateCall)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = stateCall.key.hashCode();
            result = 31 * result + stateEnd;
            return result;
        }
    }
    public final Key key;
    StateReturn(Key key) { this.key = key; }

    public int hashCode() {
        return this.key.hashCode();
    }
}

class NonTerminalCall {
    Set<StateCall> callers = new HashSet<StateCall>();
    public final Set<StateReturn> stateReturns = new HashSet<StateReturn>();
    public final Set<StateReturn> exitStateReturns = new HashSet<StateReturn>(); // = stateReturns.filter(x.stateCall.state instanceof ExitState)
    public static class Key {
        public final NonTerminal nt;
        public final int ntBegin;
//// Boilerplate after this line ////
        public Key(NonTerminal nt, int ntBegin) {
            // assert ntBegin == c.stateBegin for c in callers
            this.nt = nt; this.ntBegin = ntBegin;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Key key = (Key) o;

            if (ntBegin != key.ntBegin) return false;
            if (!nt.equals(key.nt)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = nt.hashCode();
            result = 31 * result + ntBegin;
            return result;
        }
    }
    public final Key key;
    NonTerminalCall(Key key) { this.key = key; }
}

////////////////

class StateReturnWorkList extends TreeSet<StateReturn> {
    public void enqueue(StateReturn stateReturn) { this.add(stateReturn); }
    public StateReturn dequeue() { return this.pollFirst(); }
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

    Map<NonTerminalCall.Key,NonTerminalCall> ntCalls = new HashMap<NonTerminalCall.Key,NonTerminalCall>();
    Map<StateCall.Key,StateCall> stateCalls = new HashMap<StateCall.Key,StateCall>();
    Map<StateReturn.Key,StateReturn> stateReturns = new HashMap<StateReturn.Key,StateReturn>();

    public NonTerminalCall getNtCall(NonTerminalCall.Key key) {
            NonTerminalCall value = ntCalls.get(key);
            if (value == null) {
                    value = new NonTerminalCall(key);
                    ntCalls.put(key, value);
            }
            return value;
    }
    public StateCall getStateCall(StateCall.Key key) {
        StateCall value = stateCalls.get(key);
        if (value == null) {
            value = new StateCall(key);
            stateCalls.put(key, value);
        }
        return value;

    }
    public StateReturn getStateReturn(StateReturn.Key key) {
        StateReturn value = stateReturns.get(key);
        if (value == null) {
            value = new StateReturn(key);
            stateReturns.put(key, value);
        }
        return value;
    }
}

////////////////

public class Parser {
	
    public static void main(String[] args) {
        try {
            System.in.read();
        } catch (Exception e) {
            e.printStackTrace();
        }

        Grammar.NonTerminalId ntistart = new Grammar.NonTerminalId("StartNT");
        Grammar.StateId stistart = new Grammar.StateId("StartState");
        Grammar.StateId stiend = new Grammar.StateId("EndState");

        Grammar.NonTerminal nt1 = new Grammar.NonTerminal(ntistart, stistart, new Grammar.State.OrderingInfo(0), stiend, new Grammar.State.OrderingInfo(100));

        Grammar.RegExState res1 = new Grammar.RegExState(new Grammar.StateId("RegExStid"), nt1, new Grammar.State.OrderingInfo(1), Pattern.compile("[a-zA-Z0-9]"));

        nt1.entryState.next.add(res1);
        nt1.entryState.next.add(nt1.exitState);
        res1.next.add(nt1.exitState);
        res1.next.add(res1);

        {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < 100000; i++) {
                sb.append('a');
            }
            for (int j = 0; j < 10; j++) {
                long start = getCpuTime();
                for (int i = 0; i < 1; i++) {
                    Term result = new Parser(new ParseState(sb.toString())).parse(nt1, 0);
                }
                long end = getCpuTime();
                System.out.println("Time: " + ((end - start) / 1000000.0));
            }
        }
        try {
            System.in.read();
            System.in.read();
            System.in.read();
            System.in.read();
            System.in.read();
            System.in.read();
            System.in.read();
        } catch (Exception e) {
            e.printStackTrace();
        }
        // with proper implementation we are slow:
        //  - for a string of length 100, we are at 9.5 us per char
        //  - for a string of length 1000, we are at 65 us per char
        //  - for a string of length 10000, we are at 620 us per char
        // but with no AST construction we are getting no quadratic behavior and 1.6 micro seconds per character
        // - regex may slow things down
        // - computing Term.hashCode inside a function slows things down quite a bit
        // - constructing ASTs with long lists slows things down
        // - calling java.Object.hashCode is SLOOOOOOW
        // - calling RTTI versions of getStateCall, etc. are slow
    }

    public static long getCpuTime( ) {
        ThreadMXBean bean = ManagementFactory.getThreadMXBean();
        return bean.isCurrentThreadCpuTimeSupported( ) ?
                bean.getCurrentThreadCpuTime( ) : 0L;
    }

    private final ParseState s;

    public Parser(ParseState parseState) {
        s = parseState;
    }

    public Term parse(NonTerminal nt, int position) {
        // TODO ordering info should not rely only on integers
        // This code assumes that ordering info in the grammar are between MIN_VALUE+1 and MAX_VALUE-2
        NonTerminal startNt = new NonTerminal(new NonTerminalId("<start>"),
                                              new StateId("<start-entry>"), new State.OrderingInfo(Integer.MIN_VALUE),
                                              new StateId("<start-exit>"), new State.OrderingInfo(Integer.MAX_VALUE));
        State state = new NonTerminalState(new StateId("<start>"), startNt, new State.OrderingInfo(Integer.MAX_VALUE - 1), nt, true);

        // this lookahead must be true so that a new worklist is pushed on the stack
        activateNtCall(s.getStateCall(new StateCall.Key(s.getNtCall(new NonTerminalCall.Key(nt, position)), position, state)));

        while (s.stateReturnWorkLists.top() != null) {
            StateReturn stateReturn = null;
            while ((stateReturn = s.stateReturnWorkLists.top().dequeue()) != null) {
                this.stateReturn(stateReturn);
            }
            s.stateReturnWorkLists.pop();
        }

        Ambiguity result = new Ambiguity("K", new ArrayList<Term>());
        for(StateReturn stateReturn : s.getNtCall(new NonTerminalCall.Key(nt,0)).exitStateReturns) {
            if (stateReturn.key.stateEnd == s.input.length()) {
                for (KList klist : stateReturn.postRuleFunction.applyToNull()) {
                    result.getContents().add(klist);
                }
            }
        }
        return result;
    }

    private void unknownStateType() { assert false : "Unknown state type"; }

    /****************
     * State Return
     ****************/
    public void stateReturn(StateReturn stateReturn) {
        // Note that 'addPreRule' also puts the stateReturn in the work list
        // Note that 'addFunction' sets the call to use the top queue when a stateReturn is places
        // Note that 'addCaller' also sets up entry state

        stateReturn.postRuleFunction.addFactoredAndRunRule(stateReturn.preRuleFunction, stateReturn); // if lookahead, factors all results; always subjugates

        State state = stateReturn.key.stateCall.key.state;
        if (state instanceof ExitState) {
            // add exit state's function to all callers
            for (StateCall stateCall : stateReturn.key.stateCall.key.ntCall.callers) {
                int stateEnd = ((NonTerminalState)stateCall.key.state).isLookahead ? // we know a caller must be a NonTerminalState
                    stateCall.key.stateBegin :
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
                                       stateCall.function, Function.identity());
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

        NonTerminalCall ntCall = s.getNtCall(new NonTerminalCall.Key(((NonTerminalState)stateCall.key.state).child, stateCall.key.stateBegin));
        ntCall.callers.add(stateCall);

        StateCall entryStateCall = activateStateCall(new StateCall.Key(ntCall, ntCall.key.ntBegin, ntCall.key.nt.entryState), Function.identity());

        addPreRuleFunction(new StateReturn.Key(entryStateCall, ntCall.key.ntBegin), Function.identity(), Function.identity());
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
        // Add the state return to the NT call
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
