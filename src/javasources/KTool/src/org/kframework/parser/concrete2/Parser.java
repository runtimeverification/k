// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.Term;
import org.kframework.kil.Token;
import org.kframework.parser.concrete2.Grammar.EntryState;
import org.kframework.parser.concrete2.Grammar.ExitState;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.RegExState;
import org.kframework.parser.concrete2.Grammar.RuleState;
import org.kframework.parser.concrete2.Grammar.State;
import org.kframework.parser.concrete2.Rule.ContextFreeRule;
import org.kframework.parser.concrete2.Rule.ContextSensitiveRule;

/**
 * This is the main code for running the parser.
 *
 * ----------------
 * Terminology
 * ----------------
 *
 * entryState/exitState: the first and last states in a non-terminal
 *
 * stateCall/stateReturn: records for the entry to or exit from a state
 * ntCall/ntReturn: records for the entry to or exit from a non-terminal
 *
 * stateBegin/stateEnd: the source positions for the beginning and end the span of a state
 * ntBegin/ntEnd: the source positions for the beginning and end the span of a state
 *
 * nextState/previousState: successor/predecessor states in a state machine
 *
 * ----------------
 * ParseState
 * ----------------
 *
 * The parser operates by maintaining tables of NonTerminalCall,
 * StateCall and StateReturn records. These tables are stored
 * in ParseState and are keyed by NonTerminalCall.Key,
 * StateCall.Key and StateReturn.Key. For any given Key, there is
 * a single value that can be looked up with getNtCall(), getStateCall(),
 * and getStateReturn(). If no value exists for a given Key, then those
 * functions will create one.
 *
 * In addition to these tables, a work queue of StateReturn to be processed
 * is kept in StateReturnWorkList. This queue is ordered according to
 * StateReturn.compareTo() in such a way that it is impossible for a
 * StateReturn later in the queue to contribute to or influence a StateReturn
 * earlier in the queue.
 *
 * The main loop of the parser then processes elements in this queue until
 * it is empty.
 *
 * ----------------
 * NonTerminalCall
 * ----------------
 *
 * A NonTerminalCall represents the fact that the parser needs to try parsing
 * a particular NonTerminal (i.e., key.nt) starting at a particular position
 * (i.e., key.ntBegin).
 *
 * For each NonTerminalCall, we keep track of all StateCall
 * that triggered this NonTerminalCall (i.e., callers) so that when
 * the NonTerminalCall is finished, we can notify them of the successful parse.
 *
 * We also keep track of all StateReturns for the ExitState (i.e., exitStateReturns)
 * so that when a new StateCall activates this NonTerminalCall, we can notify
 * the StateCall of successful parses of this NonTerminalCall that are
 * already computed.
 *
 * We also keep track of all StateReturns in this NonTerminal that
 * should be added back on the work queue if we discover that this NonTerminalCall
 * is called from a new context (i.e., reactivations).  This is used
 * to handle context sensitivity.
 *
 * The contexts in which a NonTerminalCall is called are stored in a Context object
 * (i.e., 'context'). For now, contexts are limited to one layer and thus a context
 * might say that this NonTerminal is called from a StateCall that has thus far
 * parsed a '+(1,_)'.  This information is stored as a KList where the "_"
 * are omitted.  This is kept as a separate class because they might be extended
 * in the future.
 *
 * ----------------
 * StateCall
 * ----------------
 *
 * A StateCall represents the fact that the parser started parsing
 * a particular State (i.e., key.state) at a particular position
 * (i.e., key.stateBegin) while parsing a particular NonTerminalCall
 * (i.e., key.ntCall).
 *
 * For each StateCall, we keep track of the AST produced up to that point.
 * Since the AST produced may depend on the context in which the
 * NonTerminalCall associated with this StateCall (i.e., key.ntCall.context),
 * we do not simply store an AST but rather a function from individual contexts.
 * This is stored in the 'function' field.
 * (See the Function class for how that is implemented).
 *
 * ----------------
 * StateReturn
 * ----------------
 *
 * A StateReturn represents the fact that the parser finished parsing
 * something that was started by a particular StateCall (i.e., key.stateCall)
 * at a particular position (i.e. key.stateEnd).
 *
 * Just was with StateCall, a StateReturn stores the AST produced up to that
 * point as the 'function' field.
 *
 * ----------------
 * Context
 * ----------------
 *
 * See NonTerminalCall for an explanation of Context.
 *
 */
public class Parser {

    /**
     * The dynamic record for where a state starts parsing.
     */
    private static class StateCall {
        final Function function = Function.empty();

        private static class Key {
            final NonTerminalCall ntCall;
            final int stateBegin;
            final State state;

            public Key(NonTerminalCall ntCall, int stateBegin, State state) {
    //***************************** Start Boilerplate *****************************
                assert ntCall != null; assert state != null;
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
        final Key key;
        StateCall(Key key) { assert key != null; this.key = key; }

        public int hashCode() {
            return this.key.hashCode();
        }
    //***************************** End Boilerplate *****************************
    }

    /**
     *  The dynamic record for where a state ends parsing.
     */
    private static class StateReturn implements Comparable<StateReturn> {
        final Function function = Function.empty();

        public int compareTo(StateReturn that) {
            int x;
            return
                // The following idiom is a short-circuiting, integer "and"
                // that does a lexicographic ordering over:
                //  - ntBegin (contravariently),
                //  - nt.orderingInfo (not used until we get lookaheads fixed)
                //  - stateEnd,
                //  - state.orderingInfo,
                //  - stateBegin and
                //  - state.
                ((x = Integer.compare(that.key.stateCall.key.ntCall.key.ntBegin,
                                      this.key.stateCall.key.ntCall.key.ntBegin)) != 0) ? x :
                // TODO: ((x = this.key.stateCall.key.ntCall.key.nt.orderingInfo.compareTo(
                //             that.key.stateCall.key.ntCall.key.nt.orderingInfo)) != 0) ? x :
                ((x = Integer.compare(this.key.stateEnd, that.key.stateEnd)) != 0) ? x :
                ((x = this.key.stateCall.key.state.orderingInfo.compareTo(
                      that.key.stateCall.key.state.orderingInfo)) != 0) ? x :
                // NOTE: these last two comparisons are just so we don't conflate distinct values
                ((x = Integer.compare(this.key.stateCall.key.stateBegin,
                                      that.key.stateCall.key.stateBegin)) != 0) ? x :
                this.key.stateCall.key.state.compareTo(that.key.stateCall.key.state);
        }

        private static class Key {
            public final StateCall stateCall;
            public final int stateEnd;
            public Key(StateCall stateCall, int stateEnd) {
                assert stateCall != null;
                // if we are a lookahead, then force the the state end to be equal to the state begin
                if (stateCall.key.state instanceof NonTerminalState &&
                    ((NonTerminalState)stateCall.key.state).isLookahead) {
                    stateEnd = stateCall.key.stateBegin;
                }
    //***************************** Start Boilerplate *****************************
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

        final Key key;
        StateReturn(Key key) {
            this.key = key;
            //// NON-BOILERPLATE CODE: ////
            // update the NonTerminalCalls set of ExitStateReturns
            if (this.key.stateCall.key.state instanceof ExitState) {
                this.key.stateCall.key.ntCall.exitStateReturns.add(this);
            }
        }

        public int hashCode() {
            return this.key.hashCode();
        }
    //***************************** End Boilerplate *****************************
    }

    private static class Context {
        final Set<KList> contexts = new HashSet<>();
    }

    /**
     * The dynamic record for where a non-terminal starts parsing.
     */
    private static class NonTerminalCall {
        final Set<StateCall> callers = new HashSet<>();
        final Set<StateReturn> exitStateReturns = new HashSet<>();
        final Set<StateReturn> reactivations = new HashSet<>();
        final Context context = new Context();
        private static class Key {
            public final NonTerminal nt;
            public final int ntBegin;
    //***************************** Start Boilerplate *****************************
            public Key(NonTerminal nt, int ntBegin) {
                assert nt != null;
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
        final Key key;
        NonTerminalCall(Key key) { assert key != null; this.key = key; }

        public int hashCode() {
            return this.key.hashCode();
        }
    //***************************** End Boilerplate *****************************
    }

    ////////////////

    private static class StateReturnWorkList extends TreeSet<StateReturn> {
        public void enqueue(StateReturn stateReturn) { this.add(stateReturn); }
        public StateReturn dequeue() { return this.pollFirst(); }
    }

    /**
     * The state used internally by the parser.
     */
    private static class ParseState {
        // the input string which needs parsing
        final CharSequence input;
        // a priority queue containing the return states to be processed
        final StateReturnWorkList stateReturnWorkList = new StateReturnWorkList();
        // a preprocessed correspondence from index to line and column in the input string
        // TODO: replace lines and columns with Location class
        // TODO: extract Location class into it's own file
        final int[] lines;
        final int[] columns;
        public ParseState(CharSequence input) {
            /**
             * Create arrays corresponding to the index in the input CharSequence and the line and
             * column in the text. Tab counts as one.
             *
             * The newline characters are handled according to:
             * http://www.unicode.org/standard/reports/tr13/tr13-5.html
             * http://www.unicode.org/reports/tr18/#Line_Boundaries
             */
            this.input = input;
            lines = new int[input.length()+1];
            columns = new int[input.length()+1];
            int l = 1;
            int c = 1;
            for (int i = 0; i < input.length(); i++) {
                lines[i] = l;
                columns[i] = c;
                switch (input.charAt(i)) {
                    case '\r' :
                        if (i+1 < input.length()) {
                            if (input.charAt(i+1) == '\n') {
                                lines[i+1] = l;
                                columns[i+1] = c + 1;
                                i++;
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
            lines[input.length()] = l;
            columns[input.length()] = c;
        }

        private BiMap<NonTerminalCall.Key,NonTerminalCall> ntCalls = HashBiMap.create();
        private BiMap<StateCall.Key,StateCall> stateCalls = HashBiMap.create();
        private BiMap<StateReturn.Key,StateReturn> stateReturns = HashBiMap.create();

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

        public Set<StateCall.Key> getStateCallKeys() { return stateCalls.keySet(); }

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

    /**
     * A 'Function' represents a mapping from one or more 'Context's
     * to one or more ASTs.  'Function's are used throughout the parser
     * instead of manipulating ASTs in order to support context sensitivity.
     *
     * A 'Function' stores this mapping from a context to an AST as it's
     * 'mapping' field.  Their are two sorts of mappings: Nil and One.
     * A 'Nil' mapping does not depend on the context in any way.
     * In effect, it represents a constant 'Function' that ignores its argument.
     * A 'One' mapping, on the other hand, depends on one layer of context.
     * It does this by storing input/output pairs.  These pairs are populated
     * dynamically based on what input contexts actually occur, so this
     * mapping may grow when new contexts are added to a NonTerminalCall.
     * The reason we have both 'Nil' and 'One' is that several operations
     * on 'Nil' can be done much more efficiently than on a 'One'.
     */
    private static class Function {
        private abstract class Mapping {}
        private class Nil extends Mapping { Set<KList> values = new HashSet<>(); }
        private class One extends Mapping { Map<KList, Set<KList>> values = new HashMap<>(); }

        private Mapping mapping = new Nil();
        private AssertionError unknownMappingType() { return new AssertionError("Unknown mapping type"); }

        /**
         * The identity function that maps everything to a singleton containing an empty KList.
         * This is an identity because it maps every context to the KList.EMPTY which is the identity for KList.
         *
         * NOTE: It is important that this function is never mutated, but we have no good way
         * of enforcing this.
         */
        static final Function IDENTITY = new Function();
        static {
            ((Nil) IDENTITY.mapping).values.add(KList.EMPTY);
        }

        /**
         * Returns a function that maps everything to the empty set.
         * @return The newly created function.
         */
        static Function empty() { return new Function(); }

        /**
         * Converts a function containing a 'Nil' mapping to and equivalent one with
         * a 'One' mapping for the given contexts
         * @param contexts The contexts for which the 'One' should have mappings
         */
        private void promote(Set<KList> contexts) {
            assert this.mapping instanceof Nil;
            Set<KList> oldValues = ((Nil) this.mapping).values;
            this.mapping = new One();
            for (KList key : contexts) {
                // Java, why you no have copy constructor?!
                Set<KList> value = new HashSet<>();
                value.addAll(oldValues);
                ((One) this.mapping).values.put(key, value);
            }
        }

        /**
         * A helper function that adds the mappings in 'that' to 'this' after applying 'adder' to each mapping.
         * @param that     That 'Function' from which to get the mappings to be added to 'this'.
         * @param adder    The function to be applied to each value that a particular context is mapped to.
         * @return 'true' iff new mappings were added to this
         */
        private boolean addAux(Function that, com.google.common.base.Function<Set<KList>, Set<KList>> adder) {
            if (this.mapping instanceof Nil && that.mapping instanceof Nil) {
                return ((Nil) this.mapping).values.addAll(adder.apply(((Nil) that.mapping).values));
            } else if (this.mapping instanceof Nil && that.mapping instanceof One) {
                this.promote(((One) that.mapping).values.keySet());
                return this.addAux(that, adder);
            } else if (this.mapping instanceof One && that.mapping instanceof Nil) {
                boolean result = false;
                Set<KList> newValues = adder.apply(((Nil) that.mapping).values);
                for (Set<KList> values : ((One) this.mapping).values.values()) {
                    result |= values.addAll(newValues);
                }
                return result;
            } else if (this.mapping instanceof One && that.mapping instanceof One) {
                boolean result = false;
                for (KList key : ((One) that.mapping).values.keySet()) {
                    if (!((One) this.mapping).values.containsKey(key)) {
                        ((One) this.mapping).values.put(key, new HashSet<KList>());
                    }
                    result |= ((One) this.mapping).values.get(key).addAll(
                        adder.apply(((One) that.mapping).values.get(key)));
                }
                return result;
            } else { throw unknownMappingType(); }
        }

        /**
         * Get the set of KLists that this function maps to regardless of input (i.e., the range of this function).
         * @return The set of KLists that this function maps to
         */
        Set<KList> results() {
            if (this.mapping instanceof Nil) { return ((Nil) this.mapping).values; }
            else if (this.mapping instanceof One) {
                Set<KList> result = new HashSet<>();
                for (Set<KList> value: ((One) this.mapping).values.values()) {
                    result.addAll(value);
                }
                return result;
            } else { throw unknownMappingType(); }
        }

        /**
         * Returns the output of this function if it were applied to an empty (i.e., zero depth) context.
         * @return The output of this function applied to an empty context
         */
        Set<KList> applyToNull() {
            if (this.mapping instanceof Nil) { return ((Nil) this.mapping).values; }
            else { assert false : "unimplemented"; return null; } // TODO
        }

        /**
         * Adds all mappings in 'that' to 'this'
         * @param that    The 'Function' from which to add mappings
         * @return 'true' iff the mappings in this function changed
         */
        public boolean add(Function that) {
            return addAux(that, new com.google.common.base.Function<Set<KList>, Set<KList>>() {
                public Set<KList> apply(Set<KList> set) { return set; }
            });
        }

        /**
         * Add to 'this' all mappings formed by adding the token
         * 'string' of sort 'sort' to the end of the mapping in that.
         * @param that      The function from which
         * @param string    The token value
         * @param sort      The sort of the token
         * @return 'true' iff the mappings in this function changed.
         */
        boolean addToken(Function that, String string, String sort) {
            final KApp token = Token.kAppOf(sort, string);
            return addAux(that, new com.google.common.base.Function<Set<KList>, Set<KList>>() {
                public Set<KList> apply(Set<KList> set) {
                    Set<KList> result = new HashSet<>();
                    for (KList klist : set) {
                        KList newKList = new KList(klist);
                        newKList.add(token);
                        result.add(newKList);
                    }
                    return result;
                }
            });
        }

        /**
         * Add to this function the mappings resulting from composing mappings in call with the mappings in exit.
         * We do this in a way that matches up the contexts in 'exit' with the results in 'call'.
         *
         * This is used when the child (a NonTerminal) of a NonTerminalState finishes parsing.
         * In that case 'call' is the Function for the StateCall for that NonTerminalState and
         * 'exit' is the Function for the StateReturn of the ExitState in the NonTerminal.
         * @param call    The base function onto which 'exit' should be appended
         * @param exit    The function to append on 'call'
         * @return 'true' iff the mapping in this function changed
         */
        boolean addNTCall(Function call, final Function exit) {
            return addAux(call, new com.google.common.base.Function<Set<KList>, Set<KList>>() {
                public Set<KList> apply(Set<KList> set) {
                    Set<KList> result = new HashSet<>();
                    for (KList context : set) {
                        // find subset of exit that matches
                        Set<KList> matches = null;
                        if (exit.mapping instanceof Nil) {
                            matches = ((Nil) exit.mapping).values;
                        } else if (exit.mapping instanceof One) {
                            matches = ((One) exit.mapping).values.get(context);
                        } else { unknownMappingType(); }
                        // if we found some, make an amb node and append them to the KList
                        if (!matches.isEmpty()) {
                            KList newKList = new KList(context);
                            newKList.add(new Ambiguity(KSorts.K, new ArrayList<Term>(matches)));
                            result.add(newKList);
                        }
                    }
                    return result;
                }
            });
        }

        /**
         * Add to 'this', the mappings from 'that' after they have had 'rule' applied to them.
         *
         * NOTE: May also add 'stateReturn' to the 'reactivations' of the NonTerminalCall containing 'stateReturn'
         *
         * @param that           The function on which to apply 'rule'
         * @param rule           The 'Rule' to apply to the values in 'that'
         * @param stateReturn    The StateReturn containing the StateRule containing the Rule
         * @param metaData       Metadata about the current state of parsing (e.g., location information)
         *                       that the rule can use
         * @return 'true' iff the mapping in this function changed
         */
        boolean addRule(Function that, final Rule rule, final StateReturn stateReturn, final Rule.MetaData metaData) {
            if (rule instanceof ContextFreeRule) {
                return addAux(that, new com.google.common.base.Function<Set<KList>, Set<KList>>() {
                    public Set<KList> apply(Set<KList> set) {
                        return ((ContextFreeRule) rule).apply(set, metaData);
                    }
                });
            } else if (rule instanceof ContextSensitiveRule) {
                Set<KList> ntCallContexts = stateReturn.key.stateCall.key.ntCall.context.contexts;

                if (this.mapping instanceof Nil) { promote(ntCallContexts); }

                // Build a "promoted" version of "that"
                One promotedThat = null;
                if (that.mapping instanceof Nil) {
                    promotedThat = new One();
                    for (KList context : ntCallContexts) {
                        promotedThat.values.put(context, ((Nil) that.mapping).values);
                    }
                } else if (that.mapping instanceof One) {
                    promotedThat = ((One) that.mapping);
                } else { unknownMappingType(); }

                boolean result = false;
                for (KList key : promotedThat.values.keySet()) {
                    if (((One) this.mapping).values.get(key) == null) {
                        ((One) this.mapping).values.put(key, new HashSet<KList>());
                    }
                    result |= ((One) this.mapping).values.get(key).
                        addAll(((ContextSensitiveRule) rule).apply(key, promotedThat.values.get(key), metaData));
                }

                stateReturn.key.stateCall.key.ntCall.reactivations.add(stateReturn);

                return result;
            } else { throw unknownMappingType(); }
        }
    }

    ////////////////

    private final ParseState s;

    public Parser(CharSequence input) {
        s = new ParseState(input);
    }

    /**
     * Main function to run the parser.
     * @param nt the start non-terminal
     * @param position where to start parsing in the input string
     * @return the result of parsing, as a Term
     */
    public Term parse(NonTerminal nt, int position) {
        // This code assumes that ordering info in the grammar are between MIN_VALUE+1 and MAX_VALUE-2
        // TODO: can we do away with the <start> non-terminal?
        NonTerminal startNt = new NonTerminal("<start>");
        NonTerminalState state = new NonTerminalState("<start>", startNt, nt, false);
        startNt.entryState.next.add(state);
        state.next.add(startNt.exitState);

        startNt.entryState.orderingInfo = new State.OrderingInfo(Integer.MIN_VALUE);
        startNt.exitState.orderingInfo = new State.OrderingInfo(Integer.MAX_VALUE);
        state.orderingInfo = new State.OrderingInfo(Integer.MAX_VALUE - 1);

        activateStateCall(s.getStateCall(new StateCall.Key(s.getNtCall(
            new NonTerminalCall.Key(startNt, position)), position, startNt.entryState)),
            Function.IDENTITY);

        for (StateReturn stateReturn = null;
             (stateReturn = s.stateReturnWorkList.dequeue()) != null;) {
            this.workListStep(stateReturn);
        }

        Ambiguity result = new Ambiguity(KSorts.K, new ArrayList<Term>());
        for(StateReturn stateReturn : s.getNtCall(new NonTerminalCall.Key(nt,position)).exitStateReturns) {
            if (stateReturn.key.stateEnd == s.input.length()) {
                result.getContents().add(new KList(new Ambiguity(
                    KSorts.K, stateReturn.function.applyToNull())));
            }
        }
        return result;
    }

    /**
     * Looks through the list of possible parses and returns the ones that got the furthest
     * into the text.
     * @return a {@link ParseError} object containing all the possible parses that got to the
     * maximum point in the input string.
     */
    public ParseError getErrors() {
        int current = 0;
        for (StateCall.Key key : s.getStateCallKeys()) {
            if (key.state instanceof PrimitiveState)
                current = Math.max(current, key.stateBegin);
        }
        Set<Pair<String, Pattern>> tokens = new HashSet<>();
        for (StateCall.Key key : s.getStateCallKeys()) {
            if (key.state instanceof RegExState && key.stateBegin == current) {
                tokens.add(new ImmutablePair<>(
                    ((RegExState) key.state).sort, ((RegExState) key.state).pattern));
            }
        }
        return new ParseError(current, s.lines[current], s.columns[current], tokens);
    }

    /**
     * Contains the maximum position in the text which the parser managed to recognize.
     */
    public static class ParseError {
        // TODO: replace the fields below with Location class
        /// The character offset of the error
        public final int position;
        /// The column of the error
        public final int column;
        /// The line of the error
        public final int line;
        /// Pairs of Sorts and RegEx patterns that the parsed expected to occur next
        public final Set<Pair<String, Pattern>> tokens;

        public ParseError(int position, int line, int column, Set<Pair<String, Pattern>> tokens) {
            assert tokens != null;
            this.position = position;
            this.tokens = tokens;
            this.column = column;
            this.line = line;
        }
    }

    private AssertionError unknownStateType() { return new AssertionError("Unknown state type"); }

    /****************
     * State Return
     ****************/

    // finish the process of one state return from the work list
    private void workListStep(StateReturn stateReturn) {
        if (finishStateReturn(stateReturn)) {
            State state = stateReturn.key.stateCall.key.state;
            if (state instanceof ExitState) {
                for (StateCall stateCall : stateReturn.key.stateCall.key.ntCall.callers) {
                    s.stateReturnWorkList.enqueue(
                        s.getStateReturn(
                            new StateReturn.Key(stateCall, stateReturn.key.stateEnd)));
                }
            } else if (state instanceof NextableState) {
                for (State nextState : ((NextableState) state).next) {
                    activateStateCall(s.getStateCall(new StateCall.Key(
                        stateReturn.key.stateCall.key.ntCall, stateReturn.key.stateEnd, nextState)),
                        stateReturn.function);
                }
            } else { throw unknownStateType(); }
        }
    }

    // compute the Function for a state return based on the Function for the state call associated
    // with the state return, and the type of the state
    private boolean finishStateReturn(StateReturn stateReturn) {
        if (stateReturn.key.stateCall.key.state instanceof EntryState) {
            return stateReturn.function.add(stateReturn.key.stateCall.function);
        } else if (stateReturn.key.stateCall.key.state instanceof ExitState) {
            return stateReturn.function.add(stateReturn.key.stateCall.function);
        } else if (stateReturn.key.stateCall.key.state instanceof PrimitiveState) {
            return stateReturn.function.addToken(stateReturn.key.stateCall.function,
                s.input.subSequence(stateReturn.key.stateCall.key.stateBegin,
                    stateReturn.key.stateEnd).toString(),
                ((PrimitiveState) stateReturn.key.stateCall.key.state).sort);
        } else if (stateReturn.key.stateCall.key.state instanceof RuleState) {
            int startPosition = stateReturn.key.stateCall.key.ntCall.key.ntBegin;
            int endPosition = stateReturn.key.stateEnd;
            return stateReturn.function.addRule(stateReturn.key.stateCall.function,
                ((RuleState) stateReturn.key.stateCall.key.state).rule, stateReturn,
                new Rule.MetaData(
                    new Rule.MetaData.Location(startPosition, s.lines[startPosition], s.columns[startPosition]),
                    new Rule.MetaData.Location(endPosition, s.lines[endPosition], s.columns[endPosition])));
        } else if (stateReturn.key.stateCall.key.state instanceof NonTerminalState) {
            return stateReturn.function.addNTCall(
                stateReturn.key.stateCall.function,
                s.getStateReturn(new StateReturn.Key(
                    s.getStateCall(new StateCall.Key(
                        s.getNtCall(new NonTerminalCall.Key(
                            ((Grammar.NonTerminalState) stateReturn.key.stateCall.key.state).child,
                            stateReturn.key.stateCall.key.stateBegin)),
                        stateReturn.key.stateEnd,
                        ((Grammar.NonTerminalState) stateReturn.key.stateCall.key.state).child.exitState)),
                    stateReturn.key.stateEnd)).function);
        } else { throw unknownStateType(); }
    }

    // copy Function from state return to next state call
    // also put state return in the queue if need be
    private void activateStateCall(StateCall stateCall, Function function) {
        if (!stateCall.function.add(function)) { return; }
        State nextState = stateCall.key.state;
        // These types of states
        if (nextState instanceof EntryState ||
            nextState instanceof ExitState ||
            nextState instanceof RuleState) {
            s.stateReturnWorkList.enqueue(
                s.getStateReturn(
                    new StateReturn.Key(stateCall, stateCall.key.stateBegin)));
        } else if (nextState instanceof PrimitiveState) {
            for (PrimitiveState.MatchResult matchResult :
                    ((PrimitiveState)nextState).matches(s.input, stateCall.key.stateBegin)) {
                s.stateReturnWorkList.enqueue(
                    s.getStateReturn(
                        new StateReturn.Key(stateCall, matchResult.matchEnd)));
            }
        // not instanceof SimpleState
        } else if (nextState instanceof NonTerminalState) {
            // make sure lookaheads have a stateReturn even if empty
            if (((NonTerminalState) nextState).isLookahead) {
                s.stateReturnWorkList.enqueue(
                    s.getStateReturn(
                        new StateReturn.Key(stateCall, stateCall.key.stateBegin)));
            }
            // add to the ntCall
            NonTerminalCall ntCall = s.getNtCall(new NonTerminalCall.Key(
                ((NonTerminalState) nextState).child, stateCall.key.stateBegin));
            ntCall.callers.add(stateCall);
            if (ntCall.context.contexts.addAll(stateCall.function.results())) {
                // enqueues anything sensitive
                s.stateReturnWorkList.addAll(ntCall.reactivations);
            }
            // activate the entry state call (almost like activateStateCall but we have no stateReturn)
            StateCall entryStateCall = s.getStateCall(new StateCall.Key(
                ntCall, stateCall.key.stateBegin, ntCall.key.nt.entryState));
            activateStateCall(entryStateCall, Function.IDENTITY);
            // process existStateReturns already done in the ntCall
            for (StateReturn exitStateReturn : ntCall.exitStateReturns) {
                s.stateReturnWorkList.enqueue(
                    s.getStateReturn(
                        new StateReturn.Key(stateCall, exitStateReturn.key.stateEnd)));
            }
        } else { throw unknownStateType(); }
    }
}
