// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.kernel;

import org.apache.commons.codec.binary.StringUtils;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.inner.kernel.Grammar.EntryState;
import org.kframework.parser.inner.kernel.Grammar.ExitState;
import org.kframework.parser.inner.kernel.Grammar.NextableState;
import org.kframework.parser.inner.kernel.Grammar.NonTerminal;
import org.kframework.parser.inner.kernel.Grammar.NonTerminalState;
import org.kframework.parser.inner.kernel.Grammar.PrimitiveState;
import org.kframework.parser.inner.kernel.Grammar.RegExState;
import org.kframework.parser.inner.kernel.Grammar.RuleState;
import org.kframework.parser.inner.kernel.Grammar.State;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * This is the main code for running the parser.
 *
 * ----------------
 * Overview
 * ----------------
 *
 * The parser operates by maintaining tables of {@link NonTerminalCall},
 * {@link StateCall} and {@link StateReturn} records. These tables are stored
 * in ParseState and are keyed by {@link NonTerminalCall.Key},
 * {@link StateCall.Key} and {@link StateReturn.Key}. For any given Key, there is
 * a single value that can be looked up in an {@link AutoVivifyingBiMap}.
 * If no value exists for a given Key, then the {@link AutoVivifyingBiMap}
 * will create one.
 *
 * In addition to these tables, a work queue of {@link StateReturn}s
 * to be processed is kept in {@link StateReturnWorkList}.
 * This queue is ordered according to {@link StateReturn#compareTo(StateReturn)}
 * in such a way that it is impossible for a {@link StateReturn} later
 * in the queue to contribute to or influence a {@link StateReturn}
 * earlier in the queue.
 *
 * The main loop of the parser then processes elements in this queue until
 * it is empty.
 *
 * See {@link NonTerminalCall}, {@link StateCall} and {@link StateReturn}
 * (preferably in that order) for more information.
 *
 * ----------------
 * Terminology
 * ----------------
 *
 * In talking about the parser we have adopted the following naming conventions:
 *
 *  - entry/exit: the (static) start/end states of a non-terminal
 *  - call/return: the (dynamic) record for the start/end of a parse
 *  - begin/end: the start/end positions of a parse
 *  - position: a character index in a string
 *  - next/previous: next/previous edges in the state machine
 *
 * Thus we have the following terms:
 *
 *  - entry state/exit state: the first and last states in a non-terminal
 *
 *  - state call/state return: records for the entry to or exit from a state
 *  - non-terminal call: record for the entry to a non-terminal
 *
 *  - state begin/state end: the source positions for the beginning and end the span of a state
 *  - non-terminal begin: the source positions for the beginning of the span of a non-terminal
 *
 *  - next state/previous state: successor/predecessor states in a state machine
 */
public class Parser {

    /**
     * A StateCall represents the fact that the parser started parsing
     * a particular {@link State} (i.e., key.state) at a particular position
     * (i.e., key.stateBegin) while parsing a particular {@link NonTerminalCall}
     * (i.e., key.ntCall).
     *
     * For each StateCall, we keep track of the AST produced up to that point.
     * Since the AST produced may depend on the context in which the
     * {@link NonTerminalCall} associated with this StateCall
     * (i.e., key.ntCall.context), we do not simply store an AST
     * but rather a function from individual contexts.
     * This is stored in the 'function' field.
     * (See the {@link Function} class for how that is implemented).
     */
    public static class StateCall {
        /** The {@link Function} storing the AST parsed so far */
        final Function function = Function.empty();

        public static class Key {
            /** The {@link NonTerminalCall} containing this StateCall */
            final NonTerminalCall ntCall;
            /** The start position of this StateCall */
            final int stateBegin;
            /** The {@link State} that this StateCall is for */
            public final State state;

            private final int hashCode;

            //***************************** Start Boilerplate *****************************
            public Key(NonTerminalCall ntCall, int stateBegin, State state) {
                assert ntCall != null; assert state != null;
                this.ntCall = ntCall; this.stateBegin = stateBegin; this.state = state;
                this.hashCode = computeHash();
            }

            public StateCall create() { return new StateCall(this); }

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
                return hashCode;
            }
            public int computeHash() {
                int result = ntCall.key.hashCode();
                result = 31 * result + stateBegin;
                result = 31 * result + state.hashCode();
                return result;
            }

            @Override
            public String toString() {
                return ntCall.key.nt.name + "." + state.name + " @ "+ stateBegin;
            }
        }
        public final Key key;
        StateCall(Key key) { assert key != null; this.key = key; }

        public int hashCode() {
            return this.key.hashCode();
        }
        //***************************** End Boilerplate *****************************
    }

    /**
     * A StateReturn represents the fact that the parser finished parsing
     * something that was started by a particular {@link StateCall}
     * (i.e., key.stateCall) at a particular position (i.e. key.stateEnd).
     *
     * Just was with {@link StateCall}, a StateReturn stores the AST produced up to that
     * point as the 'function' field.
     */
    public static class StateReturn implements Comparable<StateReturn> {
        /** The {@link Function} storing the AST parsed so far */
        final Function function = Function.empty();

        private final int[] orderingInfo = new int[5];

        public int compareTo(StateReturn that) {
            // The following idiom is a short-circuiting, integer "and
            // that does a lexicographic ordering over:
            //  - ntBegin (contravariently),
            //  - nt.orderingInfo (not used until we get lookaheads fixed)
            //  - stateEnd,
            //  - state.orderingInfo,
            //  - stateBegin and
            //  - state.
            // NOTE: these last two comparisons are just so we don't conflate distinct values

            int v1[] = orderingInfo;
            int v2[] = that.orderingInfo;

            int k = 1;
            int c1 = v2[0];
            int c2 = v1[0];
            if (c1 != c2) {
                return c1 - c2;
            }
            while (k < 5) {
                c1 = v1[k];
                c2 = v2[k];
                if (c1 != c2) {
                    return c1 - c2;
                }
                k++;
            }
            return 0;
        }

        public static class Key {
            /** The {@link StateCall} that this StateReturn finishes */
            public final StateCall stateCall;
            /** The end position of the parse */
            public final int stateEnd;
            private final int hashCode;
            public Key(StateCall stateCall, int stateEnd) {
                assert stateCall != null;
                //***************************** Start Boilerplate *****************************
                this.stateCall = stateCall; this.stateEnd = stateEnd;
                this.hashCode = computeHash();
            }

            public StateReturn create() { return new StateReturn(this); }

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
                return hashCode;
            }

            public int computeHash() {
                int result = stateCall.key.hashCode();
                result = 31 * result + stateEnd;
                return result;
            }

            @Override
            public String toString() {
                return stateCall.key.toString() + "-" + stateEnd;
            }
        }

        public final Key key;
        StateReturn(Key key) {
            this.key = key;
            this.orderingInfo[0] = this.key.stateCall.key.ntCall.key.ntBegin;
            this.orderingInfo[1] = this.key.stateEnd;
            this.orderingInfo[2] = this.key.stateCall.key.state.orderingInfo.key;
            this.orderingInfo[3] = this.key.stateCall.key.stateBegin;
            this.orderingInfo[4] = this.key.stateCall.key.state.unique;
            //// NON-BOILERPLATE CODE: ////
            // update the NonTerminalCalls set of ExitStateReturns
            if (this.key.stateCall.key.state instanceof ExitState) {
                this.key.stateCall.key.ntCall.exitStateReturns.add(this);
            }
        }
        @Override
        public int hashCode() {
            return key.hashCode;
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            StateReturn other = (StateReturn) obj;
            if (key == null) {
                if (other.key != null)
                    return false;
            } else if (!key.equals(other.key))
                return false;
            return true;
        }

        //***************************** End Boilerplate *****************************
    }

    /**
     * A NonTerminalCall represents the fact that the parser needs to try parsing
     * a particular {@link NonTerminal} (i.e., key.nt) starting at a particular position
     * (i.e., key.ntBegin).
     *
     * For each NonTerminalCall, we keep track of all {@link StateCall}
     * that triggered this NonTerminalCall (i.e., callers) so that when
     * the NonTerminalCall is finished, we can notify them of the successful parse.
     *
     * We also keep track of all {@link StateReturn}s for the {@link ExitState} (i.e., exitStateReturns)
     * so that when a new StateCall activates this NonTerminalCall, we can notify
     * the StateCall of successful parses of this NonTerminalCall that are
     * already computed.
     *
     * We also keep track of all {@link StateReturn}s in this NonTerminalCall that
     * should be added back on the work queue if we discover that this NonTerminalCall
     * is called from a new context (i.e., reactivations).  This is used
     * to handle context sensitivity.
     */
    private static class NonTerminalCall {
        /** The {@link StateCall}s that call this NonTerminalCall */
        final Set<StateCall> callers = new HashSet<>();
        /** The {@link StateReturn}s for the {@link ExitState} in this NonTerminalCall */
        final Set<StateReturn> exitStateReturns = new HashSet<>();
        private static class Key {
            /** The {@link NonTerminal} being called */
            public final NonTerminal nt;
            /** The start position for parsing the {@link NonTerminal} */
            public final int ntBegin;
            private final int hashCode;
            //***************************** Start Boilerplate *****************************
            public Key(NonTerminal nt, int ntBegin) {
                assert nt != null;
                // assert ntBegin == c.stateBegin for c in callers
                this.nt = nt; this.ntBegin = ntBegin;
                this.hashCode = computeHash();
            }

            public NonTerminalCall create() { return new NonTerminalCall(this); }

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
                return hashCode;
            }

            public int computeHash() {
                int result = nt.hashCode();
                result = 31 * result + ntBegin;
                return result;
            }

            @Override
            public String toString() {
                return nt.name + " @ " + ntBegin;
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

    private static class StateReturnWorkList {
        private final HashSet<StateReturn> contains = new HashSet<>();
        private final TreeSet<StateReturn> ordering = new TreeSet<>();
        public void enqueue(StateReturn stateReturn) {
            if (!contains.add(stateReturn)) return;
            ordering.add(stateReturn);
        }
        public void addAll(Set<? extends StateReturn> c) {
            if (!contains.addAll(c)) return;
            ordering.addAll(c);
        }
        public StateReturn dequeue() {
            StateReturn next = ordering.pollFirst();
            contains.remove(next);
            return next;
        }
    }

    /**
     * The state used internally by the parser.
     */
    private static class ParseState {
        // the input string which needs parsing
        final Scanner.Token[] input;
        final String originalInput;
        // a priority queue containing the return states to be processed
        final StateReturnWorkList stateReturnWorkList = new StateReturnWorkList();
        // a preprocessed correspondence from index to line and column in the input string
        // TODO: replace lines and columns with Location class
        // TODO: extract Location class into it's own file
        final int[] lines;
        final int[] columns;
        private int maxPosition = 0;
        private final Source source;
        Map<NonTerminalCall.Key, NonTerminalCall> ntCalls = new HashMap<>();
        Map<StateCall.Key, StateCall> stateCalls = new HashMap<>();
        Map<StateReturn.Key, StateReturn> stateReturns = new HashMap<>();

        public ParseState(String input, Scanner scanner, Source source, int startLine, int startColumn) {
            /**
             * Create arrays corresponding to the index in the input CharSequence and the line and
             * column in the text. Tab counts as one.
             *
             * The newline characters are handled according to:
             * http://www.unicode.org/standard/reports/tr13/tr13-5.html
             * http://www.unicode.org/reports/tr18/#Line_Boundaries
             */
            this.originalInput = input;
            this.source = source;
            byte[] utf8 = StringUtils.getBytesUtf8(input);
            lines = new int[utf8.length+1];
            columns = new int[utf8.length+1];
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
            this.input = scanner.tokenize(input, source, lines, columns);
        }
    }

    ////////////////

    /**
     * A Function represents an ASTs.
     */
    private static class Function {
        /**
         * The identity function that maps everything to a singleton containing an empty KList.
         *
         * NOTE: It is important that this function is never mutated, but we have no good way
         * of enforcing this.
         */
        static final Function IDENTITY = new Function();

        /** The AST that this Function represents */
        private Set<Term> values = new HashSet<>();
        static {
            IDENTITY.values.add(KList.apply(ConsPStack.empty()));
        }

        /**
         * Returns a function that maps everything to the empty set.
         * @return The newly created function.
         */
        static Function empty() { return new Function(); }

        /**
         * A helper function that adds the mappings in 'that' to 'this' after applying 'adder' to each mapping.
         * @param that     That 'Function' from which to get the mappings to be added to 'this'.
         * @param adder    The function to be applied to each value that a particular context is mapped to.
         * @return 'true' iff new mappings were added to this
         */
        private boolean addAux(Function that, com.google.common.base.Function<Set<Term>, Set<Term>> adder) {
            return this.values.addAll(adder.apply(that.values));
        }

        /**
         * Adds all mappings in 'that' to 'this'
         * @param that    The 'Function' from which to add mappings
         * @return 'true' iff the mappings in this function changed
         */
        public boolean add(Function that) {
            return this.values.addAll(that.values);
        }

        /**
         * Add to this function the mappings resulting from composing mappings in call with the mappings in exit.
         *
         * This is used when the child (a {@link NonTerminal}) of a {@link NonTerminalState} finishes parsing.
         * In that case 'call' is the Function for the {@link StateCall} for that {@link NonTerminalState} and
         * 'exit' is the Function for the {@link StateReturn} of the {@link ExitState} in the {@link NonTerminal}.
         * @param call    The base function onto which 'exit' should be appended
         * @param exit    The function to append on 'call'
         * @return 'true' iff the mapping in this function changed
         */
        boolean addNTCall(Function call, final Function exit) {
            return addAux(call, set -> {
                Set<Term> result = new HashSet<>();
                if (!exit.values.isEmpty()) {
                    // if we found some, make an amb node and append them to the KList
                    for (Term context : set) {
                        if (exit.values.size() == 1) {
                            result.add(((KList)context).add(exit.values.iterator().next()));
                        } else {
                            result.add(((KList) context).add(Ambiguity.apply(exit.values)));
                        }
                    }
                }
                return result;
            });
        }

        /**
         * Add to 'this', the mappings from 'that' after they have had 'rule' applied to them.
         *
         *
         * @param that           The function on which to apply 'rule'
         * @param rule           The 'Rule' to apply to the values in 'that'
         * @param stateReturn    The StateReturn containing the StateRule containing the Rule
         * @param metaData       Metadata about the current state of parsing (e.g., location information)
         *                       that the rule can use
         * @return 'true' iff the mapping in this function changed
         */
        boolean addRule(Function that, final Rule rule, final StateReturn stateReturn, final Rule.MetaData metaData) {
            return addAux(that, set -> rule.apply(set, metaData));
        }
    }

    ////////////////

    private final ParseState s;

    public Parser(String input, Scanner scanner) {
        s = new ParseState(input, scanner, Source.apply("<unknown>"), 1, 1);
    }

    public Parser(String input, Scanner scanner, Source source, int startLine, int startColumn) {
        s = new ParseState(input, scanner, source, startLine, startColumn);
    }

    /**
     * Main function to run the parser.
     * @param nt the start non-terminal
     * @param position where to start parsing in the input string
     * @return the result of parsing, as a Term
     */
    public Term parse(NonTerminal nt, int position) {
        assert nt != null : "Start symbol cannot be null.";
        activateStateCall(s.stateCalls.computeIfAbsent(new StateCall.Key(s.ntCalls.computeIfAbsent(
            new NonTerminalCall.Key(nt, position), NonTerminalCall.Key::create), position, nt.entryState), StateCall.Key::create),
            Function.IDENTITY);

        for (StateReturn stateReturn;
             (stateReturn = s.stateReturnWorkList.dequeue()) != null;) {
            this.workListStep(stateReturn);
        }

        Set<Term> resultSet = new HashSet<>();
        for(StateReturn stateReturn : s.ntCalls.computeIfAbsent(new NonTerminalCall.Key(nt, position), NonTerminalCall.Key::create).exitStateReturns) {
            if (stateReturn.key.stateEnd == s.input.length) {
                resultSet.add(KList.apply(ConsPStack.singleton(Ambiguity.apply(stateReturn.function.values))));
            }
        }
        Ambiguity result = Ambiguity.apply(resultSet);

        if(result.items().size() == 0) {
            ParseError perror = getErrors();

            String msg = s.input.length == perror.position ?
                    "Parse error: unexpected end of file" :
                    "Parse error: unexpected token '" + s.input[perror.position].value + "'";
            if (perror.position != 0) {
                msg = msg + " following token '" + s.input[perror.position - 1].value + "'.";
            } else {
                msg = msg + ".";
            }
            Location loc = new Location(perror.startLine, perror.startColumn,
                    perror.endLine, perror.endColumn);
            Source source = perror.source;
            throw KEMException.innerParserError(msg, source, loc);
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
        for (StateCall.Key key : s.stateCalls.keySet()) {
            if (key.state instanceof PrimitiveState)
                current = Math.max(current, key.stateBegin);
        }
        current = Math.max(current, s.maxPosition);
        Set<Pair<Production, RegExState>> tokens = new HashSet<>();
        for (StateCall.Key key : s.stateCalls.keySet()) {
            if (key.state instanceof RegExState && key.stateBegin == s.maxPosition) {
                tokens.add(new ImmutablePair<>(
                    null, ((RegExState) key.state)));
            }
        }
        if (s.input.length == 0) {
            return new ParseError(s.source, current, s.lines[0], s.columns[0],
                    s.lines[0], s.columns[0] + 1, tokens);
        }
        if (current == s.input.length) {
            Scanner.Token t = s.input[current - 1];
            return new ParseError(s.source, current, s.lines[t.endLoc], s.columns[t.endLoc],
                    s.lines[t.endLoc], s.columns[t.endLoc] + 1, tokens);
        } else {
            return new ParseError(s.source, current, s.lines[s.input[current].startLoc], s.columns[s.input[current].startLoc],
                    s.lines[s.input[current].endLoc], s.columns[s.input[current].endLoc], tokens);
        }
    }

    /**
     * Contains the maximum position in the text which the parser managed to recognize.
     */
    public static class ParseError {
        /// The character offset of the error
        public final Source source;
        public final int position;
        public final int startColumn;
        public final int startLine;
        public final int endColumn;
        public final int endLine;
        /// Pairs of Sorts and RegEx patterns that the parsed expected to occur next
        public final Set<Pair<Production, RegExState>> tokens;

        public ParseError(Source source, int position, int startLine, int startColumn, int endLine, int endColumn, Set<Pair<Production, RegExState>> tokens) {
            this.startColumn = startColumn;
            this.endColumn = endColumn;
            this.startLine = startLine;
            this.endLine = endLine;
            assert tokens != null;
            this.source = source;
            this.position = position;
            this.tokens = tokens;
        }
    }

    private AssertionError unknownStateType() { return new AssertionError("Unknown state type"); }

    // finish the process of one state return from the work list
    private void workListStep(StateReturn stateReturn) {
        if (finishStateReturn(stateReturn)) {
            State state = stateReturn.key.stateCall.key.state;
            if (state instanceof ExitState) {
                for (StateCall stateCall : stateReturn.key.stateCall.key.ntCall.callers) {
                    s.stateReturnWorkList.enqueue(
                        s.stateReturns.computeIfAbsent(
                                new StateReturn.Key(stateCall, stateReturn.key.stateEnd), StateReturn.Key::create));
                }
            } else if (state instanceof NextableState) {
                for (State nextState : ((NextableState) state).next) {
                    activateStateCall(s.stateCalls.computeIfAbsent(new StateCall.Key(
                        stateReturn.key.stateCall.key.ntCall, stateReturn.key.stateEnd, nextState), StateCall.Key::create),
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
            return stateReturn.function.add(stateReturn.key.stateCall.function);
        } else if (stateReturn.key.stateCall.key.state instanceof RuleState) {
            int startPosition, endPosition;
            if (s.input.length == 0) {
                startPosition = 0;
                endPosition = 0;
            } else {
                if (stateReturn.key.stateCall.key.ntCall.key.ntBegin == s.input.length) {
                    startPosition = s.input[s.input.length - 1].endLoc;
                } else {
                    startPosition = s.input[stateReturn.key.stateCall.key.ntCall.key.ntBegin].startLoc;
                }
                if (stateReturn.key.stateEnd == 0) {
                    endPosition = s.input[0].startLoc;
                } else {
                    endPosition = s.input[stateReturn.key.stateEnd - 1].endLoc;
                }
            }
            return stateReturn.function.addRule(stateReturn.key.stateCall.function,
                ((RuleState) stateReturn.key.stateCall.key.state).rule, stateReturn,
                new Rule.MetaData(s.source,
                    new Rule.MetaData.Location(startPosition, s.lines[startPosition], s.columns[startPosition]),
                    new Rule.MetaData.Location(endPosition, s.lines[endPosition], s.columns[endPosition]),
                    s.originalInput));
        } else if (stateReturn.key.stateCall.key.state instanceof NonTerminalState) {
            return stateReturn.function.addNTCall(
                stateReturn.key.stateCall.function,
                s.stateReturns.computeIfAbsent(new StateReturn.Key(
                    s.stateCalls.computeIfAbsent(new StateCall.Key(
                        s.ntCalls.computeIfAbsent(new NonTerminalCall.Key(
                                ((Grammar.NonTerminalState) stateReturn.key.stateCall.key.state).child,
                                stateReturn.key.stateCall.key.stateBegin), NonTerminalCall.Key::create),
                        stateReturn.key.stateEnd,
                        ((Grammar.NonTerminalState) stateReturn.key.stateCall.key.state).child.exitState), StateCall.Key::create),
                    stateReturn.key.stateEnd), StateReturn.Key::create).function);
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
                s.stateReturns.computeIfAbsent(
                    new StateReturn.Key(stateCall, stateCall.key.stateBegin), StateReturn.Key::create));
        } else if (nextState instanceof PrimitiveState) {
            if (((PrimitiveState)nextState).matches(s.input, stateCall.key.stateBegin)) {
                s.stateReturnWorkList.enqueue(
                    s.stateReturns.computeIfAbsent(
                            new StateReturn.Key(stateCall, stateCall.key.stateBegin + 1), StateReturn.Key::create));
            }
        // not instanceof SimpleState
        } else if (nextState instanceof NonTerminalState) {
            // add to the ntCall
            NonTerminal nt = ((NonTerminalState)nextState).child;
            if (nt.nullable() || (stateCall.key.stateBegin < s.input.length && nt.lookahead(s.input[stateCall.key.stateBegin].kind))) {
                NonTerminalCall ntCall = s.ntCalls.computeIfAbsent(new NonTerminalCall.Key(
                        nt, stateCall.key.stateBegin), NonTerminalCall.Key::create);
                ntCall.callers.add(stateCall);
                // activate the entry state call (almost like activateStateCall but we have no stateReturn)
                StateCall entryStateCall = s.stateCalls.computeIfAbsent(new StateCall.Key(
                        ntCall, stateCall.key.stateBegin, ntCall.key.nt.entryState), StateCall.Key::create);
                activateStateCall(entryStateCall, Function.IDENTITY);
                // process existStateReturns already done in the ntCall
                for (StateReturn exitStateReturn : ntCall.exitStateReturns) {
                    s.stateReturnWorkList.enqueue(
                            s.stateReturns.computeIfAbsent(
                                    new StateReturn.Key(stateCall, exitStateReturn.key.stateEnd), StateReturn.Key::create));
                }
            } else {
                // we don't create an entry in the map for this statecall, so we need to track its location another way.
                s.maxPosition = Math.max(s.maxPosition, stateCall.key.stateBegin);
            }
        } else { throw unknownStateType(); }
    }
}
