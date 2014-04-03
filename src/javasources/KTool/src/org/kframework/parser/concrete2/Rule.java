package org.kframework.parser.concrete2;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.kil.KApp;
import org.kframework.kil.KLabel;
import org.kframework.kil.KList;
import org.kframework.kil.Term;

/**
 * An action that transforms an AST into another AST
 */
public abstract class Rule implements Serializable {
    /**
     * Metadata used to inform a rule about the current parse.
     */
    static class MetaData {
        public final int startPosition;
        public final int startLine;
        public final int startColumn;
        public final int endPosition;
        public final int endLine;
        public final int endColumn;
        public MetaData(int startPosition, int startLine, int startColumn, int endPosition, int endLine, int endColumn) {
            this.startPosition = startPosition; this.startLine = startLine; this.startColumn = startColumn;
            this.endPosition = endPosition; this.endLine = endLine; this.endColumn = endColumn;
        }
    }

    /**
     * A rule who's action does not depend on the context in which the parse occurs.
     */
    public static abstract class ContextFreeRule extends Rule {
        public abstract Set<KList> apply(Set<KList> set, MetaData metaData);
    }

    /**
     * Helper class for rules that treat each KList passed to apply() independently from each other
     */
    public static abstract class KListRule extends ContextFreeRule {
        public Set<KList> apply(Set<KList> set, MetaData metaData) {
            Set<KList> result = new HashSet<>();
            for (KList klist : set) {
                KList newKList = this.apply(klist, metaData);
                if (newKList != null) {
                    result.add(newKList);
                }
            }
            return result;
        }
        protected abstract KList apply(KList set, MetaData metaData);
    }

    /**
     * Wraps the current KList with the given KLabel
     */
    public static class WrapLabelRule extends KListRule {
        private final KLabel label;
        private final String sort;
        public WrapLabelRule(KLabel label, String sort) { this.label = label; this.sort = sort; }
        protected KList apply(KList klist, MetaData metaData) {
            Term term = new KApp(label, klist);
            term.setSort(this.sort);
            return new KList(Arrays.<Term>asList(term));
        }
    }

    /**
     * Helper class for rules that consider only the last few elements of a KList
     */
    public static abstract class SuffixRule extends KListRule {
        /** Returns true iff a KList should be rejected if it doesn't have enough elements */
        protected abstract boolean rejectSmallKLists();
        /** Returns the number of elements at the end of a KList to consider */
        protected abstract int getSuffixLength();
        /** Transforms the last {@link getSuffixLength()} elements of a KList */
        protected abstract Result applySuffix(List<Term> suffix, MetaData metaData);

        /** Determines what should be done with the entire KList */
        protected abstract class Result {}
        /** Reject the entire KList */
        protected class Reject extends Result {}
        /** Keep the KList unchanged */
        protected class Original extends Result {}
        /** Change the last {@link getSuffixLength()} elements to the ones in {@link list} */
        protected class Accept extends Result {
            List<Term> list;
            public Accept(List<Term> list) { this.list = list; }
        }

        protected KList apply(KList klist, MetaData metaData) {
            List<Term> terms = klist.getContents();
            int i = terms.size() - this.getSuffixLength();
            if (i < 0) {
                return this.rejectSmallKLists() ? null : klist;
            } else {
                List<Term> suffix = new ArrayList<>();
                for (; i < terms.size(); i++) {
                    suffix.add(terms.get(i));
                }
                Result result = this.applySuffix(suffix, metaData);
                if (result instanceof Reject) {
                    return null;
                } else if (result instanceof Original) {
                    return klist;
                } else if (result instanceof Accept) {
                    KList prefix = new KList(klist);
                    for (int j = terms.size() - 1;
                         j >= terms.size() - this.getSuffixLength(); j--) {
                        prefix.getContents().remove(j);
                    }
                    for (Term term : ((Accept) result).list) {
                        prefix.add(term);
                    }
                    return prefix;
                } else { assert false : "impossible"; return null; }
            }
        }
    }

    /**
     * Delete the last few elements added to the KList.
     * Usually used to remove whitespace and tokens
     */
    public static class DeleteRule extends SuffixRule {
        private final int length;
        private final boolean reject;
        public DeleteRule(int length, boolean reject) {
            this.length = length; this.reject = reject;
        }

        protected boolean rejectSmallKLists() { return reject; }
        protected int getSuffixLength() { return length; }
        protected Result applySuffix(List<Term> terms, MetaData metaData) {
            return new Accept(Arrays.<Term>asList());
        }
    }

    /**
     * Appends a term to the KList in a parse.
     * This is useful if you are putting labels down before parsing children.
     */
    public static class InsertRule extends SuffixRule {
        private final Term term;
        public InsertRule(Term term) { this.term = term; }
        protected boolean rejectSmallKLists() { return false; }
        protected int getSuffixLength() { return 0; }
        public Result applySuffix(List<Term> set, MetaData metaData) {
            return new Accept(Arrays.asList(term));
        }
    }

    /**
     * Annotates the last term from the KList with location information.
     */
    public static class AddLocationRule extends SuffixRule {
        protected boolean rejectSmallKLists() { return false; }
        protected int getSuffixLength() { return 1; }
        public Result applySuffix(List<Term> terms, MetaData metaData) {
            Term newTerm = terms.get(0).shallowCopy();
            newTerm.setLocation("("+metaData.startLine+","+metaData.startColumn+","+metaData.endLine+","+metaData.endColumn+")");
            return new Accept(Arrays.asList(newTerm));
        }
    }

    /*  // for adding a non-constant to a label that was added before the fact
        class AdoptionRule extends ContextFreeRule {
            private boolean reject;
            public Set<KList> apply(Set<KList> set) {
                Set<KList> result = new HashSet<>();
                for (KList klist : set) {
                    List<Term> contents = klist.getContents();
                    if (contents.size() >= 2) {
                        KList newKList = new KList(klist);
                        Term oldFinal = newKList.getContents().remove(contents);
                        Term oldPreFinal = newKList.getContents().remove(...);
                        if (oldPreFinal instanceof KApp) {
                            assert ((KApp) oldPreFinal).getChild() instanceof KList : "unimplemented"; // TODO
                            Term newFinal = new KApp(((KApp) oldPreFinal).getLabel(),
                                KList.append((KList) ((KApp) oldPreFinal).getChild(), oldFinal));
                            newKList.add(newFinal);
                            result.add(newKList);
                        } else if (!reject) { result.add(klist); }
                    } else if (!reject) { return.add(klist); }
                }
            }
        }
        */

    /**
     * TODO: implement this
     */
    public static abstract class ContextSensitiveRule extends Rule {
        abstract Set<KList> apply(KList context, Set<KList> set, MetaData metaData);
    }

    /*
    public static class CheckLabelContextRule extends ContextSensitiveRule {
        private boolean positive;
    }
    */
}
