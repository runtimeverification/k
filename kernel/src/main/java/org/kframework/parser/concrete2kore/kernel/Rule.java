// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.kernel;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Production;
import org.kframework.parser.Constant;
import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * An action that transforms an AST into another AST
 */
public abstract class Rule implements Serializable {
    /**
     * Metadata used to inform a rule about the current parse.
     */
    static class MetaData {
        public static class Location {
            public final int position;
            public final int line;
            public final int column;

            public Location(int position, int line, int column) {
                this.position = position;
                this.line = line;
                this.column = column;
            }
        }
        public final Source source;
        public final Location start;
        public final Location end;
        public final CharSequence input;
        public MetaData(Source source, Location start, Location end, CharSequence input) {
            assert start != null && end != null && source != null;
            this.source = source;
            this.start = start;
            this.end = end;
            this.input = input;
        }
    }

    public abstract Set<Term> apply(Set<Term> set, MetaData metaData);

    /**
     * Helper class for rules that treat each KList passed to apply() independently from each other
     */
    public static abstract class KListRule extends Rule {
        public Set<Term> apply(Set<Term> set, MetaData metaData) {
            Set<Term> result = new HashSet<>();
            for (Term klist : set) {
                Term newKList = this.apply((KList)klist, metaData);
                if (newKList != null) {
                    result.add(newKList);
                }
            }
            return result;
        }
        protected abstract Term apply(KList set, MetaData metaData);
    }

    /**
     * Wraps the current KList with the given KLabel
     */
    public static class WrapLabelRule extends KListRule {
        public final Production label;
        private final boolean isToken, needsLabel;
        public WrapLabelRule(Production label) {
            assert label != null;
            this.label = label;
            this.isToken = label.att().contains("token");
            this.needsLabel = label.klabel().isDefined() || !label.isSyntacticSubsort();
        }
        protected Term apply(KList klist, MetaData metaData) {
            Term term;
            Location loc = new Location(metaData.start.line, metaData.start.column, metaData.end.line, metaData.end.column);
            Source source = metaData.source;
            if (isToken) {
                String value = metaData.input.subSequence(metaData.start.position, metaData.end.position).toString();
                term = Constant.apply(value, label, Optional.of(loc), Optional.of(source));
            } else if (needsLabel) {
                term = TermCons.apply(klist.items(), label, loc, source);
            } else {
                return klist;
            }
            return term;
        }
    }

    /**
     * Delete the last few elements added to the KList.
     * Usually used to remove whitespace and tokens
     */
    public static class DeleteRule extends KListRule {
        private final int length;
        public DeleteRule(int length) {
            this.length = length;
        }


        @Override
        protected KList apply(KList set, MetaData metaData) {
            return set.remove(length);
        }
    }
}
