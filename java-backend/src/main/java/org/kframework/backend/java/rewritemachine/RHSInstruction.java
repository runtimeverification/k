// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.io.Serializable;
import java.util.List;

public final class RHSInstruction implements Serializable {

    public enum Type {
        PUSH, CONSTRUCT, SUBST, EVAL, PROJECT
    }

    public static final RHSInstruction EVAL = new RHSInstruction(Type.EVAL, null, null);
    public static final RHSInstruction PROJECT = new RHSInstruction(Type.PROJECT, null, null);

    private final Type type;
    private final Constructor constructor;
    private final Term term;

    public static class Constructor implements Serializable {
        private final ConstructorType type;
        private final int size1;
        private final int size2;
        private final int size3;
        private final Kind kind;
        private final List<CellLabel> cellLabels;
        private final Source source;
        private final Location location;

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append(type);
            if (size1 > 0) {
                sb.append(' ');
                sb.append(size1);
            }
            if (size2 > 0) {
                sb.append(' ');
                sb.append(size2);
            }
            if (size3 > 0) {
                sb.append(' ');
                sb.append(size3);
            }
            if (kind != null) {
                sb.append(' ');
                sb.append(kind);
            }
            if (cellLabels != null) {
                sb.append(' ');
                sb.append(cellLabels);
            }
            return sb.toString();
        }

        public enum ConstructorType {
            KITEM, BUILTIN_LIST, BUILTIN_MAP, BUILTIN_SET,
            KLABEL_FREEZER, KLIST, KSEQUENCE, KITEM_PROJECTION,
            KLABEL_INJECTION, CELL_COLLECTION, INJECTED_KLABEL
        }

        public Constructor(ConstructorType type) {
            this(type, 0);
        }

        public Constructor(ConstructorType type, int size1) {
            this(type, size1, 0);
        }

        public Constructor(ConstructorType type, int size1,
                int size2) {
            this(type, size1, size2, 0);
        }

        public Constructor(ConstructorType type, int size1,
                int size2, int size3) {
            this(type, size1, size2, size3, null, null);
        }

        public Constructor(ConstructorType type, int size1,
                int size2, int size3, Kind kind, List<CellLabel> cellLabels) {
            this(type, size1, size2, size3, kind, cellLabels, null, null);
        }

        public Constructor(ConstructorType type, Source source, Location location) {
            this(type, 0, 0, 0, null, null, source, location);
        }

        public Constructor(ConstructorType type, int size1,
                int size2, int size3, Kind kind, List<CellLabel> cellLabels,
                Source source, Location location) {
            this.type = type;
            this.size1 = size1;
            this.size2 = size2;
            this.size3 = size3;
            this.kind = kind;
            this.cellLabels = cellLabels;
            this.source = source;
            this.location = location;
        }

        public Constructor(ConstructorType type, Kind kind) {
            this(type, 0, 0, 0, kind, null);
        }

        public Constructor(ConstructorType type, int size1, List<CellLabel> cellLabels) {
            this(type, size1, 0, 0, null, cellLabels);
        }

        public Kind kind() {
            return kind;
        }

        public int size1() {
            return size1;
        }

        public int size2() {
            return size2;
        }

        public int size3() {
            return size3;
        }

        public ConstructorType type() {
            return type;
        }

        public List<CellLabel> cellLabels() {
            return cellLabels;
        }

        public Source getSource() {
            return source;
        }

        public Location getLocation() {
            return location;
        }
    }

    public static RHSInstruction CONSTRUCT(Constructor constructor) {
        return new RHSInstruction(Type.CONSTRUCT, null, constructor);
    }

    public static RHSInstruction PUSH(Term term) {
        return new RHSInstruction(Type.PUSH, term, null);
    }

    public static RHSInstruction SUBST(Variable var) {
        return new RHSInstruction(Type.SUBST, var, null);
    }
    private RHSInstruction(Type type, Term term, Constructor constructor) {
        this.type = type;
        this.term = term;
        this.constructor = constructor;
    }

    public Type type() {
        return type;
    }

    public Term term() {
        return term;
    }

    public Constructor constructor() {
        return constructor;
    }

    @Override
    public String toString() {
        switch (type) {
        case SUBST:
        case PUSH:
            return type.name() + " " + term;
        case CONSTRUCT:
            return "CONSTRUCT " + constructor;
        case EVAL:
        case PROJECT:
            return type.name();
        default:
            throw new AssertionError("unreachable");
        }
    }
}
