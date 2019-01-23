// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import org.kframework.attributes.Att;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.io.Serializable;

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
        private final org.kframework.kore.Sort cellCollectionSort;
        public final Sort assocListSort;
        public final KLabelConstant assocListOperator;
        public final KLabelConstant assocListUnit;
        private final Att att;

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
            return sb.toString();
        }

        public Att att() {
            return att;
        }

        public enum ConstructorType {
            KITEM, BUILTIN_LIST, BUILTIN_MAP, BUILTIN_SET,
            KLIST, KSEQUENCE, KITEM_PROJECTION, KLABEL_INJECTION, INJECTED_KLABEL
        }

        public Constructor(ConstructorType type) {
            this(type, 0);
        }

        public Constructor(ConstructorType type, int size, Sort assocListSort, KLabelConstant assocListOperator, KLabelConstant assocListUnit) {
            this(type, size, 0, 0, null, null, assocListSort, assocListOperator, assocListUnit, Att.empty());
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
                           int size2, int size3, Kind kind,
                           org.kframework.kore.Sort cellCollectionSort) {
            this(type, size1, size2, size3, kind, cellCollectionSort, null, null, null, Att.empty());
        }

        public Constructor(ConstructorType type, Att att) {
            this(type, 0, 0, 0, null, null, null, null, null, att);
        }

        public Constructor(ConstructorType type, int size1,
                           int size2, int size3, Kind kind, org.kframework.kore.Sort cellCollectionSort,
                           Sort assocListSort, KLabelConstant assocListOperator, KLabelConstant assocListUnit,
                           Att att) {
            this.type = type;
            this.size1 = size1;
            this.size2 = size2;
            this.size3 = size3;
            this.kind = kind;
            this.cellCollectionSort = cellCollectionSort;
            this.assocListSort = assocListSort;
            this.assocListOperator = assocListOperator;
            this.assocListUnit = assocListUnit;
            this.att = att;
        }

        public Constructor(ConstructorType type, Kind kind) {
            this(type, 0, 0, 0, kind, null);
        }

        public Constructor(ConstructorType type, int size1,
                           org.kframework.kore.Sort cellCollectionSort) {
            this(type, size1, 0, 0, null, cellCollectionSort);
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

        public org.kframework.kore.Sort cellCollectionSort() {
            return cellCollectionSort;
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
