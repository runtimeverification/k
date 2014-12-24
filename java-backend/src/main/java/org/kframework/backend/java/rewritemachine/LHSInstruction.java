// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.Map;

import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.util.Utils;

import com.google.common.collect.Maps;

/**
 * Represents instructions of the {@link KAbstractRewriteMachine}.
 *
 * @author YilongL
 *
 */
public final class LHSInstruction implements Serializable {

    public enum Type {
        UP, CHOICE, GOTO
    }

    public static final LHSInstruction UP = new LHSInstruction(Type.UP, null);
    public static final LHSInstruction CHOICE = new LHSInstruction(Type.CHOICE, null);

    private static final Map<CellLabel, LHSInstruction> cachedGOTOInstructions = Maps.newHashMapWithExpectedSize(100);

    private final Type type;
    private final CellLabel cellLabel;
    private final int hashCode;

    public static LHSInstruction GOTO(CellLabel cellLabel) {
        LHSInstruction instr = cachedGOTOInstructions.get(cellLabel);
        if (instr == null) {
            instr = new LHSInstruction(Type.GOTO, cellLabel);
            cachedGOTOInstructions.put(cellLabel, instr);
        }
        return instr;
    }

    private LHSInstruction(Type type, CellLabel cellLabel) {
        this.type = type;
        this.cellLabel = cellLabel;
        this.hashCode = type == Type.GOTO ?
                type.hashCode() * Utils.HASH_PRIME + cellLabel.hashCode() :
                type.hashCode();
    }

    public Type type() {
        return type;
    }

    public CellLabel cellLabel() {
        return cellLabel;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    public String toString() {
        return cellLabel == null ? type.toString() : type.toString() + "(" + cellLabel + ")";
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if
     * there is a cached instance.
     */
    Object readResolve() throws ObjectStreamException {
        switch (type) {
        case UP:
            return UP;
        case CHOICE:
            return CHOICE;
        case GOTO:
            LHSInstruction instr = cachedGOTOInstructions.get(cellLabel);
            if (instr == null) {
                instr = new LHSInstruction(type, cellLabel);
                cachedGOTOInstructions.put(cellLabel, instr);
            }
            return instr;
        default:
            assert false;
            return null;
        }
    }

}
