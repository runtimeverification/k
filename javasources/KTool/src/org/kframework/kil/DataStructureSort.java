package org.kframework.kil;

import org.kframework.kil.loader.Context;

import com.google.common.collect.ImmutableSet;

import java.io.Serializable;
import java.util.Collection;


/**
 * A builtin data structure sort.
 *
 * @author AndreiS
 */
public class DataStructureSort implements Serializable {

    private final String name;
    private final String type;
    private final String constructorLabel;
    private final String elementLabel;
    private final String unitLabel;
    private final ImmutableSet<String> operatorLabels;

    public DataStructureSort(
            String name,
            String type,
            String constructorLabel,
            String elementLabel,
            String unitLabel,
            Collection<String> operatorLabels) {
        assert Context.DataStructureTypes.contains(type):
               "unknown builtin collection type " + type;

        this.name = name;
        this.type = type;
        this.constructorLabel = constructorLabel;
        this.elementLabel = elementLabel;
        this.unitLabel = unitLabel;
        this.operatorLabels = ImmutableSet.copyOf(operatorLabels);
    }

    public String constructorLabel() {
        return constructorLabel;
    }

    public String elementLabel() {
        return elementLabel;
    }

    public String name() {
        return name;
    }

    public String type() {
        return type;
    }

    public String unitLabel() {
        return unitLabel;
    }

}
