package org.kframework.backend.java.util;

import org.apache.commons.lang3.mutable.MutableInt;

/**
 * @author Denis Bogdanas
 * Created on 01-Apr-19.
 */
public class Counter {
    private String name;
    private MutableInt level;
    private int countTop;
    private int countRecursive;

    protected Counter(String name, MutableInt levelHolder) {
        this.name = name;
        this.level = levelHolder;
    }

    protected Counter(String name, MutableInt level, int countTop, int countRecursive) {
        this.name = name;
        this.level = level;
        this.countTop = countTop;
        this.countRecursive = countRecursive;
    }

    public void increment() {
        if (level.intValue() == 1) {
            countTop++;
        } else {
            countRecursive++;
        }
    }

    public String getName() {
        return name;
    }

    public int getCountTop() {
        return countTop;
    }

    public int getCountRecursive() {
        return countRecursive;
    }
}
