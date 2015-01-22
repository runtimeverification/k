// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class SelectionGenerator {

    private final int size;
    private final int coSize;
    private List<Integer> selection;
    private Set<Integer> selected;
    private int index;

    public SelectionGenerator(int size, int coSize) {
        assert size <= coSize;

        this.size = size;
        this.coSize = coSize;
        selection = new ArrayList<>();
        selected = new HashSet<>();
        for (int i = 0; i < size; ++i) {
            selection.add(i);
            selected.add(i);
        }
    }

    public int getSelection(int index) {
        return selection.get(index);
    }

    public boolean isSelected(int element) {
        return selected.contains(element);
    }

    private void pop() {
        index = selection.remove(selection.size() - 1);
        selected.remove(index);
        ++index;
    }

    private void push() {
        selection.add(index);
        selected.add(index);
        index = 0;
    }

    public boolean generate() {
        if (selection.isEmpty()) return false;
        pop();
        while (selection.size() != size) {
            if (index == coSize) {
                if (selection.isEmpty()) {
                    break;
                } else {
                    pop();
                    continue;
                }
            }

            if (!selected.contains(index)) {
                push();
                continue;
            }

            ++index;
        }

        return !selection.isEmpty();
    }

}