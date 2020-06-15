// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kore.Sort;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

/** A module. */
public class Module extends DefinitionItem {
    private String name;
    private List<ModuleItem> items = new ArrayList<>();

    // lazily computed set of sorts.
    private Set<Sort> sorts;

    public Module() {
        super();
    }

    public Module(String name) {
        super();
        this.name = name;
    }

    public void appendModuleItem(ModuleItem item) {
        this.items.add(item);
        this.sorts = null;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public void setItems(List<ModuleItem> items) {
        this.items = items;
        this.sorts = null;
    }

    public List<ModuleItem> getItems() {
        return items;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("module ").append(name).append(" ").append(getAttributes()).append("\n");
        for (ModuleItem i : items) {
            i.toString(sb);
            sb.append("\n");
        }
        sb.append("endmodule");
    }


}
