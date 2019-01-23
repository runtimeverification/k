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

    public Module(Module m) {
        super(m);
        this.name = m.name;
        this.items = m.items;
        this.sorts = m.sorts;
    }

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
    public String toString() {
        String content = "";
        List<ModuleItem> sortedItems = new ArrayList<ModuleItem>(items);

        sortedItems.sort(new Comparator<ModuleItem>() {
            @Override
            public int compare(ModuleItem o1, ModuleItem o2) {
                return o1.toString().compareTo(o2.toString());
            }
        });

        for (ModuleItem i : sortedItems)
            content += i + " \n";

        return "module " + name + "\n" + content + "\nendmodule";
    }


    @Override
    public Module shallowCopy() {
        return new Module(this);
    }

}
