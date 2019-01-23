// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;

import java.io.File;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


/**
 * Represents a language definition.
 * Includes contents from all {@code required}-d files.
 * @see DefinitionLoader
 */
public class Definition extends ASTNode {

    private List<DefinitionItem> items;
    private File mainFile;
    private String mainModule;
    /** An index of all modules in {@link #items} by name */
    private String mainSyntaxModule;
    public Map<String, ASTNode> locations = new HashMap<>();

    public Definition() {
        super();
    }

    @Inject
    public Definition(Void v) {}

    public Definition(Definition d) {
        super(d);
        this.mainFile = d.mainFile;
        this.mainModule = d.mainModule;
        this.mainSyntaxModule = d.mainSyntaxModule;
        this.items = d.items;
        this.locations = d.locations;
    }

    @Override
    public String toString() {
        String content = "";
        List<DefinitionItem> sortedItems = new ArrayList<>(items);
        sortedItems.sort(new Comparator<DefinitionItem>() {
            @Override
            public int compare(DefinitionItem o1, DefinitionItem o2) {
                return o1.toString().compareTo(o2.toString());
            }
        });
        for (DefinitionItem di : sortedItems)
            content += di + " \n";

        return "DEF: " + mainFile + " -> " + mainModule + "\n" + content;
    }

    public void setItems(List<DefinitionItem> items) {
        this.items = items;
    }

    public List<DefinitionItem> getItems() {
        return items;
    }

    public void setMainModule(String mainModule) {
        this.mainModule = mainModule;
    }

    public String getMainModule() {
        return mainModule;
    }

    public void setMainSyntaxModule(String mainSyntaxModule) {
        this.mainSyntaxModule = mainSyntaxModule;
    }

    @Override
    public Definition shallowCopy() {
        return new Definition(this);
    }

}
