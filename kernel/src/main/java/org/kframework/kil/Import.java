// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

/** An import directive */
public class Import extends ModuleItem {

    String name;

    public static final String IMPORTS_SYNTAX_SUFFIX = "$SYNTAX";

    public Import(String importName) {
        super();
        name = importName;
    }

    public Import(Import import1) {
        super(import1);
        this.name = import1.name;
    }

    public Import(String importName, Location loc, Source source) {
        super(loc, source);
        this.name = importName;
    }

    public Import(String importName, boolean isImportSyntax) {
        this(isImportSyntax ? importName + IMPORTS_SYNTAX_SUFFIX : importName);
    }

    @Override
    public String toString() {
        return "  imports " + name;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public Import shallowCopy() {
        return new Import(this);
    }

    public boolean isImportSyntax() {
        return name.endsWith(IMPORTS_SYNTAX_SUFFIX);
    }

    public Import getImportSyntax() {
        if (isImportSyntax()) {
            return this;
        }
        return new Import(name + IMPORTS_SYNTAX_SUFFIX, getLocation(), getSource());
    }

    public String getMainModuleName() {
        assert isImportSyntax();
        return name.substring(0, name.length() - IMPORTS_SYNTAX_SUFFIX.length());
    }
}
