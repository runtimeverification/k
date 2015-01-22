// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 * Variables, used both in rules/contexts and for variables like {@code $PGM} in configurations.
 */
public class Variable extends Term {

    private static int nextVariableIndex = 0;

    private String name;
    /** True if the variable was written with an explicit type annotation */
    private boolean userTyped = false;
    private final boolean freshVariable;
    private final boolean freshConstant;
    private boolean syntactic = false;
    /** Used by the type inferencer  */
    private Sort expectedSort = null;
    public static final String GENERATED_ANON_VAR = "GeneratedAnonVar";

    public Sort getExpectedSort() {
        return expectedSort;
    }

    public void setExpectedSort(Sort expectedSort) {
        this.expectedSort = expectedSort;
    }

    public Variable(Element element, JavaClassesFactory factory) {
        super(element);
        this.sort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
        this.name = element.getAttribute(Constants.NAME_name_ATTR);
        this.userTyped = element.getAttribute(Constants.TYPE_userTyped_ATTR).equals("true");

        java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
        if (its.size() > 0) {
            getAttributes().putAll((Attributes) factory.getTerm(its.get(0)));
        }

        if (this.name.startsWith("?")) {
            this.freshVariable = true;
            this.freshConstant = false;
            this.name = this.name.substring(1);
        } else if (this.name.startsWith("!")) {
            this.freshConstant = true;
            this.freshVariable = false;
            this.name = this.name.substring(1);
        } else {
            this.freshVariable = false;
            this.freshConstant = false;
        }
    }

    public Variable(String name, Sort sort, boolean freshVariable, boolean freshConstant) {
        super(sort);
        this.name = name;
        this.freshVariable = freshVariable;
        this.freshConstant = freshConstant;
    }

    public Variable(String name, Sort sort) {
        this(name, sort, false, false);
    }

    public Variable(Variable variable) {
        super(variable);
        name = variable.name;
        freshVariable = variable.freshVariable;
        freshConstant = variable.freshConstant;
        userTyped = variable.userTyped;
        syntactic = variable.syntactic;
        expectedSort = variable.expectedSort;
    }

    public static Variable getAnonVar(Sort sort) {
        return new Variable(GENERATED_ANON_VAR + nextVariableIndex++, sort);
    }

    public static Variable getAnonVar(Sort sort, boolean freshVariable, boolean freshConstant) {
        return new Variable(GENERATED_ANON_VAR + nextVariableIndex++, sort, freshVariable, freshConstant);
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public String fullName() {
        if (isFreshVariable()) {
            return "?" + name;
        } else if (isFreshConstant()) {
            return "!" + name;
        } else {
            return name;
        }
    }

    public String toString() {
        return name + ":" + sort;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof Variable))
            return false;
        Variable var = (Variable) obj;

        return this.sort.equals(var.getSort()) && this.name.equals(var.getName())
                && this.freshVariable == var.freshVariable
                && this.freshConstant == var.freshConstant;
    }

    @Override
    public int hashCode() {
        return sort.hashCode() + name.hashCode();
    }

    public void setUserTyped(boolean userTyped) {
        this.userTyped = userTyped;
    }

    public boolean isUserTyped() {
        return userTyped;
    }

    @Override
    public Variable shallowCopy() {
        return new Variable(this);
    }

    public boolean isFreshVariable() {
        return freshVariable;
    }

    public boolean isFreshConstant() {
        return freshConstant;
    }

    public boolean isGenerated(){
        return name.startsWith(GENERATED_ANON_VAR);
    }

    public boolean isSyntactic() {
        return syntactic;
    }

    public void setSyntactic(boolean syntactic) {
        this.syntactic = syntactic;
    }

}
