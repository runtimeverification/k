// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Represents either an explicit attribute on a {@link Rule} or {@link Production},
 * or node metadata like location.
 * The inherited member attributes is used for location information
 * if this represents an explicitly written attribute.
 */
public class Attribute extends ASTNode {

    public static final String BUILTIN_KEY = "builtin";
    public static final String FUNCTION_KEY = "function";
    public static final String PREDICATE_KEY = "predicate";
    public static final String ANYWHERE_KEY = Constants.ANYWHERE;
    public static final String PATTERN_KEY = "pattern";
    public static final String HOOK_KEY = "hook";
    public static final String MACRO_KEY = "macro";
    public static final String LEMMA_KEY = "lemma";
    public static final String SIMPLIFICATION_KEY = "simplification";
    public static final String FRESH_GENERATOR = "freshGenerator";
    public static final String BITWIDTH_KEY = "bitwidth";
    public static final String SMTLIB_KEY = "smtlib";


    public static final Attribute BRACKET = new Attribute("bracket", "");
    public static final Attribute FUNCTION = new Attribute(FUNCTION_KEY, "");
    public static final Attribute PREDICATE = new Attribute(PREDICATE_KEY, "");
    public static final Attribute PATTERN = new Attribute(PATTERN_KEY, "");
    public static final Attribute MACRO = new Attribute(MACRO_KEY, "");
    public static final Attribute ANYWHERE = new Attribute("anywhere", "");
    public static final Attribute EQUALITY = new Attribute("equality", "");
    public static final Attribute TRANSITION = new Attribute("transition", "");
    public static final Attribute SYMBOLIC = new Attribute(SymbolicBackend.SYMBOLIC, "");
    public static final Attribute NOT_IN_RULES = new Attribute("notInRules", "");
    public static final Attribute VARIABLE = new Attribute("variable", "");
    public static final Attribute SUPERCOOL = new Attribute("supercool", "");
    public static final Attribute SUPERHEAT = new Attribute("superheat", "");
    public static final Attribute HYBRID = new Attribute("hybrid", "");
    public static final String CELL_KEY = "cell";

    private String key;
    private String value;

    public Attribute(String key, String value) {
        super();
        this.key = key;
        this.value = value;
    }

    public Attribute(Element elm) {
        super(elm);

        key = elm.getAttribute(Constants.KEY_key_ATTR);
        value = elm.getAttribute(Constants.VALUE_value_ATTR);
    }

    public Attribute(Attribute attribute) {
        super(attribute);
        key = attribute.key;
        value = attribute.value;
    }

    @Override
    public String toString() {
        return " " + this.getKey() + "(" + this.getValue() + ")";
    }

    public void setValue(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    public void setKey(String key) {
        this.key = key;
    }

    public String getKey() {
        return key;
    }

    @Override
    public Attribute shallowCopy() {
        return new Attribute(this);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((key == null) ? 0 : key.hashCode());
        result = prime * result + ((value == null) ? 0 : value.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Attribute other = (Attribute) obj;
        if (key == null) {
            if (other.key != null)
                return false;
        } else if (!key.equals(other.key))
            return false;
        if (value == null) {
            if (other.value != null)
                return false;
        } else if (!value.equals(other.value))
            return false;
        return true;
    }
}
