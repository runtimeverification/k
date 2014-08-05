// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * class for AST Attributes.
 * This is used to represent a collection of attributes on a node,
 * which may contain both attributes in the K source
 * written by a user, and metadata like location added by kompile.
 * Only {@link Rule} and {@link Production} may have user-written
 * attributes.
 *
 * @see ASTNode
 */
public class Attributes extends ASTNode implements Interfaces.MutableList<Attribute, Enum<?>>, Map<String, Attribute> {

    protected LinkedHashMap<String, Attribute> contents;

    public Attributes(Attributes c) {
        super(c);
        this.contents = c.contents;
    }

    public Attributes(Location location, Source source) {
        super(location, source);
        contents = new LinkedHashMap<String, Attribute>();
    }

    public Attributes(Element element) {
        super(element);

        contents = new LinkedHashMap<String, Attribute>();
        List<Element> children = XML.getChildrenElements(element);
        for (Element e : children)
            add((Attribute) JavaClassesFactory.getTerm(e));
    }

    public Attributes() {
        contents = new LinkedHashMap<String, Attribute>();
    }

    @Override
    public String toString() {
        if (isEmpty())
            return "";
        String content = "[";
        for (Attribute t : contents.values())
            content += t + ", ";
        return content.substring(0, content.length() - 2) + "]";
    }

    @Override
    public Attributes shallowCopy() {
        Attributes result = new Attributes();
        result.contents.putAll(contents);
        return result;
    }


    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((contents == null) ? 0 : contents.hashCode());
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
        Attributes other = (Attributes) obj;
        if (contents == null) {
            if (other.contents != null)
                return false;
        } else if (!contents.equals(other.contents))
            return false;
        return true;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public List<Attribute> getChildren(Enum<?> _) {
        return new ArrayList<Attribute>(contents.values());
    }

    @Override
    public void setChildren(List<Attribute> children, Enum<?> _) {
        contents.clear();
        for (Attribute attr : children) {
            add(attr);
        }
    }

    public void add(Attribute e) {
        contents.put(e.getKey(), e);
    }

    @Override
    public void clear() {
        contents.clear();
    }

    @Override
    public boolean containsKey(Object key) {
        return contents.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return contents.containsValue(value);
    }

    @Override
    public Set<java.util.Map.Entry<String, Attribute>> entrySet() {
        return contents.entrySet();
    }

    @Override
    public Attribute get(Object key) {
        return contents.get(key);
    }

    @Override
    public boolean isEmpty() {
        return contents.isEmpty();
    }

    @Override
    public Set<String> keySet() {
        return contents.keySet();
    }

    @Override
    public Attribute put(String key, Attribute value) {
        return contents.put(key, value);
    }

    @Override
    public void putAll(Map<? extends String, ? extends Attribute> m) {
        contents.putAll(m);
    }

    @Override
    public Attribute remove(Object key) {
        return contents.remove(key);
    }

    @Override
    public int size() {
        return contents.size();
    }

    @Override
    public Collection<Attribute> values() {
        return contents.values();
    }
}
