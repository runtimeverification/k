// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.*;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * AST representation a term of sort K explicitly constructed as an application of a KLabel to a KList.
 */
public class KApp extends Term implements Interfaces.MutableParent<Term, KApp.Children> {
    /**
     * A KLabel represented as a non-null instance of {@link KLabel}, {@link Variable} of sort KLabel, or {@link Ambiguity}.
     */
    private Term label;
    /**
     * A KList represented as a non-null instance of {@link KList}, {@link Variable} of sort KList, or {@link Ambiguity}.
     */
    private Term child;

    public static enum Children {
        LABEL, CHILD;
    }

    /**
     * Constructs the application of the given KLabel to a KList with the given elements.
     *
     * @param label the KLabel which is applied to a KList with the given elements. A non-null instance of {@link KLabel}, {@link Variable} of sort KLabel or {@link Ambiguity}.
     * @param elements the elements of the KList.
     * @return a {@link KApp} which represents the application of the given KLabel to a KList with the given elements.
     */
    public static KApp of(Term label, Term... elements) {
        return new KApp(label, new KList(Arrays.asList(elements)));
    }

    /**
     * Constructs the application of the given KLabel to a KList with the given elements.
     *
     * @param label the string of a KLabelConstant which is applied to a KList with the given elements.
     * @param elements the elements of the KList.
     * @return a {@link KApp} which represents the application of the given KLabel to a KList with the given elements.
     */
    public static KApp of(String label, Term... elements) {
        return KApp.of(KLabelConstant.of(label), elements);
    }

    public static KApp of(Term label, List<Term> elements) {
        return KApp.of(label, new KList(elements));
    }

    /**
     * Constructs a {@link KApp} object representing the application of the specified KLabel to the specified KList.
     *
     * @param location the line and column
     * @param filename the complete name of the file
     * @param label the KLabel which is applied to the given KList. A non-null instance of {@link KLabel}, {@link Variable} of sort KLabel or {@link Ambiguity}.
     * @param child the KList which the given KLabel is applied to. A non-null instance of {@link KList}, {@link Variable} of sort KList, or {@link Ambiguity}.
     */
    public KApp(Location location, Source source, Term label, Term child) {
        super(location, source, Sort.KITEM);
        setLabel(label);
        setChild(child);
    }

    /**
     * Constructs a {@link KApp} object representing the application of the specified KLabel to the specified KList.
     *
     * @param label the KLabel which is applied to the given KList. A non-null instance of {@link KLabel}, {@link Variable} of sort KLabel or {@link Ambiguity}.
     * @param child the KList which the given KLabel is applied to. A non-null instance of {@link KList}, {@link Variable} of sort KList, or {@link Ambiguity}.
     */
    public KApp(Term label, Term child) {
        super(label.getLocation(), label.getSource(), Sort.KITEM);
        setLabel(label);
        setChild(child);
    }

    /**
     * Constructs a {@link KApp} object from an XML {@link Element}.
     */
    public KApp(Element element, JavaClassesFactory factory) {
        super(element);
        List<Element> childrenElements = XML.getChildrenElements(element);
        Element body = XML.getChildrenElements(childrenElements.get(0)).get(0);
        setLabel((Term) factory.getTerm(body));
        Term term = (Term) factory.getTerm(childrenElements.get(1));
        if (!(term.getSort().equals(Sort.KLIST) || term instanceof Ambiguity)) {
            setChild(new KList(Collections.<Term> singletonList(term)));
        } else {
            setChild(term);
        }
    }

    private KApp(KApp node) {
        super(node);
        setLabel(node.label);
        setChild(node.child);
    }

    @Override
    public String toString() {
        return label + "(" + child + ")";
    }

    public Term getLabel() {
        return label;
    }

    /**
     * Sets the KLabel of this K application.
     *
     * @param label the KLabel represented as a non-null instance of {@link KLabel}, {@link Variable} of sort KLabel or {@link Ambiguity}.
     */
    public void setLabel(Term label) {
        assert label != null;
        // assertion disabled due to getSort relying on Context
        //        assert label.getSort(context).equals(Sort.KLABEL) || child instanceof Ambiguity:
        //                "unexpected sort " + label.getSort(context) + " of KApp first argument " + label + ";"
        //                        + " expected KLabel";
        //
        this.label = label;
    }

    public Term getChild() {
        return child;
    }

    /**
     * Sets the KLabel of this K application.
     *
     * @param child the KList represented as a non-null instance of {@link KList}, {@link Variable} of sort KList, or {@link Ambiguity}
     */
    public void setChild(Term child) {
        assert child != null;
        // assertion disabled due to getSort relying on Context
        //        assert child.getSort(context).equals(Sort.KLIST) || child instanceof Ambiguity:
        //                "unexpected sort " + child.getSort(context) + " of KApp second argument " + child + ";"
        //                        + "; expected KList";
        //
        this.child = child;
    }

    @Override
    public KApp shallowCopy() {
        return new KApp(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KApp kApp = (KApp) o;

        if (!child.equals(kApp.child)) return false;
        if (!label.equals(kApp.label)) return false;

        return true;
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket) o).getContent());
        if (o instanceof Cast)
            return contains(((Cast) o).getContent());
        if (!(o instanceof KApp))
            return false;
        KApp k = (KApp) o;
        return label.contains(k.label) && child.contains(k.child);
    }

    @Override
    public int hashCode() {
        return label.hashCode() * 23 + child.hashCode();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Term getChild(Children type) {
        switch (type) {
            case LABEL:
                return label;
            case CHILD:
                return child;
            default:
                throw new AssertionError("unreachable");
        }
    }

    @Override
    public void setChild(Term child, Children type) {
        switch (type) {
            case LABEL:
                this.label = child;
                break;
            case CHILD:
                this.child = child;
                break;
            default:
                throw new AssertionError("unreachable");
        }
    }
}
