// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;

/**
 * Class for representing a K cell term.  The textual representation of a K cell is the following:
 * <table>
 * <tr><td>Cell </td>
 * <td>::= "<" Label CellAttribute* ">"  CellContents  "<" Label ">"</td></tr>
 * <tr><td>Label</td><td>::= Id</td></tr>
 * <tr><td>CellContents</td><td>::= Term</td></tr>
 * <tr><td>CellAttribute</td><td> = "ellipses" "=" ( '"left"' | '"right"' | '"both"' | '"none"')</td></tr>
 * <tr><td/><td> | "multiplicity" "=" ('"1"' | '"*"' | '"+"' | '"?"') </td></tr>
 * <tr><td/><td> | "color" "=" String </td></tr>
 * <tr><td/><td> | "stream" "=" ('"stdin"' | '"stdout"') </td></tr>
 * </table>
 * <p>
 *  For example, a configuration cell might look like
 *   {@code <output color="blue" multiplicity="?" stream="stdout"> </output>},
 *  while a rule cell might look like
 *     {@code <k ellipses="right"> X </k>}
 *  corresponding to  {@code <k> X ...</k>}
 * <p>
 * Cell attributes are in {@link #cellAttributes}, not {@link #attributes}.
 */
public class Cell extends Term implements Interfaces.MutableParent<Term, Enum<?>> {
    /** Possible values for the multiplicity attribute */
    public enum Multiplicity {
        ONE, MAYBE, ANY, SOME,
    }

    /** Possible values for the ellipses attribute */
    public enum Ellipses {
        LEFT, RIGHT, BOTH, NONE,
    }

    public static String SORT_ATTRIBUTE = "sort";

    /** Must equal with {@link #endLabel} */
    String label;
    /** Must equal with {@link #label} */
    String endLabel;

    /**
     * label and endLabel should be equal;  however, this is not checked during parsing, but later during compilation.
     * @return the end label
     *
     * @see org.kframework.parser.concrete.disambiguate.CellEndLabelFilter
     */
    public String getEndLabel() {
        return endLabel;
    }

    public void setEndLabel(String endLabel) {
        this.endLabel = endLabel;
    }

    Term contents;
    Map<String, String> cellAttributes;

    public Cell(Location location, Source source) {
        super(location, source, Sort.BAG_ITEM);
        cellAttributes = new HashMap<String, String>();
    }

    public Cell(Element element) {
        super(element);
        this.sort = Sort.BAG_ITEM;
        this.label = element.getAttribute(Constants.LABEL_label_ATTR);
        this.endLabel = element.getAttribute(Constants.ENDLABEL_label_ATTR);
        this.contents = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));

        NamedNodeMap its = element.getAttributes();
        cellAttributes = new HashMap<String, String>();
        setEllipses(element.getAttribute(Constants.ELLIPSES_ellipses_ATTR));

        for (int i = 0; i < its.getLength(); i++) {
            if (!its.item(i).getNodeName().equals(Constants.FILENAME_filename_ATTR)
                    && !its.item(i).getNodeName().equals(Constants.LOC_loc_ATTR) // &&
                                                                                    // !its.item(i).getNodeName().equals(Constants.ELLIPSES_ellipses_ATTR)
                    && !its.item(i).getNodeName().equals(Constants.SORT_sort_ATTR) && !its.item(i).getNodeName().equals(Constants.LABEL_label_ATTR)
                    && !its.item(i).getNodeName().equals(Constants.ENDLABEL_label_ATTR)) {
                cellAttributes.put(its.item(i).getNodeName(), StringUtil.unquoteKString("\"" + its.item(i).getNodeValue() + "\""));
            }
        }
    }

    public Cell(Cell node) {
        super(node);
        this.label = node.label;
        this.endLabel = node.endLabel;
        this.cellAttributes = node.cellAttributes;
        this.contents = node.contents;
    }

    public Cell(String label, Term contents) {
        super(Sort.BAG_ITEM);
        this.label = label;
        this.endLabel = label;
        this.cellAttributes = new HashMap<String, String>();
        this.contents = contents;
    }

    public Cell() {
        super(Sort.BAG_ITEM);
        cellAttributes = new HashMap<String, String>();
    }

    public boolean hasRightEllipsis() {
        Ellipses e = getEllipses();
        return (e == Ellipses.RIGHT || e == Ellipses.BOTH);
    }

    public boolean hasLeftEllipsis() {
        Ellipses e = getEllipses();
        return (e == Ellipses.LEFT || e == Ellipses.BOTH);
    }

    @Override
    public String toString() {
        String attributes = "";
        for (Entry<String, String> entry : this.cellAttributes.entrySet())
            attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";

        String content = "<" + this.label + attributes + ">";

        if (hasLeftEllipsis())
            content += "...";
        content += " " + this.contents + " ";
        if (hasRightEllipsis())
            content += "...";

        return content + "</" + this.label + "> ";
    }

    public String getLabel() {
        return label;
    }

    public Term getContents() {
        return contents;
    }

    public void setContents(Term contents) {
        this.contents = contents;
    }

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public Multiplicity getMultiplicity() {
        if (cellAttributes.containsKey("multiplicity")) {
            String attr = cellAttributes.get("multiplicity");
            if ("?".equals(attr))
                return Multiplicity.MAYBE;
            if ("*".equals(attr))
                return Multiplicity.ANY;
            if ("+".equals(attr))
                return Multiplicity.SOME;
            if ("1".equals(attr))
                return Multiplicity.ONE;
            GlobalSettings.kem.registerCompilerWarning("Unknown multiplicity in configuration for cell " + this.getLabel() + ".",
                    this);
        }
        return Multiplicity.ONE;
    }

    public Ellipses getEllipses() {
        String attr = cellAttributes.get("ellipses");
        try {
            if (attr != null) {
                return Ellipses.valueOf(attr.toUpperCase());
            }
        } catch (IllegalArgumentException e) {
            String msg = "Unknown ellipses value in configuration for cell " + this.getLabel() + ". Assuming none.";
            GlobalSettings.kem.registerCompilerWarning(msg, e, this);
        }
        return Ellipses.NONE;
    }

    public void setEllipses(String ellipses) {
        ellipses = ellipses.toLowerCase();
        if (ellipses.isEmpty() || ellipses.equals("none")) {
            cellAttributes.remove("ellipses");
        } else
            cellAttributes.put("ellipses", ellipses);
    }

    public Map<String, String> getCellAttributes() {
        return cellAttributes;
    }

    public void setCellAttributes(Map<String, String> cellAttributes) {
        this.cellAttributes = cellAttributes;
    }

    public boolean containsCellAttribute(String attribute) {
        return cellAttributes.containsKey(attribute);
    }

    public String getCellAttribute(String attribute) {
        return cellAttributes.get(attribute);
    }

    public void setLabel(String label) {
        this.label = label;
    }

    public void setDefaultAttributes() {
        cellAttributes = new HashMap<String, String>();
    }

    @Override
    public Cell shallowCopy() {
        return new Cell(this);
    }

    public String getId() {
        String id = cellAttributes.get("id");
        if (null == id)
            id = this.label;
        return id;
    }

    public void setEllipses(Ellipses e) {
        setEllipses(e.toString());
    }

    public void setId(String id) {
        if (getId().equals(id))
            return;
        cellAttributes.put("id", id);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Cell))
            return false;
        Cell c = (Cell) o;
        return label.equals(c.label) && contents.equals(c.contents);
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket) o).getContent());
        if (o instanceof Cast)
            return contains(((Cast) o).getContent());
        if (!(o instanceof Cell))
            return false;
        Cell c = (Cell) o;
        return label.equals(c.label) && contents.contains(c.contents);
    }

    @Override
    public int hashCode() {
        return label.hashCode() * 17 + contents.hashCode();
    }

    public List<Term> getCellTerms() {
        Term contents = getContents();
        List<Term> cells = new ArrayList<Term>();
        if (contents instanceof Variable || contents instanceof Cell) {
            cells.add(contents);
        } else if (contents instanceof Bag) {
            cells.addAll(((Bag) contents).getContents());
        }
        return cells;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Term getChild(Enum<?> type) {
        return contents;
    }

    @Override
    public void setChild(Term child, Enum<?> type) {
        this.contents = child;
    }
}
