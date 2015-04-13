// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Constants;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.w3c.dom.*;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

public class XmlLoader {

    public static Document getXMLDoc(String toParse) {

        try {
            // parse the xml returned by the parser.
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db = dbf.newDocumentBuilder();
            InputStream is = new ByteArrayInputStream(toParse.getBytes("UTF-8"));
            Document doc = db.parse(is);

            return doc;
        } catch (IOException | ParserConfigurationException | SAXException e) {
            e.printStackTrace();
        }

        return null;
    }

    public static void reportErrors(Document doc) throws ParseFailedException {
        // report any error that xml parser returns
        NodeList nl = doc.getElementsByTagName("error");

        if (nl.getLength() > 0) {
            Node nodeElem = nl.item(0);
            String attr = nodeElem.getAttributes().getNamedItem(Tag.value).getNodeValue();
            NodeList ch = nodeElem.getChildNodes();
            for (int i = 0; i < ch.getLength(); i++) {
                if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
                    Element node = (Element) ch.item(i);
                    if (node.getNodeName().equals(Tag.localized)) {
                        String msg = node.getAttribute("message");
                        Source source = ASTNode.getElementSource(node);
                        Location location = ASTNode.getElementLocation(node);
                        throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, attr + ": " + msg, source, location));
                    }
                }
            }
        }
    }

    public static void reportErrors(Document doc, String fromWhere) throws ParseFailedException {
        // report any error that xml parser returns
        NodeList nl = doc.getElementsByTagName("error");

        if (nl.getLength() > 0) {
            Node nodeElem = nl.item(0);
            String attr = nodeElem.getAttributes().getNamedItem(Tag.value).getNodeValue();
            NodeList ch = nodeElem.getChildNodes();
            for (int i = 0; i < ch.getLength(); i++) {
                if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
                    Element node = (Element) ch.item(i);
                    if (node.getNodeName().equals(Tag.localized)) {
                        String msg = node.getAttribute("message");
                        if (msg.equals("Unexpected end of file"))
                            msg = "Unexpected end of " + fromWhere;
                        Source source = ASTNode.getElementSource(node);
                        Location location = ASTNode.getElementLocation(node);
                        throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, attr + ": " + msg, source, location));
                    }
                }
            }
        }
    }

    public static Node updateLocation(Node node, int startLine, int startCol) {
        if (Node.ELEMENT_NODE == node.getNodeType()) {
            NamedNodeMap attr = node.getAttributes();
            Node item = attr.getNamedItem(Tag.location);
            if (item != null) {
                String location = item.getNodeValue();
                int loc0 = getLocNumber(location, 0);
                int loc1 = getLocNumber(location, 1);
                int loc2 = getLocNumber(location, 2);
                int loc3 = getLocNumber(location, 3);

                if (loc0 + loc1 + loc2 + loc3 == 0) {
                    loc0 = startLine;
                    loc1 = startCol;
                    loc2 = startLine;
                    loc3 = startCol;
                } else {
                    if (loc0 == 1)
                        loc1 += startCol - 1;
                    if (loc2 == 1)
                        loc3 += startCol - 1;
                    loc0 += startLine - 1;
                    loc2 += startLine - 1;
                }

                String newLoc = "(" + loc0 + "," + loc1 + "," + loc2 + "," + loc3 + ")";
                item.setNodeValue(newLoc);
            }
        }
        NodeList list = node.getChildNodes();
        for (int i = 0; i < list.getLength(); i++) {
            // Get child node
            Node childNode = list.item(i);

            // Visit child node
            updateLocation(childNode, startLine, startCol);
        }
        return node;
    }

    public static Node addSource(Node node, Source source) {
        if (source == null) {
            return node;
        }
        if (Node.ELEMENT_NODE == node.getNodeType()) {
            NamedNodeMap attr = node.getAttributes();
            Node item = attr.getNamedItem(Tag.location);
            if (item != null) {
                Element e = (Element) node;
                e.setUserData(Constants.SOURCE_ATTR, source, null);
            }
        }
        NodeList list = node.getChildNodes();
        for (int i = 0; i < list.getLength(); i++) {
            // Get child node
            Node childNode = list.item(i);

            // Visit child node
            addSource(childNode, source);
        }
        return node;
    }

    public static int getLocNumber(String loc, int place) {
        if (loc.equals("generated"))
            return -1;

        String[] str = loc.split("[\\(,\\)]");
        return Integer.parseInt(str[place + 1]);
    }
}
