// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.utils.xml;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class XML {

    /**
     * Given an XML file as input it return the DOM Document
     * @param xmlFilePath
     * @return DOM Document of the file
     */
    public static Document getDocument(String xmlContent)
    {
        try {
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db;
            db = dbf.newDocumentBuilder();
            Document doc = db.parse(new ByteArrayInputStream(xmlContent.getBytes()));
            return doc;
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
        } catch (SAXException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return null;
    }

    // probably, in the future I'll use some callback functions
    public static List<Element> getChildrenElements(Element element)
    {
        NodeList children = element.getChildNodes();
        List<Element> elements = new LinkedList<Element>();

        for(int i = 0; i < children.getLength(); i++)
        {
            if (children.item(i).getNodeType() == Node.ELEMENT_NODE)
            {
                Element child = (Element) children.item(i);
                elements.add(child);
            }
        }

        return elements;
    }


    public static List<Element> getChildrenElementsByTagName(Element element, List<String> tagNames)
    {
        List<Element> elements = getChildrenElements(element);
        List<Element> filteredElements = new LinkedList<Element>();
        for (Element e : elements)
            if (tagNames.contains(e.getNodeName()))
                filteredElements.add(e);

        return filteredElements;
    }

    public static List<Element> getChildrenElementsByTagName(Element element, String tag)
    {
        List<String> strings = new LinkedList<String>();
        strings.add(tag);

        return getChildrenElementsByTagName(element, strings);
    }
}
