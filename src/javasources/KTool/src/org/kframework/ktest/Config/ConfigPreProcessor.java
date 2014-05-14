// Copyright (c) 2011-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Config;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.*;
import org.w3c.dom.events.Event;
import org.w3c.dom.events.EventListener;
import org.w3c.dom.events.EventTarget;
import org.xml.sax.Attributes;
import org.xml.sax.Locator;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.LocatorImpl;
import org.xml.sax.helpers.XMLFilterImpl;

import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * For location data annotation part, see
 * http://javacoalface.blogspot.com/2011/04/line-and-column-numbers-in-xml-dom.html
 */
// Please note that this class is not intended to do all kinds of different transformation at once,
// at first my plan was to have several processor passes and combine them on demand, but everything
// about XML parsing in Java is so complex , I couldn't do that. So instead in this pass I'm
// both annotating elements with location information and resolving environment variables in
// attributes/text nodes.
public class ConfigPreProcessor extends XMLFilterImpl {

    private Locator locator;
    private final Stack<Locator> locatorStack = new Stack<>();
    private final Stack<Element> elementStack = new Stack<>();
    private final UserDataHandler dataHandler = new LocationDataHandler();

    ConfigPreProcessor(XMLReader xmlReader, Document dom) {
        super(xmlReader);

        // Add listener to DOM, so we know which node was added.
        EventListener modListener = new EventListener() {
            @Override
            public void handleEvent(Event e) {
                EventTarget target = e.getTarget();
                elementStack.push((Element) target);
            }
        };
        ((EventTarget) dom).addEventListener("DOMNodeInserted", modListener, true);
    }

    @Override
    public void setDocumentLocator(Locator locator) {
        super.setDocumentLocator(locator);
        this.locator = locator;
    }

    @Override
    public void startElement(String uri, String localName,
            String qName, Attributes atts) throws SAXException {
        super.startElement(uri, localName, qName, atts);

        // Keep snapshot of start location,
        // for later when end of element is found.
        locatorStack.push(new LocatorImpl(locator));
    }

    @Override
    public void endElement(String uri, String localName, String qName)
            throws SAXException {

        // Mutation event fired by the adding of element end,
        // and so lastAddedElement will be set.
        super.endElement(uri, localName, qName);

        if (locatorStack.size() > 0) {
            Locator startLocator = locatorStack.pop();

            LocationData location = new LocationData(
                    startLocator.getSystemId(),
                    startLocator.getLineNumber(),
                    startLocator.getColumnNumber(),
                    locator.getLineNumber(),
                    locator.getColumnNumber());

            // annotate element with location data
            Element elem = elementStack.pop();
            elem.setUserData(LocationData.LOCATION_DATA_KEY, location, dataHandler);

            // resolve env variables in attributes of element
            NamedNodeMap nodes = elem.getAttributes();
            for (int i = 0; i < nodes.getLength(); i++) {
                Node node = nodes.item(i);
                node.setNodeValue(resolveEnvVars(node.getNodeValue()));
            }
        }
    }

    // Ensure location data copied to any new DOM node.
    private class LocationDataHandler implements UserDataHandler {

        @Override
        public void handle(short operation, String key, Object data,
                Node src, Node dst) {

            if (src != null && dst != null) {
                LocationData locatonData = (LocationData)
                        src.getUserData(LocationData.LOCATION_DATA_KEY);

                if (locatonData != null) {
                    dst.setUserData(LocationData.LOCATION_DATA_KEY,
                            locatonData, dataHandler);
                }
            }
        }
    }

    private String resolveEnvVars(String str) {
        Matcher m = Pattern.compile("\\$\\{(.*?)\\}").matcher(str);
        if (m.find()) {
            String var = m.group(1);
            String val = System.getenv(var);
            if (val != null) {
                return resolveEnvVars(m.replaceFirst(val));
            } else {
                String msg = "The variable is not defined in the system environment: " + var;
                GlobalSettings.kem.register(
                        new KException(
                                KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL,
                                msg, "command line", "System file."));
                return null; // unreachable code
            }
        } else {
            return str;
        }
    }
}