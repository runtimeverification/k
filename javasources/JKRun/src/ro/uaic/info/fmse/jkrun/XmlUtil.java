package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.fusesource.jansi.AnsiConsole;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class XmlUtil {

    private static XmlFormatter formatter = new XmlFormatter(2, 80);

    public static String formatXml(String s, boolean color) {
            return formatter.format(s, 0, color);
    }

    public static String formatXml(String s, int initialIndent, boolean color) {
            return formatter.format(s, initialIndent, color);
    }

    private static class XmlFormatter {
            private int indentNumChars;
            private int lineLength;
            private boolean singleLine;

            public XmlFormatter(int indentNumChars, int lineLength) {
                    this.indentNumChars = indentNumChars;
                    this.lineLength = lineLength;
            }

            public synchronized String format(String s, int initialIndent, boolean color) {
                    int indent = initialIndent;
                    StringBuilder sb = new StringBuilder();
     
                    AnsiConsole.systemInstall();
                    
                    for (int i = 0; i < s.length(); i++) {
                            char currentChar = s.charAt(i);
                            char nextChar_ = currentChar;
                            if (i != s.length() - 1) {
                                    nextChar_ = s.charAt(i + 1);
                            }
                            if (currentChar == '<') {
                                    if (color) {
                                            if (Character.isLetter(nextChar_) || nextChar_ == '/') {
                                                    sb.append(PrettyPrintOutput.ANSI_GREEN);
                                            }       
                                    }
                                    char nextChar = s.charAt(i + 1);
                                    if (nextChar == '/')
                                            indent -= indentNumChars;
                                    if (!singleLine) // Don't indent before closing element if we're creating opening and closing elements on a single line.
                                            sb.append(buildWhitespace(indent));
                                    if (nextChar != '?' && nextChar != '!' && nextChar != '/')
                                            indent += indentNumChars;
                                    singleLine = false; // Reset flag.
                            }
                            sb.append(currentChar);
                            if (currentChar == '>') {
                                    if (color) {
                                            sb.append(PrettyPrintOutput.ANSI_NORMAL);
                                    }
                                    if (s.charAt(i - 1) == '/') {
                                            indent -= indentNumChars;
                                            sb.append("\n");
                                    } else {
                                            boolean newline = false;
                                            String[] temp = new String[1];
                                            int nextStartElementPos = s.indexOf('<', i);
                                            if (nextStartElementPos > i + 1) {
                                                    String textBetweenElements = s.substring(i + 1, nextStartElementPos);
                                                    if (color) {
                                                            StringBuilder aux = new StringBuilder();
                                                            aux = colorSymbol(textBetweenElements, "|->", PrettyPrintOutput.ANSI_PURPLE);
                                                            textBetweenElements = new String(aux);
                                                            aux = colorSymbol(textBetweenElements, "~>", PrettyPrintOutput.ANSI_BLUE);
                                                            textBetweenElements = new String(aux);
                                                    }

                                                    if (textBetweenElements.contains("\n")) {
                                                            newline = true;
                                                            String delimiter = "\n";
                                                            temp = textBetweenElements.split(delimiter);
                                                    }
                                                    // If the space between elements is solely newlines, let them through to preserve additional newlines in source document.
                                                    if (textBetweenElements.replaceAll("\n", "").length() == 0) {
                                                            sb.append(textBetweenElements + "\n");
                                                    }
                                                    // Put tags and text on a single line if the text is short.
                                                    /* else if (textBetweenElements.length() <= lineLength * 0.5) { sb.append(textBetweenElements); singleLine = true; } */
                                                    // For larger amounts of text, wrap lines to a maximum line length.
                                                    else {
                                                            if (newline) {
                                                                    for (int k = 0; k < temp.length; k++) {
                                                                            sb.append("\n" + lineWrap(temp[k], lineLength, indent, null));
                                                                    }
                                                                    sb.append("\n");
                                                            } else {
                                                                    sb.append("\n" + lineWrap(textBetweenElements, lineLength, indent, null) + "\n");
                                                            }
                                                    }
                                                    i = nextStartElementPos - 1;
                                            } else {
                                                    sb.append("\n");
                                            }
                                    }
                            }
                    }
                    return sb.toString();
            }
    }
    
    public static StringBuilder colorSymbol(String text, String symbol, String color) {
            StringBuilder aux = new StringBuilder();
            String[] tokens;
            tokens = text.split("\\" + symbol);
            for (int i = 0; i < tokens.length - 1; i++) {
                    aux.append(tokens[i]);
                    aux.append(color);
                    aux.append(symbol);
                    aux.append(PrettyPrintOutput.ANSI_NORMAL);
            }
            aux.append(tokens[tokens.length - 1]);
            return aux;
    }

    public static String buildWhitespace(int numChars) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < numChars; i++)
                    sb.append(" ");
            return sb.toString();
    }

    /**
     * Wraps the supplied text to the specified line length.
     * 
     * @lineLength the maximum length of each line in the returned string (not including indent if specified).
     * @indent optional number of whitespace characters to prepend to each line before the text.
     * @linePrefix optional string to append to the indent (before the text).
     * @returns the supplied text wrapped so that no line exceeds the specified line length + indent, optionally with indent and prefix applied to each line.
     */
    private static String lineWrap(String s, int lineLength, Integer indent, String linePrefix) {
            if (s == null)
                    return null;

            StringBuilder sb = new StringBuilder();
            int lineStartPos = 0;
            int lineEndPos;
            boolean firstLine = true;
            
            while (lineStartPos < s.length()) {
                    if (!firstLine)
                            sb.append("\n");
                    else
                            firstLine = false;
                    if (lineStartPos + lineLength > s.length())
                            lineEndPos = s.length() - 1;
                    else {
                            lineEndPos = lineStartPos + lineLength - 1;
                            while (lineEndPos > lineStartPos && (s.charAt(lineEndPos) != ' ' && s.charAt(lineEndPos) != '\t'))
                                    lineEndPos--;
                    }
                    sb.append(buildWhitespace(indent));
                    if (linePrefix != null)
                            sb.append(linePrefix);

                    sb.append(s.substring(lineStartPos, lineEndPos + 1));
                    lineStartPos = lineEndPos + 1;
            }
            return sb.toString();
    }
    
    // Function to read DOM Tree from File
	public static Document readXML(File f) {

		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		Document doc = null;
		try {
			builder = dbf.newDocumentBuilder();
			InputSource input = new InputSource(new FileInputStream(f));
			doc = builder.parse(input);
		} catch (ParserConfigurationException e) {
			//e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (SAXException e) {
			//e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (FileNotFoundException e) {
			//e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (IOException e) {
			//e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		}
		return doc;
	}
    
    public static ArrayList<Element> getChildElements(Node node) {
            ArrayList l = new ArrayList();
            for (Node childNode = node.getFirstChild(); childNode != null;) {
                    if (childNode.getNodeType() == Node.ELEMENT_NODE) {
                            Element elem = (Element) childNode;
                            l.add(elem);
                    }
                    Node nextChild = childNode.getNextSibling();
                    childNode = nextChild;
            }

            return l;
    }
    
    public static Element getNextSiblingElement(Node node) {
            Node nextSibling = node.getNextSibling();
            while (nextSibling != null) {
                    if (nextSibling.getNodeType() == Node.ELEMENT_NODE) {
                            return (Element) nextSibling;
                    }
                    nextSibling = nextSibling.getNextSibling();
            }

            return null;
    }
    
    public static Element getPreviousSiblingElement(Node node) {
            Node previousSibling = node.getPreviousSibling();
            while (previousSibling != null) {
                    if (previousSibling.getNodeType() == Node.ELEMENT_NODE) {
                            return (Element) previousSibling;
                    }
                    previousSibling = previousSibling.getPreviousSibling();
            }

            return null;
    }

    public static String convertNodeToString(Node node) {
            try {
                    Transformer t = TransformerFactory.newInstance().newTransformer();
                    t.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
                    StringWriter sw = new StringWriter();
                    t.transform(new DOMSource(node), new StreamResult(sw));
                    return sw.toString();
            } catch (TransformerException e) {
                    //e.printStackTrace();
                    Error.report("Error while convert node to string:" + e.getMessage());
            }
            return null;
    }
    
    // write the XML document to disk
    public static void serializeXML(Document doc, String fileName) {
            try {
                    Source xmlSource = new DOMSource(doc);
                    Result result = new StreamResult(new FileOutputStream(fileName));
                    TransformerFactory transformerFactory = TransformerFactory.newInstance();
                    Transformer transformer = transformerFactory.newTransformer();
                    //transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
                    transformer.setOutputProperty(OutputKeys.INDENT, "yes");
                    transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "1");
                    transformer.transform(xmlSource, result);
            }
            catch (TransformerFactoryConfigurationError factoryError) {
                    //factoryError.printStackTrace();
                    Error.report("Error creating TransformerFactory:" + factoryError.getMessage());
            } catch (TransformerException transformerError) {
                    //transformerError.printStackTrace();
                    Error.report("Error transforming document:" + transformerError.getMessage());
            } catch (IOException ioException) {
                    //ioException.printStackTrace();
                    Error.report("Error while serialize XML:" + ioException.getMessage());
            }
    }


}