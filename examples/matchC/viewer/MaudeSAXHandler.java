import java.io.FileReader;

import org.xml.sax.XMLReader;
import org.xml.sax.helpers.XMLReaderFactory;
import org.xml.sax.InputSource;
import org.xml.sax.helpers.DefaultHandler;
import org.xml.sax.Attributes;

import java.util.Stack;
import java.util.Collection;
import java.util.ArrayList;


public class MaudeSAXHandler extends DefaultHandler
{

  final Stack<Collection<MaudeTerm>> stack = new Stack<Collection<MaudeTerm>>();
  Boolean isResult = false;


  public MaudeSAXHandler()
  {
    super();
  }


  /*
   * Event handlers
   */
  public void startDocument()
  {
    stack.clear();
    isResult = false;
  }

  public void endDocument()
  {
  }

  public void startElement(String uri, String name, String qName,
                           Attributes atts)
  {
    if (isResult && "term".equals(qName))
    {
      int index = 0;
      MaudeTerm term = null;
      String op = null;
      String number = null;
      String sort = null;

      if ("op".equals(atts.getQName(index)))
        op = atts.getValue(index++);

      if ("number".equals(atts.getQName(index)))
        number = atts.getValue(index++);

      if ("sort".equals(atts.getQName(index)))
        sort = atts.getValue(index++);

      if (index == 2)
        term = new DefaultTerm(op, sort);
      else
        term = new NestedTerm(op, number, sort);

      stack.peek().add(term);
      stack.push(term.subterms());
    }
    else if ("result".equals(qName))
    {
      stack.push(new ArrayList<MaudeTerm>());
      isResult = true;
    }
  }


  public void endElement(String uri, String name, String qName)
  {
    if (isResult && "term".equals(qName))
      stack.pop();
    else if ("result".equals(qName))
      isResult = false;
  }


  public static KTreeNode getKTree(String filename)
  {
    MaudeTerm result;

    try
    {
      XMLReader reader = XMLReaderFactory.createXMLReader();
      MaudeSAXHandler handler = new MaudeSAXHandler();
      reader.setContentHandler(handler);
      reader.setErrorHandler(handler);
      reader.parse(new InputSource(new FileReader(filename)));
      result = handler.stack.peek().iterator().next();
    }
    catch (Exception e)
    {
      e.printStackTrace();
      return null;
    }

    KTreeNode root = KTreeNode.formatCell2(null, DefaultTerm.format(result));

    return root;
  }

}

