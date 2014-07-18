// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign.xmlEditor;

import java.awt.Cursor;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionAdapter;
import java.awt.event.MouseMotionListener;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.Reader;
import java.io.Writer;
import java.util.Iterator;
import javax.swing.Action;
import javax.swing.JEditorPane;
import javax.swing.JTextPane;
import javax.swing.text.BadLocationException;
import javax.swing.text.BoxView;
import javax.swing.text.Document;
import javax.swing.text.Element;
import javax.swing.text.JTextComponent;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.Position;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.TextAction;
import javax.swing.text.View;
import javax.swing.text.ViewFactory;
import org.kframework.krun.gui.UIDesign.ConfigurationPanel;

public class XMLEditorKit extends StyledEditorKit {
  private static final long serialVersionUID = 1L;
  static JTextPane confText ;
  public XMLEditorKit (JTextPane confText){
    XMLEditorKit.confText = confText;
  }
  ViewFactory defaultFactory = new XMLViewFactory();

  public ViewFactory getViewFactory() {
    return defaultFactory;
  }

  public MutableAttributeSet getInputAttributes() {
    MutableAttributeSet mAttrs = super.getInputAttributes();
    return mAttrs;
  }

  public Document createDefaultDocument() {
    return new XMLDocument();
  }

  public String getContentType() {
    return "text/xml";
  }

  public void read(Reader in, Document doc, int pos) throws IOException, BadLocationException {
    BufferedReader br = new BufferedReader(in);
    String firstLine = br.readLine();
    String lastLine = "";
    StringBuffer buff = new StringBuffer();
    String nextLines = firstLine;
    while (nextLines != null) {
      buff.append(nextLines + "\n");
      lastLine = nextLines;
      nextLines = br.readLine();
    }
    if (!verifyRootElement(firstLine, lastLine)) {
      buff = addRootElement(buff);
    }
    int p = getInsertPosition(pos, doc);
    XMLReader.getInstance().read(new ByteArrayInputStream(buff.toString().getBytes()), doc, p);
  }

  public void write(OutputStream out, Document doc, int pos, int len) throws IOException,
          BadLocationException {
    int[] sel = new int[2];
    sel[0] = pos;
    sel[1] = pos + len;
    correctSelectionBounds(sel, doc);
    pos = sel[0];
    len = sel[1] - pos;
    super.write(out, doc, pos, len);
  }

  public void write(Writer out, Document doc, int pos, int len) throws IOException,
          BadLocationException {
    int[] sel = new int[2];
    sel[0] = pos;
    sel[1] = pos + len;
    correctSelectionBounds(sel, doc);
    pos = sel[0];
    len = sel[1] - pos;
    super.write(out, doc, pos, len);
  }

  public static void correctSelectionBounds(int[] selection, Document d) {
    if (d instanceof XMLDocument && d.getLength() > 0) {
      XMLDocument doc = (XMLDocument) d;
      int start = selection[0];
      Element root = doc.getDefaultRootElement();
      int i = root.getElementIndex(start);
      while (i >= 0 && root.getElement(i).getName().equals(XMLDocument.TAG_ELEMENT)) {
        root = root.getElement(i);
        i = root.getElementIndex(start);
      }

      Element startTag = root;

      int end = selection[0];
      root = doc.getDefaultRootElement();
      i = root.getElementIndex(end);
      while (i >= 0 && root.getElement(i).getName().equals(XMLDocument.TAG_ELEMENT)) {
        root = root.getElement(i);
        i = root.getElementIndex(end);
      }

      Element endTag = root;
      Element commonParent = startTag;
      while (commonParent != null &&
              !(commonParent.getStartOffset() <= endTag.getStartOffset() &&
              commonParent.getEndOffset() >= endTag.getEndOffset())) {
        commonParent = commonParent.getParentElement();
      }

      if (commonParent != null) {
        selection[0] = commonParent.getStartOffset();
        selection[1] = commonParent.getEndOffset();
      }
    }
  }

  protected int getInsertPosition(int pos, Document d) {
    if (d instanceof XMLDocument && d.getLength() > 0) {
      XMLDocument doc = (XMLDocument) d;
      Element root = doc.getDefaultRootElement();
      int i = root.getElementIndex(pos);
      while (i >= 0 && root.getElement(i).getName().equals(XMLDocument.TAG_ELEMENT)) {
        root = root.getElement(i);
        i = root.getElementIndex(pos);
      }

      while (root.getElementCount() < 3) {
        root = root.getParentElement();
      }
      return root.getElement(0).getEndOffset();
    }
    // collapseMemorizedTags((XMLDocument)d);
    return pos;
  }

  MouseListener lstCollapse = new MouseAdapter() {
    public void mouseClicked(MouseEvent e) {
      JEditorPane src = (JEditorPane) e.getSource();
      int pos = src.viewToModel(e.getPoint());
      View v = src.getUI().getRootView(src);
      while (v != null && !(v instanceof TagView)) {
        int i = v.getViewIndex(pos, Position.Bias.Forward);
        v = v.getView(i);
      }
      TagView deepest = (TagView) v;
      while (v != null && v instanceof TagView) {
        deepest = (TagView) v;
        int i = v.getViewIndex(pos, Position.Bias.Forward);
        v = v.getView(i);
      }

      if (deepest != null) {
        Shape a = getAllocation(deepest, src);
        if (a != null) {
          Rectangle r = a instanceof Rectangle ? (Rectangle) a : a.getBounds();
          r.y += TagView.AREA_SHIFT / 2;
          r.width = TagView.AREA_SHIFT;
          r.height = TagView.AREA_SHIFT;

          if (r.contains(e.getPoint())) {

            XMLDocument doc = (XMLDocument) src.getDocument();
            String[] elements = null;
            try {
              String element = doc.getText(deepest.getStartOffset(), deepest.getEndOffset()
                      - deepest.getStartOffset());
              elements = element.split("\n");
            } catch (BadLocationException e2) {
              e2.printStackTrace();
            }

            if (deepest.isExpanded()) {
              deepest.setExpanded(false);
              int tagNo = getTagPosition(doc, elements[0], pos);
              ConfigurationPanel.collapsedViews.put(elements[0] + "|" + tagNo,
                      deepest.getEndOffset() - deepest.getStartOffset());

            }
            else {
              int tagNo = getTagPosition(doc, elements[0], pos);
              ConfigurationPanel.collapsedViews.remove(elements[0] + "|" + tagNo);
              deepest.setExpanded(true);
            }

            try {
              doc.setUserChanges(false);
              pos++;
              doc.insertString(pos, "\n", new SimpleAttributeSet());
              doc.remove(pos, 1);
              doc.setUserChanges(true);
            } catch (BadLocationException e1) {
              e1.printStackTrace();
            }
          }
        }
      }
    }
  };

  Cursor oldCursor;

  MouseMotionListener lstMoveCollapse = new MouseMotionAdapter() {
    public void mouseMoved(MouseEvent e) {
      JEditorPane src = (JEditorPane) e.getSource();
      if (oldCursor == null) {
        oldCursor = src.getCursor();
      }

      int pos = src.viewToModel(e.getPoint());
      View v = src.getUI().getRootView(src);
      while (v != null && !(v instanceof TagView)) {
        int i = v.getViewIndex(pos, Position.Bias.Forward);
        v = v.getView(i);
      }
      TagView deepest = (TagView) v;
      while (v != null && v instanceof TagView) {
        deepest = (TagView) v;
        int i = v.getViewIndex(pos, Position.Bias.Forward);
        v = v.getView(i);
      }

      if (deepest != null) {
        Shape a = getAllocation(deepest, src);
        if (a != null) {
          Rectangle r = a instanceof Rectangle ? (Rectangle) a : a.getBounds();
          r.y += TagView.AREA_SHIFT / 2;
          r.width = TagView.AREA_SHIFT;
          r.height = TagView.AREA_SHIFT;

          if (r.contains(e.getPoint())) {
            src.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
            return;
          }
        }
      }

      src.setCursor(oldCursor);
    }
  };

  public void install(JEditorPane c) {
    super.install(c);
    c.setEditable(true);
    c.addMouseListener(lstCollapse);
    c.addMouseMotionListener(lstMoveCollapse);
  }

  public void deinstall(JEditorPane c) {
    c.removeMouseListener(lstCollapse);
    c.removeMouseMotionListener(lstMoveCollapse);
    super.deinstall(c);
  }

  protected static Shape getAllocation(View v, JEditorPane edit) {
    Insets ins = edit.getInsets();
    View vParent = v.getParent();
    int x = ins.left;
    int y = ins.top;

    while (vParent != null) {
      int i = vParent.getViewIndex(v.getStartOffset(), Position.Bias.Forward);
      Shape alloc = vParent.getChildAllocation(i, new Rectangle(0, 0, Short.MAX_VALUE,
              Short.MAX_VALUE));
      x += alloc.getBounds().x;
      y += alloc.getBounds().y;

      vParent = vParent.getParent();
    }
    if (v instanceof BoxView) {
      int ind = v.getParent().getViewIndex(v.getStartOffset(), Position.Bias.Forward);
      Rectangle r2 = v.getParent()
              .getChildAllocation(ind, new Rectangle(0, 0, Integer.MAX_VALUE, Integer.MAX_VALUE))
              .getBounds();
      return new Rectangle(x, y, r2.width, r2.height);
    }

    return new Rectangle(x, y, (int) v.getPreferredSpan(View.X_AXIS),
            (int) v.getPreferredSpan(View.Y_AXIS));
  }

  public Action[] getActions() {
    Action[] res = super.getActions();
    for (int i = 0; i < res.length; i++) {
      if (res[i] instanceof CopyAction) {
        res[i] = new XMLCopyAction();
      }
    }
    return res;
  }

  public class XMLCopyAction extends TextAction {

    private static final long serialVersionUID = 1L;

    /** Create this object with the appropriate identifier. */
    public XMLCopyAction() {
      super(copyAction);
    }

    /**
     * The operation to perform when this action is triggered.
     *
     * @param e
     *          the action event
     */
    public void actionPerformed(ActionEvent e) {
      JTextComponent target = getTextComponent(e);
      if (target != null) {
        // adapt selection
        int start = target.getSelectionStart();
        int end = target.getSelectionEnd();
        if (start != end) {
          int[] sel = new int[2];
          sel[0] = start;
          sel[1] = end;
          XMLEditorKit.correctSelectionBounds(sel, target.getDocument());
          target.setSelectionStart(sel[0]);
          target.setSelectionEnd(sel[1]);
        }
        target.copy();
      }
    }
  }

  public static void collapseMemorizedTags() {
    Iterator<?> iter = ConfigurationPanel.collapsedViews.keySet().iterator();
    XMLDocument docu = (XMLDocument)confText.getDocument();
    boolean existingTag = false;

    while (iter.hasNext()) {
      existingTag = false;
      String collapsedTag = (String) iter.next();
      String[] collapsedTagInfo = collapsedTag.split("[|]");
      String doc = "";
      try {
        doc = docu.getText(0, docu.getLength());
      } catch (BadLocationException e) {
        e.printStackTrace();
      }

      int pos = 0;
      int end = 0;
      if (collapsedTagInfo[1].equals("1")) {

        pos = doc.indexOf(collapsedTagInfo[0]);
        end = doc.indexOf(collapsedTagInfo[0].charAt(0) + "/" + collapsedTagInfo[0].substring(1));
        existingTag = true;
      }
      else {
        String[] lines = doc.split(collapsedTagInfo[0]);
        if (lines.length > Integer.parseInt(collapsedTagInfo[1])) {
          pos = doc.indexOf(lines[Integer.parseInt(collapsedTagInfo[1])])
                  - collapsedTagInfo[0].length();
          end = pos
                  + lines[Integer.parseInt(collapsedTagInfo[1])].indexOf(collapsedTagInfo[0]
                          .charAt(0) + "/" + collapsedTagInfo[0].substring(1));
          existingTag = true;
        }
      }

      if (existingTag) {
        View v = confText.getUI().getRootView(confText);
        while (v != null && !(v instanceof TagView)) {
          int i = v.getViewIndex(pos, Position.Bias.Forward);
          v = v.getView(i);
        }
        TagView deepest = (TagView) v;

        while (v != null && v instanceof TagView) {
          deepest = (TagView) v;
          int i = v.getViewIndex(pos, Position.Bias.Forward);
          v = v.getView(i);
        }

        if (deepest != null) {
          Rectangle r = new Rectangle();// a instanceof Rectangle ? (Rectangle)a
          // : a.getBounds();
          r.x = pos;
          r.y = end;
          r.y += TagView.AREA_SHIFT / 2;
          r.width = TagView.AREA_SHIFT;
          r.height = TagView.AREA_SHIFT;

          deepest.setExpanded(false);

          try {
            docu.setUserChanges(false);
            pos++;
            docu.insertString(pos, "\n", new SimpleAttributeSet());
            docu.remove(pos, 1);
            docu.setUserChanges(true);
          } catch (BadLocationException e1) {
            e1.printStackTrace();
          }
        }
      }
    }
  }

  public int getTagPosition(XMLDocument doc, String separator, int pos) {
    int min = Integer.MAX_VALUE;
    int positionMin = -1;
    String[] lines;
    try {
      lines = doc.getText(0, doc.getLength()).split(separator);
      if (lines.length > 2) {
        for (int i = 0; i < lines.length; i++) {
          if (doc.getText(0, doc.getLength()).indexOf(lines[i]) - pos > 0
                  && doc.getText(0, doc.getLength()).indexOf(lines[i]) - pos < min) {
            min = doc.getText(0, doc.getLength()).indexOf(lines[i]) - pos;
            positionMin = i;
          }
        }
        return positionMin;
      }
      return 1;
    } catch (BadLocationException e1) {
      e1.printStackTrace();
    }
    return -1;
  }

  public boolean verifyRootElement(String begin, String end) {
    String validEnd = begin.charAt(0) + "/" + begin.substring(1);
    return validEnd.equals(end);
  }

  public StringBuffer addRootElement(StringBuffer buff) {
    return buff.insert(0, "<configurations>").append("</configurations>");
  }
}