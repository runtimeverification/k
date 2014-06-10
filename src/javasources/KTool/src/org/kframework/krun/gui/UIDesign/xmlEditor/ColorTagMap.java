// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign.xmlEditor;

import java.awt.Color;
import java.util.HashMap;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;

/**
 * Holds the color for each cell
 * 
 */
public class ColorTagMap {

  private static HashMap<String, SimpleAttributeSet> colorMap = new HashMap<String, SimpleAttributeSet>();

  public static void addColorToTag(String tagName, Color c) {
    if (tagName == null || tagName.isEmpty() || c == null)
      return;
    SimpleAttributeSet sas = new SimpleAttributeSet();
    StyleConstants.setBold(sas, true);
    StyleConstants.setForeground(sas, c);
    colorMap.put(tagName, sas);
  }

  public static SimpleAttributeSet getColorForTag(String tag) {
    SimpleAttributeSet sas = colorMap.get(tag);
    if (sas == null)
      return new SimpleAttributeSet();
    return sas;
  }

  public static void clear() {
    colorMap.clear();
  }
}
