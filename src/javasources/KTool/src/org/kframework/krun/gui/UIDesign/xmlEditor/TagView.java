// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign.xmlEditor;

import javax.swing.text.*;
import javax.swing.*;
import java.awt.*;
import java.awt.geom.Area;

public class TagView extends BoxView {
  private boolean isExpanded = true;
  public static final int AREA_SHIFT = 10;

  public TagView(Element elem) {
    super(elem, View.Y_AXIS);
    setInsets((short) 0, (short) (AREA_SHIFT + 2), (short) 0, (short) 0);
  }

  public float getAlignment(int axis) {
    return 0;
  }

  public void paint(Graphics g, Shape alloc) {
    Rectangle a = alloc instanceof Rectangle ? (Rectangle) alloc : alloc.getBounds();
    Shape oldClip = g.getClip();
    if (!isExpanded()) {
      Area newClip = new Area(oldClip);
      newClip.intersect(new Area(a));
      g.setClip(newClip);
    }
    super.paint(g, a);
    if (getViewCount() > 1) {
      g.setClip(oldClip);
      a.width--;
      a.height--;
      g.setColor(Color.lightGray);
      // collapse rect
      g.drawRect(a.x, a.y + AREA_SHIFT / 2, AREA_SHIFT, AREA_SHIFT);

      if (!isExpanded()) {
        g.drawLine(a.x + AREA_SHIFT / 2, a.y + AREA_SHIFT / 2 + 2, a.x + AREA_SHIFT / 2, a.y
                + AREA_SHIFT / 2 + AREA_SHIFT - 2);
      }
      else {
        g.drawLine(a.x + AREA_SHIFT / 2, a.y + 3 * AREA_SHIFT / 2, a.x + AREA_SHIFT / 2, a.y
                + a.height);
        g.drawLine(a.x + AREA_SHIFT / 2, a.y + a.height, a.x + AREA_SHIFT, a.y + a.height);
      }

      g.drawLine(a.x + 2, a.y + AREA_SHIFT, a.x + AREA_SHIFT - 2, a.y + AREA_SHIFT);
    }
  }

  public float getPreferredSpan(int axis) {
    if (isExpanded() || axis != View.Y_AXIS) {
      return super.getPreferredSpan(axis);
    }
    else {
      View firstChild = getView(0);
      return getTopInset() + firstChild.getPreferredSpan(View.Y_AXIS);
    }
  }

  public float getMinimumSpan(int axis) {
    if (isExpanded() || axis != View.Y_AXIS) {
      return super.getMinimumSpan(axis);
    }
    else {
      View firstChild = getView(0);
      return getTopInset() + firstChild.getMinimumSpan(View.Y_AXIS);
    }
  }

  public float getMaximumSpan(int axis) {
    return getPreferredSpan(axis);
  }

  public boolean isExpanded() {
    return isExpanded;
  }

  public void setExpanded(boolean expanded) {
    isExpanded = expanded;
  }

  protected int getNextEastWestVisualPositionFrom(int pos, Position.Bias b,
          Shape a,
          int direction,
          Position.Bias[] biasRet)
          throws BadLocationException {
    int newPos = super.getNextEastWestVisualPositionFrom(pos, b, a, direction, biasRet);
    if (!isExpanded()) {
      if (newPos >= getStartOffset() && newPos < getView(0).getView(0).getEndOffset()) {
        // first line of first child
        return newPos;
      }
      else if (newPos >= getView(0).getView(0).getEndOffset()) {
        if (direction == SwingConstants.EAST) {
          newPos = Math.min(getDocument().getLength() - 1, getEndOffset());
        }
        else {
          newPos = getView(0).getView(0).getEndOffset() - 1;
        }
      }
    }

    return newPos;
  }
}
