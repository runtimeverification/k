package org.kframework.krun.gui.helper;

import javax.swing.JTextArea;

public class HelpInfo extends JTextArea {

  private static final long serialVersionUID = 1L;

  public HelpInfo() {
    this.setEditable(false);
  }

  public void displayInfo(String info) {
    this.setText(info);
  }

}