// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.helper;

import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.Enumeration;

public class HelpInfo extends JTextPane implements MouseListener {

    private static final long serialVersionUID = 1L;
    private TreeFromFile tree;
    public static String htmlPrefix = "<html> <h3>";
    public static String htmlMiddle = "</h3> <hr color=blue> <body>"
            + "<div id=\"holder\" > "
            + "<div style=\"height:370px;\"><p style=\"font-size:10px; padding: 20px 0px 20px 15px;\"> ";
    public static String htmlEnd = "</p></div><div id=\"footer\" style=\"background-color: #eeeeee;\n"
            + "    bottom: 0;\n"
            + "    height: 30px;\n"
            + "    left: 0;\n"
            + "    position: absolute;\n"
            + "    right: 0;"
            + " font-size:9px;text-align:center;\"><hr color=blue>"
            + " Graphical debugger manual </div></div></body></html>";

    public HelpInfo() {
        this.setEditable(false);
        this.addMouseListener(this);
        this.setContentType("text/html");
    }

    public void displayInfo(String info, TreeFromFile tree) {
        this.tree = tree;
        this.setText(info);
    }

    @Override
    public void mouseClicked(MouseEvent e) {

        try {
            String element = this.getDocument().getText(this.getCaretPosition(), 1);
            int i = 1;
            String currentLetter = this.getDocument().getText(this.getCaretPosition() + i, 1);
            while (currentLetter.hashCode() != 32 && currentLetter.hashCode() != 41) {
                element += this.getDocument().getText(this.getCaretPosition() + i, 1);
                i++;
                currentLetter = this.getDocument().getText(this.getCaretPosition() + i, 1);
            }

            int j = 1;
            currentLetter = this.getDocument().getText(this.getCaretPosition() - j, 1);
            while (this.getCaretPosition() - j >= 0 && currentLetter.hashCode() != 32) {
                element = this.getDocument().getText(this.getCaretPosition() - j, 1) + element;
                j++;
                currentLetter = this.getDocument().getText(this.getCaretPosition() - j, 1);

            }

            Enumeration enumeration = tree.top.breadthFirstEnumeration();
            while (enumeration.hasMoreElements()) {
                DefaultMutableTreeNode node = (DefaultMutableTreeNode) enumeration.nextElement();
                if (element.equals(node.getUserObject().toString())) {
                    tree.tree.setSelectionPath(new TreePath(node.getPath()));
                }
            }
        } catch (BadLocationException e1) {
            e1.printStackTrace();
        }
        // To change body of implemented methods use File | Settings | File
        // Templates.
    }

    @Override
    public void mousePressed(MouseEvent e) {
        // To change body of implemented methods use File | Settings | File
        // Templates.

    }

    @Override
    public void mouseReleased(MouseEvent e) {
        // To change body of implemented methods use File | Settings | File
        // Templates.
    }

    @Override
    public void mouseEntered(MouseEvent e) {
        // To change body of implemented methods use File | Settings | File
        // Templates.
    }

    @Override
    public void mouseExited(MouseEvent e) {
        // To change body of implemented methods use File | Settings | File
        // Templates.
    }
}