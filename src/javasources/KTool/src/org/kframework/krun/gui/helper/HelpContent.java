// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.helper;

import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;

public class HelpContent extends JPanel {

    private static final long serialVersionUID = 1L;
    HelpInfo observer;
    TreeFromFile tree = new TreeFromFile();

    public HelpContent(HelpInfo obs) {
        setLayout(new BorderLayout());
        observer = obs;
        // tree = new TreeFromFile();
        tree.tree.addTreeSelectionListener(new TreeSelectionListener() {
            public void valueChanged(TreeSelectionEvent e) {
                DefaultMutableTreeNode node = (DefaultMutableTreeNode) e.getPath()
                        .getLastPathComponent();
                notifyObservers(((TreeNode) node.getUserObject()).getContent());
            }
        });
        this.add(tree.tree);
    }

    private void notifyObservers(String node) {

        observer.displayInfo(node, tree);
    }

}