// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.ktree;

import org.kframework.kore.AbstractKTransformer;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.unparser.ToKast;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeSelectionModel;
import java.awt.*;

/**
 * Display a K term as a tree
 */
class KTreePanel extends JPanel {
    private JTree tree;

    KTreePanel() {
        super(new GridLayout(1,0));

        tree = new JTree(new DefaultMutableTreeNode("No term loaded"));
        tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);

        add(tree);
        JScrollPane treeView = new JScrollPane(tree);
        treeView.setMinimumSize(new Dimension(100,100));
        treeView.setPreferredSize(new Dimension(500,300));

        add(treeView);
    }

    public void setTerm(K term) {
        DefaultMutableTreeNode top = new BuildNodes().apply(term);
        tree.setModel(new DefaultTreeModel(top));
    }

    private class BuildNodes extends AbstractKTransformer<DefaultMutableTreeNode> {

        @Override
        public DefaultMutableTreeNode apply(KApply k) {
            boolean childrenAllSmall = true;
            DefaultMutableTreeNode node = new DefaultMutableTreeNode(k.klabel().name());
            for (K child : k.asIterable()) {
                DefaultMutableTreeNode c = apply(child);
                if (childrenAllSmall) {
                    childrenAllSmall = c.isLeaf();
                }
                node.add(c);
            }
            if (childrenAllSmall) {
                String text = ToKast.apply(k);
                if (text.length() < 80) {
                    return new DefaultMutableTreeNode(text);
                }
            }
            return node;
        }

        @Override
        public DefaultMutableTreeNode apply(KRewrite k) {
            DefaultMutableTreeNode node = new DefaultMutableTreeNode("=>");
            DefaultMutableTreeNode l = apply(k.left());
            DefaultMutableTreeNode r = apply(k.right());
            if (l.isLeaf() && r.isLeaf()) {
                String text = ToKast.apply(k);
                if (text.length() < 80) {
                    node.setUserObject(text);
                    return node;
                }
            }
            node.add(l);
            node.add(r);
            return node;
        }

        @Override
        public DefaultMutableTreeNode apply(KToken k) {
            return new DefaultMutableTreeNode("#token{"+k.s()+"}");
        }

        @Override
        public DefaultMutableTreeNode apply(KVariable k) {
            return new DefaultMutableTreeNode(k.name());
        }

        @Override
        public DefaultMutableTreeNode apply(KSequence k) {
            boolean childrenAllSmall = true;
            DefaultMutableTreeNode node = new DefaultMutableTreeNode("~>");
            for (K child: k.asIterable()) {
                DefaultMutableTreeNode c = apply(child);
                if (childrenAllSmall) {
                    childrenAllSmall = c.isLeaf();
                }
                node.add(c);
            }
            if (childrenAllSmall) {
                String text = ToKast.apply(k);
                if (text.length() < 80) {
                    return new DefaultMutableTreeNode(text);
                }
            }
            return node;
        }

        public DefaultMutableTreeNode apply(KAs k) {
            DefaultMutableTreeNode pattern = apply(k.pattern());
            DefaultMutableTreeNode alias = apply(k.alias());
            if (pattern.isLeaf() && alias.isLeaf()) {
                String text = ToKast.apply(k);
                if (text.length() < 80) {
                    return new DefaultMutableTreeNode(text);
                }
            }
            DefaultMutableTreeNode node = new DefaultMutableTreeNode("#as");
            node.add(pattern);
            node.add(alias);
            return node;
        }

        @Override
        public DefaultMutableTreeNode apply(InjectedKLabel k) {
            return new DefaultMutableTreeNode(k.klabel().name());
        }
    }
}
