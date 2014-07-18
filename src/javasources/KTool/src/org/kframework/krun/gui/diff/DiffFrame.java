// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.diff;

import java.awt.Dimension;
import java.awt.Toolkit;

import javax.swing.JEditorPane;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.text.html.HTMLEditorKit;

import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.gui.Controller.RunKRunCommand;

/**
 * Frame that displays the differences between two KrunStates
 *
 * @author "DanielV"
 */
public class DiffFrame extends javax.swing.JFrame {

    private static final long serialVersionUID = 1L;
    private JLabel dest;
    private JEditorPane diffEditor;
    private JScrollPane jScrollPane1;
    private JLabel src;
    private JLabel transition;

    /**
     * Creates new form DiffFrame
     */
    public DiffFrame(KRunState srcState, KRunState destState, Transition transition,
            Context context) {
        initComponents("");
        String htmlDiff;
        htmlDiff = Diff.comparableTest(
                RunKRunCommand.transformTerm(srcState.getResult(), context),
                RunKRunCommand.transformTerm(destState.getResult(), context));
        diffEditor.setText(htmlDiff);
        src.setText("Config : " + srcState.getStateId());
        dest.setText("Config : " + destState.getStateId());
        if (transition != null)
            this.transition.setText("Transition : " + transition.getLabel());
    }

    private void initComponents(String Htmldiffs) {
        jScrollPane1 = new javax.swing.JScrollPane();
        diffEditor = new javax.swing.JEditorPane();
        diffEditor.setEditable(false);
        diffEditor.setContentType("text/html");
        HTMLEditorKit kit = new HTMLEditorKit();
        diffEditor.setEditorKit(kit);
        src = new javax.swing.JLabel();
        dest = new javax.swing.JLabel();
        transition = new javax.swing.JLabel();
        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
        jScrollPane1.setViewportView(diffEditor);
        src.setText("");
        dest.setText("");
        transition.setText("");
        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(layout
                .createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                .addComponent(jScrollPane1)
                .addGroup(
                        layout.createSequentialGroup()
                                .addGap(52, 52, 52)
                                .addComponent(src)
                                .addPreferredGap(
                                        javax.swing.LayoutStyle.ComponentPlacement.RELATED,
                                        javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                                .addComponent(dest).addGap(102, 102, 102))
                .addGroup(
                        layout.createSequentialGroup().addGap(158, 158, 158)
                                .addComponent(transition).addContainerGap()));
        layout.setVerticalGroup(layout.createParallelGroup(
                javax.swing.GroupLayout.Alignment.LEADING).addGroup(
                layout.createSequentialGroup()
                        .addComponent(jScrollPane1, javax.swing.GroupLayout.PREFERRED_SIZE, 462,
                                javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addGroup(
                                layout.createParallelGroup(
                                        javax.swing.GroupLayout.Alignment.BASELINE)
                                        .addComponent(src).addComponent(dest))
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED,
                                javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(transition)));

        // pack();
        Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
        setBounds(0, 0, screenSize.width / 2, screenSize.height);
        setVisible(true);

    }
}
