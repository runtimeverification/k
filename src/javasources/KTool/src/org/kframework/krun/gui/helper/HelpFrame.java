// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.helper;

import java.awt.Color;
import java.awt.Container;
import java.awt.Dimension;
import javax.swing.BoxLayout;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;

import org.kframework.kil.loader.Context;

public class HelpFrame extends JFrame {

    private static final long serialVersionUID = 1L;
    HelpInfo helpInfo;
    HelpContent helpContent;
    JScrollPane contentScroll;
    JScrollPane detailedScroll;
    JSplitPane splitPane;

    public HelpFrame(Context helper) {
        this.setForeground(Color.black);
        this.setBackground(Color.lightGray);
        Container cp = this.getContentPane();
        this.setPreferredSize(new Dimension(600, 600));
        cp.setLayout(new BoxLayout(cp, BoxLayout.X_AXIS));

        initInfo();
        initContent();
        initScrollContent();
        initScrollInfo();
        initSplitPane();

        cp.add(splitPane);
        this.pack();
        this.setVisible(true);
        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
    }

    public void initInfo() {
        helpInfo = new HelpInfo();
    }

    public void initContent() {
        helpContent = new HelpContent(helpInfo);
    }

    public void initScrollContent() {
        contentScroll = setScrollable(helpContent);
    }

    public void initScrollInfo() {
        detailedScroll = setScrollable(helpInfo);
    }

    public void initSplitPane() {
        splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        splitPane.setLeftComponent(contentScroll);
        splitPane.setRightComponent(detailedScroll);
        splitPane.setDividerLocation(200);
    }

    public JScrollPane setScrollable(JComponent scrollableComp) {
        return new JScrollPane(scrollableComp);
    }
}