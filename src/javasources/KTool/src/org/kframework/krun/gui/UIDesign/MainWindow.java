// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;

import org.kframework.krun.gui.Controller.RunKRunCommand;

public class MainWindow extends JFrame {

    private static final long serialVersionUID = 3473620040436748664L;
    private static MainWindow window;
    JTabbedPane tabbedPanel;
    JMenuBar menuBar;
    JMenu menu;
    
    public final Object lock = new Object();
    private boolean error;
    
    public static MainWindow instance() {
        return window;
    }
    
    public boolean error() {
        return error;
    }

    public MainWindow(RunKRunCommand command) {
        Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
        this.setPreferredSize(screenSize);
        this.setExtendedState(MAXIMIZED_BOTH);
        this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        tabbedPanel = new JTabbedPane();
        tabbedPanel.add("Debug", new GraphRepresentation(command));
        // do not allow to close the default tab
        // tabbedPanel.setTabComponentAt(0,
        // new ButtonTabComponent(tabbedPanel));
        this.getContentPane().add(tabbedPanel);
        addMenu();
        this.pack();
        this.setVisible(true);
        window = this;
    }

    private void addMenu() {
        menuBar = new JMenuBar();
        menu = new JMenu("File");
        menu.setMnemonic(KeyEvent.VK_A);
        menuBar.add(menu);
        JMenuItem menuItem = new JMenuItem("Save configuration", KeyEvent.VK_S);
        menuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_S, ActionEvent.CTRL_MASK));
        menuItem.getAccessibleContext().setAccessibleDescription(
                "Save selected configuration to a file");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                saveConfs();
            }
        });
        menu.add(menuItem);

        JMenuItem menuItemLoad = new JMenuItem("Load configuration", KeyEvent.VK_S);
        menuItemLoad.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_L, ActionEvent.CTRL_MASK));
        menuItemLoad.getAccessibleContext().setAccessibleDescription(
                "Save selected configuration to a file");
        menuItemLoad.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                loadConf();
            }
        });
        menu.add(menuItemLoad);

        menuItem = new JMenuItem("Export png", KeyEvent.VK_P);
        menuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, ActionEvent.CTRL_MASK));
        menuItem.getAccessibleContext().setAccessibleDescription("Saves the graph as png");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                exportPng();
            }
        });
        menu.add(menuItem);

        this.setJMenuBar(menuBar);
    }

    public static void addDebugTab(GraphRepresentation newGraph, String message) {
        window.tabbedPanel.addTab("Loaded", null, newGraph, message);
        window.tabbedPanel.setTabComponentAt(window.tabbedPanel.getTabCount() - 1,
                new ButtonTabComponent(window.tabbedPanel));
    }

    public void exportPng() {
        Component selComp = window.tabbedPanel.getSelectedComponent();
        if (selComp instanceof GraphRepresentation) {
            ((GraphRepresentation) selComp).savePng("file.png");
        }
    }

    public void saveConfs() {
        Component selComp = window.tabbedPanel.getSelectedComponent();
        if (selComp instanceof GraphRepresentation) {
            ((GraphRepresentation) selComp).saveSelectedConf();
        }
    }

    public void loadConf() {
        Component selComp = window.tabbedPanel.getSelectedComponent();
        if (selComp instanceof GraphRepresentation) {
            ((GraphRepresentation) selComp).loadConf();
        }
    }

    public static void showAndExit(String title, String message) {
        JOptionPane.showMessageDialog(window, message, title, JOptionPane.ERROR_MESSAGE);
        window.dispose();
        window.error = true;
        synchronized(MainWindow.instance().lock) {
            MainWindow.instance().lock.notify();
        }
    }
}