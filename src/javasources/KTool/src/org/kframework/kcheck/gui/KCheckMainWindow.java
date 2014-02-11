package org.kframework.kcheck.gui;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;

/**
 * Created by andrei on 2/11/14.
 */
public class KCheckMainWindow extends JFrame implements KeyListener{
    JPanel mainPanel;

    // edit panels
    JTextPane left, right;

    // scroll panels for left and right
    JScrollPane sLeft, sRight;

    // labels
    JLabel and;

    public KCheckMainWindow() {
        // initialize the main Panel, use GridBagLayout
        mainPanel = new JPanel(new GridBagLayout());
        mainPanel.setVisible(true);
        mainPanel.setDoubleBuffered(true);
        mainPanel.setBackground(Color.lightGray);
        Dimension dimension = Toolkit.getDefaultToolkit().getScreenSize();
        mainPanel.setPreferredSize(dimension);
        this.getContentPane().add(mainPanel);
        this.pack();

        // setup the grid constraints
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.HORIZONTAL;

        // setup the left panel
        Dimension leftSize = new Dimension(dimension.width / 2, dimension.height / 2);
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 0;
        c.gridy = 0;
        left = new JTextPane();
        left.setEditable(true);
        left.setVisible(true);
        left.addKeyListener(this);
        sLeft = new JScrollPane(left);
        sLeft.setPreferredSize(leftSize);
        sLeft.setVisible(true);
        mainPanel.add(sLeft, c);


        // setup label /\
        and = new JLabel("/\\");
        c.anchor = GridBagConstraints.BASELINE;
        c.gridx = 1;
        c.gridy = 0;
        mainPanel.add(and, c);

        right = new JTextPane();
        right.setVisible(true);
        right.setPreferredSize(new Dimension(dimension.width / 4, dimension.height / 2));
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 2;
        c.gridy = 0;
        mainPanel.add(right, c);

        // set window title
        this.setTitle("K verifier");

        // Exit on Close
        this.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
    }

    @Override
    public void keyTyped(KeyEvent e) {
        String text = left.getText();
//        left.setText("<p>" + text + "</p>");
//        left.revalidate();
//        left.repaint();
        System.out.println(text);
    }

    @Override
    public void keyPressed(KeyEvent e) {

    }

    @Override
    public void keyReleased(KeyEvent e) {

    }
}
