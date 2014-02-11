package org.kframework.kcheck.gui;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kcheck.KCheckFrontEnd;
import org.kframework.kcheck.RLBackend;
import org.kframework.kil.loader.Context;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.List;

/**
 * Created by andrei on 2/11/14.
 */
public class KCheckMainWindow extends JFrame implements KeyListener, ActionListener {

    private JPanel mainPanel;

    // edit panels
    private JTextPane pi1, phi1, pi2, phi2;

    // scroll panels
    private JScrollPane sphi2, spi2, sphi1, spi1;

    // labels
    private JLabel and;

    // console
    private JTextPane console;
    private JScrollPane sConsole;

    // definition setup
    private JTextField def;
    private JButton loadDef;

    // program setup
    private JTextField pgm;
    private JButton loadPgm;

    // verification setup
    private JTextField file;
    private JButton loadFile;
    private JButton addToFile;
    private JButton kcheckFile;

    // actions
    private final String BROWSE_FILE = "browse_file";
    private final String BROWSE_PGM = "browse_pgm";
    private final String BROWSE_DEF = "browse_def";
    private final String VERIF = "verify";
    private final String ADD = "add";

    /**
     * The Main kcheck window
     */
    public KCheckMainWindow() {
        // initialize the main Panel, use GridBagLayout
        mainPanel = new JPanel(new GridBagLayout());
        mainPanel.setVisible(true);
        mainPanel.setDoubleBuffered(true);
        mainPanel.setBackground(Color.lightGray);
        Dimension dimension = Toolkit.getDefaultToolkit().getScreenSize();
        mainPanel.setPreferredSize(new Dimension(dimension.width - (dimension.width / 5), dimension.height - (dimension.height / 10)));
        this.getContentPane().add(mainPanel);
        this.pack();

        // setup the main grid constraints
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.HORIZONTAL;

        // keep the level number
        int levely = 0;


        /**
         * Main menu
         */

        // Definition
        JLabel defLabel = new JLabel("Definition: ");
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(defLabel, c);

        def = new JTextField();
        def.setEditable(false);
        c.anchor = GridBagConstraints.EAST;
        c.gridx = 1;
        c.gridy = levely;
        mainPanel.add(def, c);

        loadDef = new JButton("Browse K definition");
        loadDef.setActionCommand(BROWSE_DEF);
        loadDef.addActionListener(this);
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(loadDef, c);


        // Program
        levely++;
        JLabel pgmLabel = new JLabel("Program: ");
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(pgmLabel, c);

        pgm = new JTextField();
        pgm.setEditable(false);
        c.anchor = GridBagConstraints.EAST;
        c.gridx = 1;
        c.gridy = levely;
        mainPanel.add(pgm, c);

        loadPgm = new JButton("Browse program");
        loadPgm.setActionCommand(BROWSE_PGM);
        loadPgm.addActionListener(this);
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(loadPgm, c);


        /**
         * End Menu
         */

        /**
         * SETUP PI_1 /\ PHI_1
         */
        levely++;

        JLabel piphi = new JLabel("\u03C0 \u2227 \u03C6:");
        c.anchor = GridBagConstraints.BASELINE;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(piphi, c);

        // setup the pi1 panel
        Dimension leftSize = new Dimension(dimension.width / 3, dimension.height / 4);
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 1;
        c.gridy = levely;
        pi1 = initializeEditPane(this);
        spi1 = wrapScrollEditPane(pi1, leftSize);
        mainPanel.add(spi1, c);


        // setup label /\
        and = new JLabel("\u2227");
        c.anchor = GridBagConstraints.BASELINE;
        c.gridx = 2;
        c.gridy = levely;
        mainPanel.add(and, c);

        // setup the phi1 panel
        Dimension rightSize = new Dimension(dimension.width / 4, dimension.height / 4);
        phi1 = initializeEditPane(this);
        sphi1 = wrapScrollEditPane(phi1, rightSize);
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(sphi1, c);

        /**
         * END PI_1 /\ PHI_1
         */


        /**
         * SETUP PI_2 /\ PHI_2
         */
        levely++;

        JLabel piphi_ = new JLabel("\u03C0' \u2227 \u03C6':");
        c.anchor = GridBagConstraints.BASELINE;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(piphi_, c);

        // setup the pi2 panel
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 1;
        c.gridy = levely;
        pi2 = initializeEditPane(this);
        spi2 = wrapScrollEditPane(pi2, leftSize);
        mainPanel.add(spi2, c);


        // setup label /\
        JLabel and_2 = new JLabel("\u2227");
        c.anchor = GridBagConstraints.BASELINE;
        c.gridx = 2;
        c.gridy = levely;
        mainPanel.add(and_2, c);

        // setup the phi1 panel
        phi2 = initializeEditPane(this);
        sphi2 = wrapScrollEditPane(phi2, rightSize);
        c.anchor = GridBagConstraints.NORTHEAST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(sphi2, c);

        /**
         * END PI_2 /\ PHI_2
         */


        /**
         * Verification menu
         */

        // Check reachability rules
        levely++;
        JLabel fileLabel = new JLabel("File: ");
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(fileLabel, c);

        file = new JTextField();
        file.setEditable(false);
        c.anchor = GridBagConstraints.EAST;
        c.gridx = 1;
        c.gridy = levely;
        mainPanel.add(file, c);

        loadFile = new JButton("Browse file");
        loadFile.setActionCommand(BROWSE_FILE);
        loadFile.addActionListener(this);
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(loadFile, c);

        // Check reachability rules
        levely++;

        addToFile = new JButton("Add \u03C0 \u2227 \u03C6 \u21D2 \u03C0' \u2227 \u03C6' to file");
        addToFile.setActionCommand(ADD);
        addToFile.addActionListener(this);
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 1;
        c.gridy = levely;
        mainPanel.add(addToFile, c);

        kcheckFile = new JButton("Verify file");
        kcheckFile.setActionCommand(VERIF);
        kcheckFile.addActionListener(this);
        c.anchor = GridBagConstraints.WEST;
        c.gridx = 3;
        c.gridy = levely;
        mainPanel.add(kcheckFile, c);

        /**
         * END verification menu
         */

        /**
         * Console
         */
        levely++;

        JLabel consoleLabel = new JLabel("Console:");
        c.anchor = GridBagConstraints.NORTHWEST;
        c.gridx = 0;
        c.gridy = levely;
        mainPanel.add(consoleLabel, c);

        Dimension consoleSize = new Dimension((dimension.width / 3), (dimension.height / 4));
        console = initializeEditPane(this);
        // console.setEditable(false);
        sConsole = wrapScrollEditPane(console, consoleSize);
        c.anchor = GridBagConstraints.SOUTH;
        c.gridx = 1;
        c.gridy = levely;
        c.gridwidth = 3;
        mainPanel.add(sConsole, c);

        /**
         * End Console
         */

        // set window title
        this.setTitle("K verifier");
        this.setName("K Verif");

        // Exit on Close
        this.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
    }

    private JTextPane initializeEditPane(KeyListener keyListener) {
        JTextPane pane = new JTextPane();
        pane.setEditable(true);
        pane.setVisible(true);
        pane.addKeyListener(keyListener);
        return pane;
    }

    private JScrollPane wrapScrollEditPane(JTextPane pane, Dimension dimension) {
        JScrollPane scroll = new JScrollPane(pane);
        scroll.setPreferredSize(dimension);
        scroll.setVisible(true);
        return scroll;
    }

    @Override
    public void keyTyped(KeyEvent e) {
//        String text = pi1.getText();
//        pi1.setText(text);
    }

    @Override
    public void keyPressed(KeyEvent e) {

    }

    @Override
    public void keyReleased(KeyEvent e) {

    }

    @Override
    public void actionPerformed(ActionEvent e) {
        String cmd = e.getActionCommand();
        switch (cmd) {
            case BROWSE_FILE:
                selectFile(file);
                GlobalSettings.CHECK = file.getText();
                break;
            case BROWSE_PGM:
                selectFile(pgm);
                break;
            case BROWSE_DEF:
                selectFile(def);
                if (def.getText().equals("null"))
                    break;

                GlobalSettings.setMainFile(def.getText());
                String lang = FileUtil.getMainModule(GlobalSettings.mainFile.getName());
                // Matching Logic & Symbolic Calculus options
                GlobalSettings.symbolicEquality = true;
                GlobalSettings.SMT = true;

                Context context = new Context();

                if (context.dotk == null) {
                    try {
                        context.dotk = new File(GlobalSettings.mainFile.getCanonicalFile().getParent() + File.separator + ".k");
                    } catch (IOException ioe) {
                        GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Canonical file cannot be obtained for main file.", GlobalSettings.mainFile.getAbsolutePath(),
                                "File system."));
                        JOptionPane.showMessageDialog(this, new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Canonical file cannot be obtained for main file.", GlobalSettings.mainFile.getAbsolutePath(),
                                "File system.").toString());
                    }
                    context.dotk.mkdirs();
                }

                Backend backend = new RLBackend(Stopwatch.sw, context);
                KCheckFrontEnd.output = FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled";
                context.dotk = new File(KCheckFrontEnd.output);
                context.dotk.mkdirs();

                KCheckFrontEnd.genericCompile(lang, backend, null, context);
                BinaryLoader.save(context.dotk.getAbsolutePath() + "/compile-options.bin", cmd);

                KCheckFrontEnd.verbose(KCheckFrontEnd.cmd, context);
                break;
            case ADD:
                break;
            case VERIF:
                break;
        }

    }

    private void selectFile(JTextField field) {
        final JFileChooser fc = new JFileChooser();
        int response = fc.showOpenDialog(this);
        if (response == JFileChooser.FILES_ONLY) {
            field.setBackground(Color.WHITE);
            field.setText(fc.getSelectedFile().getAbsolutePath());
        } else {
            JOptionPane.showMessageDialog(this, "Please select a file.");
            field.setText("null");
            field.setBackground(Color.RED);
        }
    }
}
