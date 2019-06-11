// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.ktree;

import org.apache.commons.io.FileUtils;
import org.kframework.attributes.Source;
import org.kframework.kore.K;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.parser.kast.KastParser;
import org.kframework.utils.errorsystem.KEMException;

import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.StandardOpenOption;

/**
 * A simple application for displaying kore files in a Swing TreeView.
 * Can load binary or textual kore format.
 * The file is parsed on the Swing thread, so the UI hangs while loading.
 */
public class KTreeViewer {
    /**
     * This needs to be invoked from the event dispatch thread.
     */
    private static void createAndShowGUI() {
        JFrame frame = new JFrame("KTree");
        frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);

        final KTreePanel tree = new KTreePanel();

        JMenuItem openMenu = new JMenuItem("Open File...");
        openMenu.addActionListener(actionEvent -> {
            JFileChooser chooser = new JFileChooser();
            int returnVal = chooser.showOpenDialog(frame);
            if (returnVal == JFileChooser.APPROVE_OPTION) {
                try {
                    K newTerm = loadFile(chooser.getSelectedFile());
                    assert newTerm != null;
                    tree.setTerm(newTerm);
                } catch (IOException e) {
                    String message;
                    if (e.getCause() != null) {
                        message = "cause:"+e.getCause().getMessage();
                    } else {
                        message = e.getMessage();
                    }
                    JOptionPane.showMessageDialog(frame,
                        "Error opening file: "+message,
                        "Error",
                        JOptionPane.ERROR_MESSAGE);
                }
            }
        });

        JMenuBar menuBar = new JMenuBar();
        menuBar.add(openMenu);
        frame.setJMenuBar(menuBar);
        frame.add(tree);

        frame.pack();
        frame.setVisible(true);
    }

    /**
     * Tries to parse a term from the given file, as either binary or textual kore.
     *
     * We don't seem to have good error returns, nor access to the KExceptionGroup
     * chosen for a KEMException, so it's hard to give a good message when neither
     * parser worked, or figure out which might have been closer to parsing the file.
     */
    private static K loadFile(File file) throws IOException {
        try {
            try {
                return KastParser.parse(FileUtils.readFileToString(file),
                        new Source(file.getName()));
            } catch (KEMException e) {
                FileChannel input = FileChannel.open(file.toPath(), StandardOpenOption.READ);
                return BinaryParser.parse(input.map(FileChannel.MapMode.READ_ONLY, 0, input.size()));
            }
        } catch (KEMException e) {
            throw new IOException("Parse Error", e);
        }
    }

    public static void main(String[] args) throws IOException {
        javax.swing.SwingUtilities.invokeLater(KTreeViewer::createAndShowGUI);
    }
}
