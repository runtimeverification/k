package org.kframework.krun.gui.UIDesign;

import java.awt.Dimension;
import java.awt.Toolkit;

import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JTabbedPane;

import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.krun.gui.Controller.RunKRunCommand;

public class MainWindow extends JFrame {

  private static final long serialVersionUID = 1L;

  private static MainWindow window;
  JTabbedPane tabbedPanel;

  public MainWindow(RunKRunCommand command, DefinitionHelper definitionHelper) {
    Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
    this.setPreferredSize(screenSize);
    this.setExtendedState(MAXIMIZED_BOTH);
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    tabbedPanel = new JTabbedPane();
    try {
      tabbedPanel.add("Debug", new GraphRepresentation(command, definitionHelper));
      this.getContentPane().add(tabbedPanel);
    } catch (Exception e) {
      e.printStackTrace();
    }
    this.pack();
    this.setVisible(true);
    window = this;
  }

  public static void addDebugTab(Term modTerm) {
    try {
      System.out.println(RunKRunCommand.transformTerm(modTerm));
      System.out.println(modTerm.toString());
      RunKRunCommand krcmd = new RunKRunCommand(modTerm, "", RunKRunCommand.definitionHelper,
              false);
      GraphRepresentation gr = new GraphRepresentation(krcmd, RunKRunCommand.definitionHelper);
      window.tabbedPanel.add("Debug " + window.tabbedPanel.getTabCount(), gr);
      window.tabbedPanel.setSelectedComponent(gr);
    } catch (Exception e) {
    	e.printStackTrace();
      JOptionPane.showMessageDialog(window, "Unable to add new tab due to :\n" + e.getMessage(),
              "", JOptionPane.ERROR_MESSAGE);
    }
  }
}