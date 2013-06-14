package org.kframework.krun.gui.UIDesign;

import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JOptionPane;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.gui.Controller.RunKRunCommand;
import org.kframework.utils.DefinitionLoader;

/**
 * 
 * @author daniel
 */
public class ConfEditor extends javax.swing.JFrame {

  private static final long serialVersionUID = 1L;

  private KRunState krunState;
  private javax.swing.JTextPane confEditorPane;
  private javax.swing.JLabel confName;
  private javax.swing.JScrollPane jScrollPane1;
  private javax.swing.JButton saveBtn;
  private javax.swing.JButton exitBtn;

  public ConfEditor(KRunState krunState) {
    this.krunState = krunState;
    initComponents();
    addSaveAction();
    addExitAction();
  }

  private void addSaveAction() {
    saveBtn.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent e) {
        ASTNode out;
        try {
          org.kframework.parser.concrete.KParser.ImportTblGround(DefinitionHelper.kompiled
                  .getCanonicalPath() + "/ground/Concrete.tbl");
          out = DefinitionLoader.parseCmdString(confEditorPane.getText(), "", "Saved from gui",
                  RunKRunCommand.definitionHelper);
          out = out.accept(new RemoveBrackets(RunKRunCommand.definitionHelper));
          out = out.accept(new AddEmptyLists(RunKRunCommand.definitionHelper));
          out = out.accept(new RemoveSyntacticCasts(RunKRunCommand.definitionHelper));
          out = out.accept(new FlattenSyntax(RunKRunCommand.definitionHelper));
          out = out.accept(new RemoveSyntacticCasts(RunKRunCommand.definitionHelper));
        } catch (Exception e1) {
          JOptionPane.showMessageDialog(ConfEditor.this, ConfEditor.this,
                  "Unable to save modified configuration due to :\n" + e1.getMessage(),
                  JOptionPane.ERROR_MESSAGE);
        }
      }
    });
  }

  private void addExitAction() {
    exitBtn.addActionListener(new ActionListener() {
      @Override
      public void actionPerformed(ActionEvent e) {
        ConfEditor.this.dispose();
      }
    });
  }

  private void initComponents() {
    jScrollPane1 = new javax.swing.JScrollPane();
    confEditorPane = new javax.swing.JTextPane();
    saveBtn = new javax.swing.JButton();
    exitBtn = new javax.swing.JButton();
    confName = new javax.swing.JLabel();

    setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);

    jScrollPane1.setViewportView(confEditorPane);

    saveBtn.setText("Save");
    exitBtn.setText("Close");

    confName.setText("Config :" + krunState.getStateId());
    confEditorPane.setText(RunKRunCommand.transformTerm(krunState.getRawResult()));
    javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
    getContentPane().setLayout(layout);
    layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(jScrollPane1)
                    .addGroup(
                            javax.swing.GroupLayout.Alignment.TRAILING,
                            layout.createSequentialGroup()
                                    .addContainerGap()
                                    .addComponent(confName)
                                    .addPreferredGap(
                                            javax.swing.LayoutStyle.ComponentPlacement.RELATED,
                                            293, Short.MAX_VALUE)
                                    .addComponent(saveBtn)
                                    .addContainerGap()
                                    .addComponent(exitBtn)
                                    .addContainerGap())
            );
    layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(
                            layout.createSequentialGroup()
                                    .addComponent(jScrollPane1,
                                            javax.swing.GroupLayout.PREFERRED_SIZE, 261,
                                            javax.swing.GroupLayout.PREFERRED_SIZE)
                                    .addPreferredGap(
                                            javax.swing.LayoutStyle.ComponentPlacement.RELATED,
                                            javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                                    .addGroup(
                                            layout.createParallelGroup(
                                                    javax.swing.GroupLayout.Alignment.BASELINE)
                                                    .addComponent(saveBtn)
                                                    .addComponent(exitBtn)
                                                    .addComponent(confName))
                                    .addContainerGap())
            );

    Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
    this.confEditorPane.setBounds(0, 0, screenSize.width / 2, (int) (screenSize.height * 0.7));
    pack();
  }

  public KRunState getKrunState() {
    return krunState;
  }

  public void setKrunState(KRunState krunState) {
    this.krunState = krunState;
  }

}
