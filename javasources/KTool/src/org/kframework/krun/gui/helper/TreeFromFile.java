package org.kframework.krun.gui.helper;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;

import org.kframework.utils.file.KPaths;

public class TreeFromFile {

  private DefaultMutableTreeNode top;
  public JTree tree;
  private String SUBSUBSECTION_DELIMITER = "\\\\subsubsection";
  private String PARAGRAPH_DELIMITER = "\\\\paragraph";
  private String LABEL_DELIMITER = "\\\\label";
  private String GRAPHIC_DEBUGGER_IDENTIFIER = "Debugging programs graphically";
  private String[] latexTerms = { "\\\\ref", "\\{[A-Za-z-: ]*\\}", "\\\\verb", "\\\\texttt",
      "\\\\label", "[{}\\\\^\\\\*/@]" };

  public TreeFromFile() {
    top = new DefaultMutableTreeNode(new TreeNode("Graphical debugger"));
    readFile();

    tree = new JTree(top);
    tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
  }

  public void readFile() {
    getParagraphs(getManualContentforGraphDebugger(buildPathToFile()));
  }

  // returns path to the ref-manual.k
  public String buildPathToFile() {
    return KPaths.getKBase(false) + System.getProperty("file.separator") +
            "documentation" + System.getProperty("file.separator") + "ref-manual.k";
  }

  public String getManualContentforGraphDebugger(String filePath) {
    Scanner scanner = null;
    try {
      scanner = new Scanner(new File(filePath));
      // divide entire content into the contents of subsubsection to extract the
      // needed information
      scanner.useDelimiter(SUBSUBSECTION_DELIMITER);
      while (scanner.hasNext()) {
        String currentSection = scanner.next();
        if (currentSection.contains(GRAPHIC_DEBUGGER_IDENTIFIER))
        {
          return currentSection;
        }
      }
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } finally {
      if (scanner != null)
        scanner.close();
    }
    return "";
  }

  public void setTopContent(String content) {
    ((TreeNode) top.getUserObject()).setContent(replaceLatexTerms(content));
  }

  public void getParagraphs(String content) {
    String[] paragraphs = content.split(PARAGRAPH_DELIMITER);
    setTopContent(paragraphs[0]);
    for (int i = 1; i < paragraphs.length; i++) {
      if (!verifyChildren(paragraphs[i])) {
        DefaultMutableTreeNode paragraph = new DefaultMutableTreeNode(new TreeNode(
                getPrintableName(paragraphs[i].split("\n")[0]), replaceLatexTerms(paragraphs[i])));
        top.add(paragraph);
      }
      else
      {
        DefaultMutableTreeNode paragraph = new DefaultMutableTreeNode(new TreeNode(
                getPrintableName(paragraphs[i].split("\n")[0])));
        top.add(paragraph);
        getSubParagraphs(paragraphs[i], paragraph);
      }
    }
  }

  public String getPrintableName(String paragraph) {
    return paragraph.replaceAll("[{}]", "");

  }

  public String replaceLatexTerms(String content) {
    for (int i = 0; i < latexTerms.length; i++) {
      content = content.replaceAll(latexTerms[i], "");
    }
    return content;
  }

  public void getSubParagraphs(String paragraph, DefaultMutableTreeNode parent) {
    String[] subparagraphs = paragraph.split(LABEL_DELIMITER);
    ((TreeNode) parent.getUserObject()).setContent(replaceLatexTerms(subparagraphs[1]));
    for (int i = 2; i < subparagraphs.length; i++) {
      DefaultMutableTreeNode subparagraph = new DefaultMutableTreeNode(new TreeNode(
              getPrintableName(subparagraphs[i].split("\n")[0]),
              replaceLatexTerms(subparagraphs[i])));
      parent.add(subparagraph);
    }

  }

  public boolean verifyChildren(String paragraph) {
    return paragraph.split(LABEL_DELIMITER).length > 2;
  }

}