// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.helper;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;

import org.kframework.utils.file.JarInfo;

public class TreeFromFile {

    public DefaultMutableTreeNode top;
    public JTree tree;
    private String SUBSUBSECTION_DELIMITER = "\\\\subsubsection";
    private String PARAGRAPH_DELIMITER = "\\\\paragraph";
    private String LABEL_DELIMITER = "\\\\label";
    private String GRAPHIC_DEBUGGER_IDENTIFIER = "Debugging programs graphically";
    private String[] latexTerms = { "\\\\verb", "\\\\texttt", "\\\\label", "^\\{[A-Za-z-:_ ]*\\}",
            "[^\\\\ref]\\{[A-Za-z-: ]*\\}" };

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
        return JarInfo.getKBase(false) + System.getProperty("file.separator") + "documentation"
                + System.getProperty("file.separator") + "ref-manual.k";
    }

    public String getManualContentforGraphDebugger(String filePath) {
        Scanner scanner = null;
        try {
            scanner = new Scanner(new File(filePath));
            // divide entire content into the contents of subsubsection to
            // extract the
            // needed information
            scanner.useDelimiter(SUBSUBSECTION_DELIMITER);
            while (scanner.hasNext()) {
                String currentSection = scanner.next();
                if (currentSection.contains(GRAPHIC_DEBUGGER_IDENTIFIER)) {
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
        ((TreeNode) top.getUserObject()).setContent(replaceLatexTerms(content, top.getUserObject()
                .toString()));
    }

    public void getParagraphs(String content) {
        String[] paragraphs = content.split(PARAGRAPH_DELIMITER);
        setTopContent(paragraphs[0]);
        for (int i = 1; i < paragraphs.length; i++) {
            if (!verifyChildren(paragraphs[i])) {
                String nodeName = getPrintableName(paragraphs[i].split("\n")[0]);
                DefaultMutableTreeNode paragraph = new DefaultMutableTreeNode(new TreeNode(
                        nodeName, replaceLatexTerms(paragraphs[i], nodeName)));
                top.add(paragraph);
            } else {
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

    public String replaceLatexTerms(String content, String parentName) {
        for (int i = 0; i < latexTerms.length; i++) {
            content = content.replaceAll(latexTerms[i], "");
        }

        return preserveSpacing(setLinks(content), parentName);
    }

    public String setLinks(String content) {

        Pattern p = Pattern.compile("\\\\ref\\{sec:[A-za-z]*\\}");
        Matcher m = p.matcher(content);
        while (m.find()) {
            String result = m.group().toString();
        }
        content = content.replaceAll("\\\\tab", "&nbsp&nbsp&nbsp&nbsp ");
        content = content.replaceAll("\\\\ref\\{sec:", "<a href=\"\">");
        content = content.replaceAll("\\}", "</a>");
        content = content.replaceAll("[{}\\\\^\\\\*/@]", "");

        return content;
    }

    public String preserveSpacing(String content, String parentName) {

        content = content.replaceAll("\\n\\n", "<br><br>");
        content = content.replaceAll("\\.\\n", ".<br>");

        return HelpInfo.htmlPrefix + parentName + HelpInfo.htmlMiddle + content + HelpInfo.htmlEnd;
    }

    public void getSubParagraphs(String paragraph, DefaultMutableTreeNode parent) {
        String[] subparagraphs = paragraph.split(LABEL_DELIMITER);
        ((TreeNode) parent.getUserObject()).setContent(replaceLatexTerms(subparagraphs[1], parent
                .getUserObject().toString()));
        for (int i = 2; i < subparagraphs.length; i++) {
            String nodeName = getPrintableName(subparagraphs[i].split("\n")[0]);
            DefaultMutableTreeNode subparagraph = new DefaultMutableTreeNode(new TreeNode(
                    nodeName, replaceLatexTerms(subparagraphs[i], nodeName)));
            parent.add(subparagraph);
        }

    }

    public boolean verifyChildren(String paragraph) {
        return paragraph.split(LABEL_DELIMITER).length > 2;
    }

}