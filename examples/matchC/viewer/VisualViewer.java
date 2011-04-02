import java.awt.BorderLayout;
import java.awt.FlowLayout;

import java.awt.event.*;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JSeparator;
import javax.swing.JToolBar;
import javax.swing.JButton;
import javax.swing.JScrollPane;
import javax.swing.JTree;

import javax.swing.event.*;

import javax.swing.UIManager;
import javax.swing.SwingUtilities;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;

//import com.jgoodies.looks.windows.*;
//import com.jgoodies.looks.plastic.*;

import com.sun.java.swing.plaf.nimbus.NimbusLookAndFeel;

public class VisualViewer implements ActionListener, TreeExpansionListener
{

  JFrame frame;
  JToolBar toolBar;
  JButton plusButton;
  JButton minusButton;
  JSeparator separator;
  JScrollPane scrollPane;
  JTree tree;

  public VisualViewer (KTreeNode root)
  {
    try
    {
      //UIManager.setLookAndFeel(new WindowsLookAndFeel());
      //UIManager.setLookAndFeel(new PlasticXPLookAndFeel());
      //UIManager.setLookAndFeel(new Plastic3DLookAndFeel());
      UIManager.setLookAndFeel(new NimbusLookAndFeel());
      //SwingUtilities.updateComponentTreeUI(frame);
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }

    toolBar = new JToolBar();
    plusButton = new JButton("+");
    plusButton.setActionCommand("zoom_in");
    plusButton.setToolTipText("zoom in");
    plusButton.addActionListener(this);
    minusButton = new JButton("-");
    minusButton.setActionCommand("zoom_out");
    minusButton.setToolTipText("zoom out");
    minusButton.addActionListener(this);
    toolBar.add(plusButton);
    toolBar.add(minusButton);

    separator = new JSeparator();

    tree = new JTree(root);
    DefaultTreeCellRenderer renderer = new DefaultTreeCellRenderer();
    renderer.setOpenIcon(null);
    renderer.setClosedIcon(null);
    renderer.setLeafIcon(null);
    tree.setCellRenderer(renderer);
    tree.addTreeExpansionListener(this);
    scrollPane = new JScrollPane(tree);

    frame = new JFrame();
    frame.add(toolBar, BorderLayout.NORTH);
    frame.add(separator, BorderLayout.CENTER);
    frame.add(scrollPane, BorderLayout.CENTER);
    frame.setSize(640, 480);
    frame.setVisible(true);
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

  }


  public void actionPerformed(ActionEvent e)
  {
    if ("zoom_in".equals(e.getActionCommand()))
    {
      tree.setFont(tree.getFont().deriveFont(tree.getFont().getSize2D() + 2));
      SwingUtilities.updateComponentTreeUI(frame);
    }
    else if ("zoom_out".equals(e.getActionCommand()))
    {
      tree.setFont(tree.getFont().deriveFont(tree.getFont().getSize2D() - 2));
    }
  }

  public void treeExpanded(TreeExpansionEvent e)
  {
    KTreeNode node = (KTreeNode) e.getPath().getLastPathComponent();
    if ("...".equals(node.getContent()))
    {
      node.getParent().expand();
      ((DefaultTreeModel) tree.getModel()).nodeStructureChanged(node.getParent());
      //((DefaultTreeModel) tree.getModel()).reload(node.getParent());
    }
  }

  public void treeCollapsed(TreeExpansionEvent e)
  {
  }


  public static void expandTree(KTreeNode node)
  {
  }

/*  
  public static void expandTree(KTreeNode node, TreePath path)
  {
  }
*/


  public static void main (String args[])
  {
    final KTreeNode root = MaudeSAXHandler.getKTree(args[0]);
    SwingUtilities.invokeLater(new Runnable()
    {
      public void run()
      {
        new VisualViewer(root);
      }
    });
  }

}

