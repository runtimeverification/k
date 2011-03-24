import javax.swing.tree.TreeNode;

import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;


public class KTreeNode implements TreeNode
{

  final static int DEFAULT_COUNT = 5;

  String content;
  boolean isKDefinition;

  int visibleCount;
  final int visibleInc = 1;

  final KTreeNode parent;
  final ArrayList<KTreeNode> children;
  final KTreeNode ldotsNode;

  static Wrapper wrapper = new Wrapper();


  public KTreeNode(KTreeNode parent)
  {
    this(parent, "", 0);
  }

  public KTreeNode(KTreeNode parent, String content)
  {
    this(parent, content, 0);
  }

  public KTreeNode(KTreeNode parent, String content, int visibleCount)
  {
    this.parent = parent;
    children = new ArrayList<KTreeNode>(); 
    this.content = content;
    this.visibleCount = visibleCount;

    if (visibleCount != 0)
    {
      ldotsNode = new KTreeNode(this, "...", 0);
      ldotsNode.add(new KTreeNode(ldotsNode));
    }
    else
      ldotsNode = null;
  }


  public void add(KTreeNode node)
  {
    children.add(node);
  }

  public void addAll(List<KTreeNode> nodeList)
  {
    children.addAll(nodeList);
  }

  public String getContent()
  {
    return content;
  }

  public void setContent(String content)
  {
    this.content = content;
  }


  public String treeToString()
  {
    wrapper.setLeftMargin(0);
    wrapper.clean();
    bufferedTreeToString();
    return wrapper.toString();
  }

  private void bufferedTreeToString()
  {
    int size = children.size();
    if (size > 0)
    {
      if (!KDefinition.cells.get(content).visible)
      {
        wrapper.append("<" + content + "> ... </" + content + ">");
        return;
      }

      wrapper.append("<" + content + ">");
      wrapper.setLeftMargin(wrapper.getLeftMargin() + 2);
      if (size > 1 || children.get(0).children.size() > 0)
      {
        int items = KDefinition.cells.get(content).items;
        if (items != 0 && items < size)
          size = items;

        for (int index = 0; index < size; ++index)
        {
          wrapper.append("\n");
          children.get(index).bufferedTreeToString();
        }
        if (size < children.size())
        {
          wrapper.append("\n");
          wrapper.append("...");
        }
        wrapper.setLeftMargin(wrapper.getLeftMargin() - 2);
        wrapper.append("\n");
      }
      else
      {
        wrapper.append(" ");
        children.get(0).bufferedTreeToString();
        wrapper.append(" ");
        wrapper.setLeftMargin(wrapper.getLeftMargin() - 2);
      }
      wrapper.append("</" + content + ">");
    }
    else
      wrapper.append(content);
  }

  public String toString()
  {
    return content;
  }


  /*
   * TreeNode Methods
   */
  public Enumeration children()
  {
    return null;
  }

  public boolean getAllowsChildren()
  {
    return true;
  }

  public TreeNode getChildAt(int childIndex)
  {
    if (visibleCount == 0 || childIndex < visibleCount - 1)
      return children.get(childIndex);
    else if (childIndex == visibleCount - 1)
      return ldotsNode;
    else
      return null;
  }
  
  public int getChildCount()
  {
    if (visibleCount == 0 || children.size() <= visibleCount) 
      return children.size();
    else
      return visibleCount;
  }

  public int getIndex(TreeNode node)
  {
    if (visibleCount == 0 || children.size() <= visibleCount) 
      return children.indexOf(node);
    else if (ldotsNode.equals(node))
      return visibleCount - 1;
   else
      return -1;
  }

  public TreeNode getParent()
  {
    return parent;
  }

  public boolean isLeaf()
  {
    return children.size() == 0;
  }

  /*
   * Static methods to construct KTree from a Term
   */
  public static List<KTreeNode> format2(KTreeNode parent, String prefix,
                                        MaudeTerm term)
  {
    if ("<_>_</_>".equals(term.getOp()))
    {
      List nodeList = new ArrayList<KTreeNode>();
      nodeList.add(formatCell2(parent, term));
      return nodeList;
    }
    else
      return formatContent2(parent, prefix, term);
  }

  public static KTreeNode formatCell2(KTreeNode parent, MaudeTerm term)
  {
    String cellLabel = term.subterms().get(0).getOp();      
    MaudeTerm cellContent = term.subterms().get(1);
    KTreeNode node = new KTreeNode(parent, cellLabel);

    if (KDefinition.assocOp.contains(cellContent.getOp()))
    {
      String assocOp = cellContent.getOp();
      String prefixOp = assocOp.substring(1, assocOp.length() - 1) + ' ';
      String prefix = "";
      for (MaudeTerm cellItem : cellContent.subterms())
      {
        node.addAll(format2(node, prefix, cellItem));
        prefix = prefixOp;
      }
    }
    else
    {
      node.addAll(format2(node, "", cellContent));
    }

    return node;
  }

  public static List<KTreeNode> formatContent2(KTreeNode parent, String prefix,
                                               MaudeTerm term)
  {
    DefaultTerm.itemize(term);
    List<String> stringItems = DefaultTerm.stringItems();
    List<MaudeTerm> termItems = DefaultTerm.termItems();

    List nodeList = new ArrayList<KTreeNode>();
    stringItems.set(0, prefix + stringItems.get(0));
    if (!"".equals(stringItems.get(0)))
      nodeList.add(new KTreeNode(parent, stringItems.get(0)));
    for (int index = 0; index < termItems.size(); ++index)
    {
      MaudeTerm termItem = termItems.get(index);
      String stringItem = stringItems.get(index + 1);
      nodeList.add(formatCell2(parent, termItem));
      if (!"".equals(stringItem))
        nodeList.add(new KTreeNode(parent, stringItem));
    }
    return nodeList;
  }
/*
  public static KTreeNode format(KTreeNode parent, MaudeTerm term)
  {
    if ("<_>_</_>".equals(term.getOp()))
      return formatKDefinition(parent, term);
    else
      return formatContent(parent, term);
  }

  public static KTreeNode formatKDefinition(KTreeNode parent, MaudeTerm term)
  {
    KTreeNode node = null;
    String cellLabel = term.subterms().get(0).getOp();      
    MaudeTerm cellContent = term.subterms().get(1);

    if (isAssocOp(cellContent.getOp()))
    {
      //node = new KTreeNode(parent, "<" + cellLabel + "/>", DEFAULT_COUNT);
      node = new KTreeNode(parent, "<" + cellLabel + "/>");
      String assocOp = cellContent.getOp();
      String prefix = assocOp.substring(1, assocOp.length() - 1);
      buffer.setLength(0);
      for (int i = 0; i < prefix.length(); ++i)
        buffer.append(" ");
      for (MaudeTerm cellItem : cellContent.subterms())
      {
        node.add(format(node, cellItem));
        buffer.setLength(0);
        buffer.append(prefix);
      }
      buffer.setLength(0);
    }
    else
    {
      node = new KTreeNode(parent, "<" + cellLabel + "/>");
      node.add(format(node, cellContent));
    }

    return node;
  }

  public static KTreeNode formatContent(KTreeNode parent, MaudeTerm term)
  {
    KTreeNode node = new KTreeNode(parent);
    buffer.setLength(0);
    node.setContent(bufferContent(node, term).toString());

    return node;
  }

  public static StringBuilder bufferContent(KTreeNode node, MaudeTerm term)
  {
    StringBuilder buffer = new StringBuilder();

    if (!"<_>_</_>".equals(term.getOp()))
    {
      List<MaudeTerm> subterms = term.subterms();
      int size = subterms.size();

      if (size > 0 && term.getOp().indexOf('_') != -1)
      {
        String[] fragments = term.getOp().replace("`", "").split("_", -1);

        int length = fragments[0].length();
        if (!"".equals(fragments[0]) &&
            Character.isLetterOrDigit(fragments[0].charAt(length - 1)))
          fragments[0] = fragments[0] + " ";
        if (!"".equals(fragments[fragments.length -1]) &&
            Character.isLetterOrDigit(fragments[fragments.length -1].charAt(0)))
          fragments[fragments.length -1] = " " + fragments[fragments.length -1];

        for (int index = 1; index < fragments.length -1; ++index)
        {
          length = fragments[index].length();
          if (length > 0)
          {
            if (Character.isLetterOrDigit(fragments[index].charAt(0)))
              fragments[index] = " " + fragments[index];
            if (Character.isLetterOrDigit(fragments[index].charAt(length - 1)))
              fragments[index] = fragments[index] + " ";
          }
          else
            fragments[index] = " ";
        }

        if (fragments.length != size + 1 && fragments.length == 3)
        {
          String[] tmp = new String[size + 1];
          tmp[0] = fragments[0];
          tmp[size] = fragments[2];
          Arrays.fill(tmp, 1, size, fragments[1]);
          fragments = tmp;
        }

        for (int index = 0; index < size; ++index)
        {
          buffer.append(fragments[index]);
          buffer.append(bufferContent(node, subterms.get(index)));
        }

        buffer.append(fragments[size]);
      }
      else
      {
        buffer.append(term.getOp());
  
        if (size > 0)
        {
          buffer.append("(");
          buffer.append(bufferContent(node, subterms.get(0)));
             
          for (int index = 1; index < size; ++index)
          {
            buffer.append(", ");
            buffer.append(bufferContent(node, subterms.get(index)));
          }
  
          buffer.append(")");
        }
      }
    }
    else
    {
      node.add(formatKDefinition(node, term));
      buffer.append("<>");
    }

    return buffer;
  }
*/

}

