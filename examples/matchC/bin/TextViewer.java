import java.io.Writer;
import java.io.FileWriter;
import java.io.BufferedWriter;

public class TextViewer
{

  public static void main (String args[])
  {
    try
    {
      KTreeNode root = MaudeSAXHandler.getKTree(args[0]);
      Writer writer = new BufferedWriter(new FileWriter(args[1]));
      writer.write(root.treeToString());
      writer.close();
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }
  }

}
