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
      Wrapper wrapper = new Wrapper();
      wrapper.append(root.toKString());
      Writer writer = new BufferedWriter(new FileWriter(args[1]));
      writer.write(wrapper.toString());
      writer.close();
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }
  }

}
