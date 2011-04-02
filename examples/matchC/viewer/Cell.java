import java.util.HashMap;
import java.util.Map;


public class Cell
{


  public final String label;
  public boolean visible;
  public int items;

  public Cell(String label)
  {
    this(label, true, -1);
  }

  public Cell(String label, boolean visible)
  {
    this(label, visible, -1);
  }

  public Cell(String label, boolean visible, int items)
  {
    this.label = label;
    this.visible = visible;
    this.items = items;
  }

}

