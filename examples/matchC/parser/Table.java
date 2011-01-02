import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;


public class Table {
  static class Cell {
    public static final String K = "K";
    public static final String LIST = "List";
    public static final String BAG = "Bag";
    public static final String SET = "Set";
    public static final String MAP = "Map";

    public final String label;
    public final String sort;
    public final boolean defaultFlag;
    ArrayList<Cell> cells;

    public Cell(String label, String sort, boolean defaultFlag) {
      this.label = label;
      this.sort = sort;
      this.defaultFlag = defaultFlag;
      cells = new ArrayList<Cell>();
    }
  }

  public static final HashMap<String, Cell>
    config = new HashMap<String, Cell>();

  public static final HashSet<String> identifiers = new HashSet<String>();

  

  public static void init() {
    config.put("config",  new Cell("config",  Cell.BAG,  false));
    config.put("program", new Cell("program", Cell.K,    true ));
    config.put("struct",  new Cell("struct",  Cell.MAP,  true ));
    config.put("fun",     new Cell("fun",     Cell.MAP,  true ));
    config.put("k",       new Cell("k",       Cell.K,    true ));
    config.put("env",     new Cell("env",     Cell.MAP,  true ));
    config.put("stack",   new Cell("stack",   Cell.LIST, false));
    config.put("tenv",    new Cell("tenv",    Cell.MAP,  true ));
    config.put("heap",    new Cell("heap",    Cell.MAP,  false));
    config.put("in",      new Cell("in",      Cell.LIST, false));
    config.put("out",     new Cell("out",     Cell.LIST, false));
    config.put("counter", new Cell("counter", Cell.K,    true ));

    config.get("config").cells.add(config.get("program"));
    config.get("config").cells.add(config.get("struct"));
    config.get("config").cells.add(config.get("fun"));
    config.get("config").cells.add(config.get("k"));
    config.get("config").cells.add(config.get("env"));
    config.get("config").cells.add(config.get("stack"));
    config.get("config").cells.add(config.get("tenv"));
    config.get("config").cells.add(config.get("heap"));
    config.get("config").cells.add(config.get("in"));
    config.get("config").cells.add(config.get("out"));
    config.get("config").cells.add(config.get("counter"));
  }
}
