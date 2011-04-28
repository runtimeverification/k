import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.regex.Pattern;


public class Table {
  static class Sort {
    public static final String K    = "K";
    public static final String LIST = "List";
    public static final String BAG  = "Bag";
    public static final String SET  = "Set";
    public static final String MAP  = "Map";
  }


  static class Cell {
    public static final int NONE = 0;
    public static final int LEFT = 1;
    public static final int RIGHT = 2;
    public static final int BOTH = 3;

    public static final Cell
      CONFIG  = new Cell("config",  Sort.BAG,  false, null  ),
      PROGRAM = new Cell("program", Sort.K,    true,  CONFIG),
      STRUCT  = new Cell("struct",  Sort.MAP,  true,  CONFIG),
      FUN     = new Cell("fun",     Sort.MAP,  true,  CONFIG),
      K       = new Cell("k",       Sort.K,    true,  CONFIG),
      ENV     = new Cell("env",     Sort.MAP,  true,  CONFIG),
      STACK   = new Cell("stack",   Sort.LIST, false, CONFIG),
      FNAME   = new Cell("fname",   Sort.K,    true,  CONFIG),
      TENV    = new Cell("tenv",    Sort.MAP,  true,  CONFIG),
      HEAP    = new Cell("heap",    Sort.MAP,  false, CONFIG),
      IN      = new Cell("in",      Sort.LIST, false, CONFIG),
      OUT     = new Cell("out",     Sort.LIST, false, CONFIG),
      COUNTER = new Cell("counter", Sort.K,    true,  CONFIG);

    public final String label;
    public final String sort;
    public final boolean isDefault;
    public final HashSet<Cell> cells;
    public final Cell parent;

    public Cell(String label, String sort, boolean isDefault, Cell parent) {
      this.label = label;
      this.sort = sort;
      this.isDefault = isDefault;
      this.cells = new HashSet<Cell>();
      this.parent = parent;
    }

    public boolean isAncestor(Cell cell) {
      while (cell != null) {
        if (this == cell)
          return true;

        cell = cell.parent;
      }

     return false;
    }
  }


  public static final Map<String, Cell>
    labelToCell = new HashMap<String, Cell>();

  public static final Set<String> kernelCIdentifiers = new HashSet<String>();
  public static final Set<String> kernelCVariables = new HashSet<String>();
  public static final Set<String> annotIdentifiers = new HashSet<String>();
  public static final Set<String> annotLeftIdentifiers = new HashSet<String>();
  public static final Set<String> annotLocalVariables = new HashSet<String>();
  public static final Set<String> annotLogicalVariables = new HashSet<String>();

  public static final Map<String, String>
    varRootToSort = new HashMap<String, String>();
  public static final Map<String, String>
    varToSort = new HashMap<String, String>();


  public static void makeVars() {
    for (String id : kernelCVariables) {
      if (!varRootToSort.containsKey(id))
        varRootToSort.put(id, "Int");
    }

    for (Map.Entry<String, String> varEntry : varRootToSort.entrySet()) {
      String id = varEntry.getKey();
      String sort = varEntry.getValue();
      String maudifiedSort = null;

      if (sort.startsWith("?")) maudifiedSort = "PE" + sort.substring(1);
      else if (sort.startsWith("!")) maudifiedSort = "FE" + sort.substring(1);
      else if (sort.startsWith("Free")) maudifiedSort = sort;

      if (maudifiedSort != null)
        varToSort.put(id, maudifiedSort);
    }

    for (String id : varToSort.keySet()) {
      varRootToSort.remove(id);
    }

    for (String id : annotIdentifiers) {
      if (!kernelCIdentifiers.contains(id) && !varToSort.containsKey(id)) {
        String rootId = id.replaceAll("^(\\?|!)?_*|_*[0-9]*$", "");
        if (varRootToSort.containsKey(rootId)) {
          String rootSort = varRootToSort.get(rootId);

          String maudifiedSort;
          if (id.startsWith("?")) maudifiedSort = "PE" + rootSort;
          else if (id.startsWith("!")) maudifiedSort = "FE" + rootSort;
          else maudifiedSort = "Free" + rootSort;

          varToSort.put(id, maudifiedSort);
        }
      }
    }
  }

  static String varStringRoot = "frame";
  static int varCount = 0;
  static String varString = "";

  public static void genVarString(String prefix) {
    varString = prefix + varStringRoot + "_" + varCount++;
  }

  public static void init() {
    Cell.CONFIG.cells.add(Cell.PROGRAM);
    Cell.CONFIG.cells.add(Cell.STRUCT );
    Cell.CONFIG.cells.add(Cell.FUN    );
    // no k cell for now
    // Cell.CONFIG.cells.add(Cell.K      );
    Cell.CONFIG.cells.add(Cell.ENV    );
    Cell.CONFIG.cells.add(Cell.STACK  );
    Cell.CONFIG.cells.add(Cell.FNAME  );
    Cell.CONFIG.cells.add(Cell.TENV   );
    Cell.CONFIG.cells.add(Cell.HEAP   );
    Cell.CONFIG.cells.add(Cell.IN     );
    Cell.CONFIG.cells.add(Cell.OUT    );
    Cell.CONFIG.cells.add(Cell.COUNTER);

    labelToCell.put("config",  Cell.CONFIG );
    labelToCell.put("program", Cell.PROGRAM);
    labelToCell.put("struct",  Cell.STRUCT );
    labelToCell.put("fun",     Cell.FUN    );
    labelToCell.put("k",       Cell.K      );
    labelToCell.put("env",     Cell.ENV    );
    labelToCell.put("stack",   Cell.STACK  );
    labelToCell.put("fname",   Cell.FNAME  );
    labelToCell.put("tenv",    Cell.TENV   );
    labelToCell.put("heap",    Cell.HEAP   );
    labelToCell.put("in",      Cell.IN     );
    labelToCell.put("out",     Cell.OUT    );
    labelToCell.put("counter", Cell.COUNTER);
  }
}
