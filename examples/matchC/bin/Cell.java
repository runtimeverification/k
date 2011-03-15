import java.util.HashMap;
import java.util.Map;


public class Cell
{

  public static Map<String, Cell> cells = new HashMap<String, Cell>();
  static
  {
    cells.put(       "top",        new Cell("top"));
    cells.put(  "feasible",   new Cell("feasible"));
    cells.put("infeasible", new Cell("infeasible"));
    cells.put(     "check",      new Cell("check", false));
    cells.put(     "tasks",      new Cell("tasks"));
    cells.put(   "funTask",    new Cell("funTask"));
    cells.put(     "funId",      new Cell("funId"));
    cells.put(      "task",       new Cell("task"));
    cells.put(  "taskType",   new Cell("taskType", false));
    cells.put(    "config",     new Cell("config"));
    cells.put(   "program",    new Cell("program", false));
    cells.put(    "struct",     new Cell("struct", false));
    cells.put(       "fun",        new Cell("fun", false));
    cells.put(         "k",          new Cell("k",  true, 5));
    cells.put(       "env",        new Cell("env"));
    cells.put(     "stack",      new Cell("stack"));
    cells.put(      "tenv",       new Cell("tenv", false));
    cells.put(      "heap",       new Cell("heap"));
    cells.put(        "in",         new Cell("in"));
    cells.put(       "out",        new Cell("out"));
    cells.put(   "counter",    new Cell("counter"));
    cells.put(      "form",       new Cell("form"));
    cells.put(     "subst",      new Cell("subst"));
    cells.put("funCounter", new Cell("funCounter"));
  }

  public final String label;
  public boolean visible;
  public int items;

  public Cell(String label)
  {
    this(label, true, 0);
  }

  public Cell(String label, boolean visible)
  {
    this(label, visible, 0);
  }

  public Cell(String label, boolean visible, int items)
  {
    this.label = label;
    this.visible = visible;
    this.items = items;
  }

}

