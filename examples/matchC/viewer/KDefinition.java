import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;


public class KDefinition
{

  public static final Map<String, Cell> cells = new HashMap<String, Cell>();
  public static final Map<String, String> renameOp = new HashMap<String, String>();
  public static final Set<String> wrapperOp = new HashSet<String>();
  public static final Set<String> assocOp = new HashSet<String>();


  static
  {
    initCells();
    initRenameOp();
    initWrapperOp();
    initAssocOp();
  }


  static void initCells()
  {
    cells.put(       "top",        new Cell("top"));
    cells.put(  "feasible",   new Cell("feasible"));
    cells.put("infeasible", new Cell("infeasible"));
    cells.put(     "check",      new Cell("check", false));
    cells.put(   "mainOut",    new Cell("mainOut"));
    cells.put(     "tasks",      new Cell("tasks",  true, 1));
    cells.put(   "funTask",    new Cell("funTask",  true, 3));
    cells.put(     "funId",      new Cell("funId"));
    cells.put(      "task",       new Cell("task"));
    cells.put(  "taskType",   new Cell("taskType", false));
    cells.put(    "config",     new Cell("config"));
    cells.put(   "program",    new Cell("program", false));
    cells.put(    "struct",     new Cell("struct", false));
    cells.put(       "fun",        new Cell("fun", false));
    cells.put(         "k",          new Cell("k",  true, 5));
    cells.put(       "env",        new Cell("env"));
    cells.put(     "fname",      new Cell("fname", false));
    cells.put(     "stack",      new Cell("stack"));
    cells.put(      "tenv",       new Cell("tenv", false));
    cells.put(      "heap",       new Cell("heap"));
    cells.put(        "in",         new Cell("in"));
    cells.put(       "out",        new Cell("out"));
    cells.put(   "counter",    new Cell("counter", false));
    cells.put(      "form",       new Cell("form"));
    cells.put(     "subst",      new Cell("subst"));
  }

  static void initRenameOp()
  {
    renameOp.put("TrueFormula", "true");
    renameOp.put("FalseFormula", "false");
    renameOp.put(".Subst", ".");

    renameOp.put("_===_", "_=_");

    renameOp.put("_+Int_", "_+_");
    renameOp.put("_-Int_", "_-_");
    renameOp.put("_*Int_", "_*_");
    renameOp.put("_/Int_", "_/_");
    renameOp.put("_%Int_", "_%_");
    renameOp.put("_>Int_", "_>_");
    renameOp.put("_>=Int_", "_>=_");
    renameOp.put("_<Int_", "_<_");
    renameOp.put("_<=Int_", "_<=_");
    renameOp.put("-Int_", "-_");

    renameOp.put("'_`,`,`,_", "'_`,_");
    renameOp.put("_;;_", "__");

    renameOp.put("tv`(_`,_`)", "`(`(_`) _`)");
    renameOp.put("'assertNormal`(_`)", "'@`assert_");

  }

  static void initWrapperOp()
  {
    wrapperOp.add("List`{MathObj++`}_");
    wrapperOp.add("Formula_");
    wrapperOp.add("Subst_");
    wrapperOp.add("Id_");
    wrapperOp.add("ExpressionType_");
    wrapperOp.add("TypedValue_");
    wrapperOp.add("@_");
    wrapperOp.add("stream");
    wrapperOp.add("wlist_");
  }

  static void initAssocOp()
  {
    assocOp.add("__");
    assocOp.add("_~>_");
    assocOp.add("_\\/_");
    assocOp.add("_/\\_");
    assocOp.add("_;;_");
  }

}

