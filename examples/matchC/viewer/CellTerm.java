public class CellTerm
{

  public final String cellName;

  public String getOp()
  {
    return "<" + cellName + ">_</" + cellName + ">";
  }

  public String getSort()
  {
    return "BagItem";
  }

  public CellTerm(String cellName)
  {
    this.cellName = cellName;
  }

}
