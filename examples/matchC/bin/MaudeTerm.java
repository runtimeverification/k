import java.util.List;


public interface MaudeTerm
{

  public String getOp();
  public String getSort();
  public List<MaudeTerm> subterms();
  public StringBuilder toMaudeString(StringBuilder buffer, int indent);

}

