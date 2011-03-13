public class NestedTerm extends DefaultTerm
{

  final String number;

  public NestedTerm(String op, String number, String sort)
  {
    super(op, sort);
    this.number = number;
  }

  public final String getNumber()
  {
    return number;
  }

}

