import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Arrays;


public class DefaultTerm implements MaudeTerm
{

  static final Map<String, String> renameOp = new HashMap<String, String>();

  final String op;
  final String sort;
  final ArrayList<MaudeTerm> subterms;

  public DefaultTerm(String op, String sort)
  {
    this.op = op;
    this.sort = sort;
    this.subterms = new ArrayList<MaudeTerm>();
  }

  public DefaultTerm(String op, String sort, Collection<MaudeTerm> subterms)
  {
    this(op, sort);
    this.subterms.addAll(subterms);
  }


  /*
   * MaudeTerm Methods
   */
  public final String getOp()
  {
    return op;
  }

  public final String getSort()
  {
    return sort;
  }

  public final List<MaudeTerm> subterms()
  {
    return subterms;
  }

  public final StringBuilder toMaudeString(StringBuilder buffer, int indent)
  {
    int size = subterms.size();

    if ("<_>_</_>".equals(op))
    {
      ++indent;
      buffer.append("\n");
      for(int i = 0; i < indent; ++i)
        buffer.append("  ");
    }

    // mixfix operator?
    if (size > 0 && op.indexOf('_') != -1)
    {
      String[] fragments = op.replace("`", "").split("_", -1);

      // assoc operator?
      if (fragments.length != size + 1 && fragments.length != 3)
      {
        System.err.println("error: " + op + " has " + size + " args");
        System.err.println("arg 1: " + subterms.get(0).getOp());
        System.err.println("arg 2: " + subterms.get(1).getOp());
      }
      if (fragments.length != size + 1 && fragments.length == 3)
      {
        String[] tmp = new String[size + 1];
        tmp[0] = fragments[0];
        tmp[size] = fragments[2];
        Arrays.fill(tmp, 1, size, fragments[1]);
        fragments = tmp;
      }

      for (int index = 0; index < size; ++index)
      {
        append(buffer, fragments[index]);
        subterms.get(index).toMaudeString(buffer, indent);
      }
      append(buffer, fragments[size]);
    }
    else
    {
      append(buffer, op);

      if (size > 0)
      {
        buffer.append("(");
        subterms.get(0).toMaudeString(buffer, indent);

        for (int index = 1; index < size; ++index)
        {
          buffer.append(", ");
          subterms.get(index).toMaudeString(buffer, indent);
        }

        buffer.append(")");
      }
    }

    return buffer;
  }

  private static void append(StringBuilder buffer, String fragment)
  {
    int length = buffer.length();
    boolean isSpace = fragment.length() != 0
                 && Character.isLetterOrDigit(fragment.charAt(0))
                 && length != 0
                 && Character.isLetterOrDigit(buffer.charAt(length - 1));
    buffer.append(isSpace ? " " + fragment : fragment);
  }


  public static void init()
  {
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
  }

  public static boolean isWrapper(String op)
  {
    return "List`{MathObj++`}_".equals(op)
        || "@_".equals(op)
        || "Formula_".equals(op)
        || "Subst_".equals(op)
        || "Id_".equals(op)
        || "ExpressionType_".equals(op)
        || "wlist_".equals(op); 
  }

  public static boolean isString(String op)
  {
    return op.charAt(0) == '\"' && op.charAt(op.length() - 1) == '\"';
  }


  public static MaudeTerm format(MaudeTerm term)
  {
    final String op = term.getOp();
    final String sort = term.getSort();
    final List<MaudeTerm> subterms = term.subterms();

    for (int index = 0; index < subterms.size(); ++index)
    {
      subterms.set(index, format(subterms.get(index)));
    }

    if ("_`(_`)".equals(op))
    {
      if (subterms.get(0).getOp().startsWith("'"))
      {
        String syntax = subterms.get(0).getOp().substring(1);
        String listOp = subterms.get(1).getOp();
        MaudeTerm syntaxTerm = new DefaultTerm(syntax, sort);
        if ("_`,`,_".equals(listOp) || ".List`{K`}".equals(listOp))
          syntaxTerm.subterms().addAll(subterms.get(1).subterms());
        else
          syntaxTerm.subterms().add(subterms.get(1));
        return syntaxTerm;
      }

      if (".List`{K`}".equals(subterms.get(1).getOp()))
        return subterms.get(0);
    }

    if (isWrapper(op))
      return subterms.get(0);

    if (renameOp.containsKey(op))
      return new DefaultTerm(renameOp.get(op), sort, subterms);

    if (term instanceof NestedTerm)
      if ("sNat_".equals(op) && "0".equals(subterms.get(0).getOp()))
        return new DefaultTerm(((NestedTerm) term).getNumber(), sort);

   if ("?var".equals(op))
      return subterms.get(0);

   if (subterms.size() == 1 && isString(subterms.get(0).getOp()))
   {
      MaudeTerm subterm = subterms.get(0);
      String name = subterm.getOp().substring(1, subterm.getOp().length() - 1);
      if ("id`(_`)".equals(op))
        return new DefaultTerm(name, sort);

      if (op.startsWith("?")) 
        return new DefaultTerm("?" + name, sort);

      if (op.startsWith("!")) 
        return new DefaultTerm("!" + name, sort);

      if (op.startsWith("Free")) 
        return new DefaultTerm("Free" + name, sort);

      if (op.startsWith("default")) 
        return new DefaultTerm("default" + name, sort);
    }

    return term;
  }

}
