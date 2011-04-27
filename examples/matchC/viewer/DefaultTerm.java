import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Arrays;


public class DefaultTerm implements MaudeTerm
{

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
  public String getOp()
  {
    return op;
  }

  public String getSort()
  {
    return sort;
  }

  public List<MaudeTerm> subterms()
  {
    return subterms;
  }


  static final List<String> stringItems = new ArrayList<String>();
  static final List<MaudeTerm> termItems = new ArrayList<MaudeTerm>(); 
  static final StringBuilder buffer = new StringBuilder(1024 * 1024);

  public static void itemize(MaudeTerm term)
  {
    stringItems.clear();
    termItems.clear();
    buffer.setLength(0);
    term.getItems();
    stringItems.add(buffer.toString());
  }

  public static List<String> stringItems()
  {
    return stringItems;
  }

  public static List<MaudeTerm> termItems()
  {
    return termItems;
  }

  public void getItems()
  {
    if ("<_>_</_>".equals(op))
    {
      stringItems.add(buffer.toString());
      termItems.add(this);
      buffer.setLength(0);
      return;
    }

    int size = subterms.size();
    // mixfix operator?
    if (size > 0 && op.indexOf('_') != -1)
    {
      String[] fragments = op.replace("`", "").split("_", -1);
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
        subterms.get(index).getItems();
      }
      append(buffer, fragments[size]);
    }
    else
    {
      append(buffer, op);
      if (size > 0)
      {
        buffer.append("(");
        subterms.get(0).getItems();
        for (int index = 1; index < size; ++index)
        {
          buffer.append(", ");
          subterms.get(index).getItems();
        }
        buffer.append(")");
      }
    }
  }

  private static void append(StringBuilder buffer, String fragment)
  {
    int length = buffer.length();
    boolean isSpace = fragment.length() != 0
                 && fragment.charAt(0) != '('
                 && fragment.charAt(0) != ')'
                 && fragment.charAt(0) != '['
                 && fragment.charAt(0) != ']'
                 && fragment.charAt(0) != '{'
                 && fragment.charAt(0) != '}'
                 && fragment.charAt(0) != ','
                 && fragment.charAt(0) != '.'
                 && fragment.charAt(0) != ' '
                 && length != 0
                 && buffer.charAt(length - 1) != '('
                 && buffer.charAt(length - 1) != ')'
                 && buffer.charAt(length - 1) != '['
                 && buffer.charAt(length - 1) != ']'
                 && buffer.charAt(length - 1) != '{'
                 && buffer.charAt(length - 1) != '}'
                 && buffer.charAt(length - 1) != ','
                 && buffer.charAt(length - 1) != '.'
                 && buffer.charAt(length - 1) != ' '
                 && buffer.charAt(length - 1) != '\n';
    buffer.append(isSpace ? " " + fragment : fragment);
  }


  /*
   * Format maude tree
   */
  public static MaudeTerm format(MaudeTerm term)
  {
    final String op = term.getOp();
    final String sort = term.getSort();
    final List<MaudeTerm> subterms = term.subterms();

    for (int index = 0; index < subterms.size(); ++index)
    {
      subterms.set(index, format(subterms.get(index)));
    }

    // flatten associative operators
    if (KDefinition.assocOp.contains(op))
    {
      for (int index = 0; index < subterms.size(); ++index)
      {
        if (op.equals(subterms.get(index).getOp()))
        {
          subterms.addAll(subterms.get(index).subterms());
          subterms.remove(index);
          --index;
        }
      }
    }

    if ("_`(_`)".equals(op))
    {
      // transform labels back to syntax
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

      // plug the freezer variables back into the syntax
      if (subterms.get(0).getOp().equals("freezer"))
      {
        String freezedOp = subterms.get(0).subterms().get(0).getOp();
        int freezedLength = freezedOp.length();
        int appIndex = freezedOp.lastIndexOf('(');
        String unfreezedOp = freezedOp.substring(2, appIndex);
        String app = freezedOp.substring(appIndex + 1, freezedLength - 2);
        String[] vars = app.split(",,");
 
        String listOp = subterms.get(1).getOp();
        Map<String, MaudeTerm> subst = new HashMap<String, MaudeTerm>();
        subst.put("`[HOLE`]:K", new DefaultTerm("[]", "K"));
        if ("_`,`,_".equals(listOp) || ".List`{K`}".equals(listOp))
        {
          for (MaudeTerm var : subterms.get(1).subterms())
          {
            addFreezeVar(subst, var);
          }
        }
        else 
          addFreezeVar(subst, subterms.get(1));

        DefaultTerm unfreezedTerm = new DefaultTerm(unfreezedOp, sort);
        for (String var : vars)
        {
          unfreezedTerm.subterms().add(subst.get(var));
        }

        return unfreezedTerm;
      }

      // remove the empty list{k} applied to constant labels
      if (".List`{K`}".equals(subterms.get(1).getOp()))
        if (!"freezeVar".equals(subterms.get(0).getOp()))
        return subterms.get(0);
    }

    // delete wrappers
    if (KDefinition.wrapperOp.contains(op))
      return subterms.get(0);

    // rename operators
    if (KDefinition.renameOp.containsKey(op))
      return new DefaultTerm(KDefinition.renameOp.get(op), sort, subterms);

    //
    if (term instanceof NestedTerm)
      if ("sNat_".equals(op) && "0".equals(subterms.get(0).getOp()))
        return new DefaultTerm(((NestedTerm) term).getNumber(), sort);

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
        return new DefaultTerm("#" + name, sort);

      if (op.startsWith("default")) 
        return new DefaultTerm("default" + name, sort);

      if (op.startsWith("'default")) 
        return new DefaultTerm("'default" + name, sort);
    }

    if ("_/\\_".equals(op) && "true".equals(subterms.get(1).getOp()))
      if (subterms.size() == 2)
        return subterms.get(0);

    if ("?var".equals(op))
      return new DefaultTerm(subterms.get(0).getOp() + "_Int", sort);

    if ("PEInt".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Int", sort);
    if ("FEInt".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Int", sort);
    if ("FreeInt".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Int", sort);
    if ("PESeq".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Seq", sort);
    if ("FESeq".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Seq", sort);
    if ("FreeSeq".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Seq", sort);
    if ("PEMSet".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_MSet", sort);
    if ("FEMSet".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_MSet", sort);
    if ("FreeMSet".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_MSet", sort);
    if ("PETree".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Tree", sort);
    if ("FETree".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Tree", sort);
    if ("FreeTree".equals(sort) && subterms.size() == 0)
      return new DefaultTerm(op + "_Tree", sort);

    if ("FreeInt".equals(op) && subterms.size() == 1) 
      return new DefaultTerm("#Int" + subterms.get(0).getOp(), sort);
    if ("FreeSeq".equals(op) && subterms.size() == 1) 
      return new DefaultTerm("#Seq" + subterms.get(0).getOp(), sort);
    if ("FreeMSet".equals(op) && subterms.size() == 1) 
      return new DefaultTerm("#MSet" + subterms.get(0).getOp(), sort);
    if ("FreeTree".equals(op) && subterms.size() == 1) 
      return new DefaultTerm("#Tree" + subterms.get(0).getOp(), sort);

    if ("skolem".equals(op))
    {
      String skolemOp = subterms.get(1).getOp() + subterms.get(0).getOp();
      return new DefaultTerm("#" + skolemOp, sort);
    }

    return term;
  }

  public static void addFreezeVar(Map<String, MaudeTerm> vars, MaudeTerm var)
  {
    String varNameString = var.subterms().get(0).subterms().get(0).getOp();
    String varName = varNameString.substring(1, varNameString.length() - 1);
    // K bug, in one place the string is "List{K}", in the other  "List`{K`}"
    if (varName.endsWith("List`{K`}"))
      varName = varName.replace("List`{K`}", "List{K}");
    vars.put(varName, var.subterms().get(1));
  }

  public static boolean isString(String op)
  {
    return op.charAt(0) == '\"' && op.charAt(op.length() - 1) == '\"';
  }

}

