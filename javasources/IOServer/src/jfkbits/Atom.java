package jfkbits;
 
import jfkbits.LispParser.Expr;
 
public class Atom implements Expr
{
    String name;
    public String toString()
    {
        return name;
    }
    public Atom(String text)
    {
        name = text;
    }
 
    public String getKIF() {
    	return "";
    }
}
