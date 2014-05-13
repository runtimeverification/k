// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.jfkbits;

import org.kframework.krun.ioserver.jfkbits.LispParser.Expr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;

 
public class ExprList extends ArrayList<Expr> implements Expr
{
    String kif = "";
    
    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    ExprList parent = null;
    int indent =1;
 
    public int getIndent()
    {
        if (parent != null)
        {
            return parent.getIndent()+indent;
        }
        else return 0;
    }
 
    public void setIndent(int indent)
    {
        this.indent = indent;
    }
 
 
 
    public void setParent(ExprList parent)
    {
        this.parent = parent;
    }
 
    public String toString()
    {
        String indent = "";
        if (parent != null && parent.get(0) != this)
        {
            indent = "\n";
            char[] chars = new char[getIndent()];
            Arrays.fill(chars, ' ');
            indent += new String(chars);        
        }
 
        String output = indent+"(";
        for(Iterator<Expr> it=this.iterator(); it.hasNext(); ) 
        {
            Expr expr = it.next();
            output += expr.toString();
            if (it.hasNext())
                output += " ";
        }
        output += ")";
        return output;
    }
 
    @Override
    public synchronized boolean add(Expr e)
    {
        if (e instanceof ExprList)
        {
            ((ExprList) e).setParent(this);
            if (size() != 0 && get(0) instanceof Atom)
                ((ExprList) e).setIndent(2);
        }
        return super.add(e);
    }
    
    public String getKIF()
    {
        String internal = "";
        for(Iterator<Expr> it=this.iterator(); it.hasNext(); ) 
        {
            Expr expr = it.next();
            if (expr.toString().equals("define-fun"))
            {
                internal += it.next().toString().trim() + "#";
                it.next();
                internal += it.next().toString().trim() + "#";
                internal += it.next().toString().trim().replaceAll("[\\(\\)\\s+]*", "") + "$";
            }
            internal += expr.getKIF() + "##";
        }
        return internal.replaceAll("#+", "#").replaceAll("\\\\s+", "");
    }
}
