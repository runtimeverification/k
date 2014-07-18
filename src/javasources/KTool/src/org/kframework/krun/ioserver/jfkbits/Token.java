// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.jfkbits;
import java.io.StreamTokenizer;

public class Token
{
    public static final int SYMBOL = StreamTokenizer.TT_WORD;
    public int type;
    public String text;
    public int line;

    public Token(StreamTokenizer tzr)
    {
        this.type = tzr.ttype;
        this.text = tzr.sval;
        this.line = tzr.lineno();
    }

    public String toString()
    {
        switch(this.type)
        {
            case SYMBOL:
            case '"':
                return this.text;
            default:
                return String.valueOf((char)this.type);
        }
    }
}
