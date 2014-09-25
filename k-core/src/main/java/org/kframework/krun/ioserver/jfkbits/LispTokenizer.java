// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.jfkbits;

import java.io.*;
import java.util.Iterator;

public class LispTokenizer implements Iterator<Token>
{
    // Instance variables have default access to allow unit tests access.
    StreamTokenizer m_tokenizer;
    IOException m_ioexn;

    /** Constructs a tokenizer that scans input from the given string.
     * @param src A string containing S-expressions.
     */
    public LispTokenizer(String src)
    {
        this(new StringReader(src));
    }

    /** Constructs a tokenizer that scans input from the given Reader.
     * @param r Reader for the character input source
     */
    public LispTokenizer(Reader r)
    {
        if(r == null)
            r = new StringReader("");
        BufferedReader buffrdr = new BufferedReader(r);
        m_tokenizer = new StreamTokenizer(buffrdr);
        m_tokenizer.resetSyntax(); // We don't like the default settings

        m_tokenizer.whitespaceChars(0, ' ');
        m_tokenizer.wordChars(' '+1,255);
        m_tokenizer.ordinaryChar('(');
        m_tokenizer.ordinaryChar(')');
        m_tokenizer.ordinaryChar('\'');
        m_tokenizer.commentChar(';');
        m_tokenizer.quoteChar('"');
    }

    public Token peekToken()
    {
        if(m_ioexn != null)
            return null;
        try
        {
            m_tokenizer.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return null;
        }
        if(m_tokenizer.ttype == StreamTokenizer.TT_EOF)
            return null;
        Token token = new Token(m_tokenizer);
        m_tokenizer.pushBack();
        return token;
    }

    public boolean hasNext()
    {
        if(m_ioexn != null)
            return false;
        try
        {
            m_tokenizer.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return false;
        }
        if(m_tokenizer.ttype == StreamTokenizer.TT_EOF)
            return false;
        m_tokenizer.pushBack();
        return true;
    }

    /** Return the most recently caught IOException, if any,
     *
     * @return
     */
    public IOException getIOException()
    {
        return m_ioexn;
    }

    public Token next()
    {
        try
        {
            m_tokenizer.nextToken();
        }
        catch(IOException e)
        {
            m_ioexn = e;
            return null;
        }

        Token token = new Token(m_tokenizer);
        return token;
    }

    public void remove()
    {
    }
}
