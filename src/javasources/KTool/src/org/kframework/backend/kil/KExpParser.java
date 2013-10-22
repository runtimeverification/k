package org.kframework.backend.kil;

import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Term;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 1/9/13
 * Time: 9:54 PM
 */
public class KExpParser {
	StreamTokenizer tokenizer;
	public  KExpParser(String s) {
		this(new StringReader(s));
	}

	public KExpParser(Reader r) {
		tokenizer = new StreamTokenizer(r);
		tokenizer.wordChars(33,126);
		tokenizer.quoteChar('"');
		tokenizer.ordinaryChar('(');
		tokenizer.ordinaryChar(')');
		tokenizer.ordinaryChar(',');
		tokenizer.ordinaryChar('[');
		tokenizer.ordinaryChar('{');
		tokenizer.ordinaryChar(']');
		tokenizer.ordinaryChar('}');
		tokenizer.ordinaryChar('`');

	}
	public Term parseK() throws ParsingException {
		try {
			tokenizer.nextToken();
		} catch (IOException e) {
			throw new ParsingException("Expected parentheses but encountered exception while parsing KExp");
		}
		if (tokenizer.ttype != '(') {
			throw new ParsingException("Expected '(' but encountered '" + (char)tokenizer.ttype + "while parsing KExp");
		}
		try {
			tokenizer.nextToken();
		} catch (IOException e) {
			throw new ParsingException("Expected token but encountered exception while parsing KExp");
		}
		if (tokenizer.ttype == ')')
			return KSequence.EMPTY;
		tokenizer.pushBack();
		Term result = new KApp(parseLabel(),parseKList());
		try {
			tokenizer.nextToken();
		} catch (IOException e) {
			throw new ParsingException("Expected parentheses but encountered exception while parsing KExp");
		}
		if (tokenizer.ttype != ')') {
			throw new ParsingException("Expected ')' but encountered '" + (char)tokenizer.ttype + "while parsing KExp");
		}
		return result;
	}

	private Term parseKList() throws ParsingException {
		try {
			tokenizer.nextToken();
		} catch (IOException e) {
			throw new ParsingException("Expected token but encountered exception while parsing KExp");
		}
		KList lok = new KList();
		while (tokenizer.ttype != ')') {
			tokenizer.pushBack();
			lok.add(parseK());
			try {
				tokenizer.nextToken();
			} catch (IOException e) {
				throw new ParsingException("Expected token but encountered exception while parsing KExp");
			}
		}
		tokenizer.pushBack();
		return lok;
	}

	private Term parseLabel() throws ParsingException {
		try {
			tokenizer.nextToken();
		} catch (IOException e) {
			throw new ParsingException("Expected token but encountered exception while parsing KExp");
		}
		if (tokenizer.ttype != '(') {

		}
		return null;
	}

	private class ParsingException extends Throwable {
		public ParsingException(String s) {
			super(s);
		}
	}
}
