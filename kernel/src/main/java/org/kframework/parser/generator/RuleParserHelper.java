// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Term;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.MakeConsList;
import org.kframework.parser.concrete2.Parser;
import org.kframework.parser.concrete2.TreeCleanerVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;

public class RuleParserHelper  {

    /**
     * Takes as input a StringSentence and returns a Sentence with body, requires and ensures.
     * @param ss              Input StringSentence.
     * @param startNt         Start symbol with which to parse.
     * @param errorMessage    Error message in case of unexpected EOF.
     * @return
     */
    public static Sentence parseSentence(StringSentence ss, NonTerminal startNt, String errorMessage) {
        // parse with the new parser for rules
        Sentence st = new Sentence();
        Parser parser = new Parser(ss.getContent());
        ASTNode out = parser.parse(startNt, 0);
        try {
            // only the unexpected character type of errors should be checked in this block
            new UpdateLocationVisitor(ss.getLocation().lineStart, ss.getLocation().columnStart, 1, 1).visitNode(out);
            out = new TreeCleanerVisitor().visitNode(out);
        } catch (ParseFailedException te) {
            Parser.ParseError perror = parser.getErrors();
            String msg = ss.getContent().length() == perror.position ?
                    "Parse error: unexpected end of " + errorMessage + "." :
                    "Parse error: unexpected character '" + ss.getContent().charAt(perror.position) + "'.";
            Location loc = new Location(perror.line, perror.column, perror.line, perror.column + 1);
            loc = UpdateLocationVisitor.updateLocation(ss.getContentStartLine(), ss.getContentStartColumn(), 1, 1, loc);
            throw new ParseFailedException(new KException(
                    ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, ss.getSource(), loc));
        }
        out = new MakeConsList().visitNode(out);
        // TODO set the other parts of the sentence
        st.setBody((Term) out);
        return st;
    }
}
