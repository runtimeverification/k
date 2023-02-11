package org.kframework.lsp;

import org.kframework.attributes.Source;
import org.kframework.parser.STerm;
import org.kframework.parser.Term;
import org.kframework.parser.ToSerializable;
import org.kframework.utils.errorsystem.KEMException;
import scala.Serializable;
import scala.Tuple2;
import scala.util.Either;

import java.util.HashSet;
import java.util.Set;

public class IDECache implements Serializable {
    // TODO: it might be possible to completely remove this class
    // The K classes that we store in existing caches already have the original production as an attribute
    String input;
    Source source;
    int startLine;
    int startColumn;

    Set<KEMException> errors = new HashSet<>();
    Set<KEMException> warnings;
    STerm ast = null;

    public IDECache(String input, Source source, int startLine, int startColumn, Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> result) {
        this.input = input;
        this.source = source;
        this.startLine = startLine;
        this.startColumn = startColumn;
        warnings = new HashSet<>(result._2());
        if (result._1().isLeft())
            errors = new HashSet<>(result._1().left().get());
        else
            ast = ToSerializable.apply(result._1().right().get());
    }
}
