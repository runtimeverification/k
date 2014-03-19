package org.kframework.compile.sharing;

import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.krun.K;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashSet;
import java.util.Set;


/**
 * Visitor collecting the names of the sorts with lexical productions (i.e.,
 * Sort ::= Token{..} or Sort ::= Lexical{...}).
 *
 * @author AndreiS
 */
public class TokenSortCollector extends BasicVisitor {

    private final Set<String> tokenSorts = new HashSet<String>();
    
    private final Set<String> nonTokenSorts = new HashSet<String>();
    
    /**
     * Collects the names of all token sorts within a specified
     * {@code Definition}.
     * 
     * @param definition
     *            the specified definition
     * @param context
     *            the context
     * @return a set representing the names of all token sorts
     * 
     * @see TokenSortCollector
     */
    public static Set<String> collectTokenSorts(Definition definition, Context context) {
        TokenSortCollector collector = new TokenSortCollector(context);
        definition.accept(collector);
        return collector.tokenSorts;
    }

    private TokenSortCollector(Context context) {
        super(context);
    }

    @Override
    public void visit(Production production) {
        if (GlobalSettings.javaBackend || K.backend.equals("java")) {
            checkIllegalProduction(production);
        } else {
            if (production.isLexical() && !production.containsAttribute(Constants.VARIABLE)) {
                tokenSorts.add(production.getSort());
            }
        }
    }
    
    /**
     * Checks if a specified production is valid w.r.t. its sort: namely, a
     * lexical production should have a token sort and a non-lexical production
     * should have a non-token sort. Throws a K exception when one of the two
     * restrictions is violated. Currently, this check is only enabled in the
     * Java backend.
     * 
     * @param production
     *            the specified production
     */
    private void checkIllegalProduction(Production production) {
        String sort = production.getSort();
        
        if (production.isLexical() && !production.containsAttribute(Constants.VARIABLE)) {
            if (nonTokenSorts.contains(sort)) {
                String msg = "Cannot subsort a lexical production to a non-token sort:\nsyntax "
                        + sort + " ::= " + production;
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER, msg,
                        production.getFilename(), production.getLocation()));
            }
            
            tokenSorts.add(sort);
        }
        
        if (!production.isLexical() && !production.containsAttribute(Constants.FUNCTION)) {
            /*
             * The second check above is used to filter out cases such as the following:
             *   syntax Id ::= "String2Id" "(" String ")"  [function, klabel(String2Id)] 
             */
            if (tokenSorts.contains(sort) &&
                    // syntax Id ::= "Main" would be automatically transformed into a constant
                    // in a late post-processing, so don't check this kind of productions
                    !(production.getItems().size() == 1 && production.getItems().get(0) instanceof Terminal)) {
                String msg = "Cannot subsort a non-lexical production to a token sort:\nsyntax "
                        + sort + " ::= " + production;
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER, msg,
                        production.getFilename(), production.getLocation()));
            }
            
            nonTokenSorts.add(sort);
        }
    }

    @Override
    public void visit(Rule node) { }

    @Override
    public void visit(org.kframework.kil.Context node) { }

    @Override
    public void visit(Configuration node) { }

}
