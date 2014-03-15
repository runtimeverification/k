package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * Initially created by Traian Florin Serbanuta
 * Date: 10/31/12
 * Time: 11:46 PM
 */
public class ContextsToHeating extends CopyOnWriteTransformer {
    private List<ModuleItem> rules = new ArrayList<ModuleItem>();
    
    public ContextsToHeating(Context context) {
           super("Contexts to Heating Rules", context);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        return ((Module)super.transform(node)).addModuleItems(rules);
    }
    
    /* assumes term has exactly one rewrite and returns the list 
     * C[v], v, t1, t2 such that
     * v is a fresh variable and term = C[t1 => t2] */
    private List<Term> splitRewrite(Term term) throws TransformerException {
        final Variable v;
        if (kompileOptions.backend.java()) {
            /* the java rewrite engine only supports heating/cooling on KItem */
            if(kompileOptions.experimental.testGen){
                if(term instanceof TermCons){
                    TermCons termCons = (TermCons)term;
                    int index = 0;
                    //TODO(OwolabiL): what if there is more than 1 KItem?
                    for (int i = 0; i < termCons.arity(); i++) {
                        if (termCons.getContents().get(i).getSort().equals("KItem")){
                            index = i;
                            break;
                        }
                    }
                    v = Variable.getFreshVar(termCons.getProduction().getChildSort(index));
                }else{
                    //TODO(OwolabiL): Remove if this is never used
                    v = Variable.getFreshVar(term.getSort());
                }

            } else{
                v = Variable.getFreshVar(KSorts.KITEM);
            }
        } else {
            v = Variable.getFreshVar(KSorts.K);
        }
        final List<Term> list = new ArrayList<Term>();
        Transformer transformer = new CopyOnWriteTransformer("splitter", context) {
            @Override public ASTNode transform(Rewrite rewrite) {
                list.add(rewrite.getLeft());
                list.add(rewrite.getRight());
                return v;
            }
        };
        Term result = (Term)term.accept(transformer);
        list.add(0, v);
        list.add(0, result);
        return list;
    }
    
    private Term substituteHole(Term term, Term replacement) throws TransformerException {
        return substituteSubstitutable(term, Hole.KITEM_HOLE, replacement);
    }

    public Term freeze(Term term) {
        try {
            return new Freezer(substituteHole(term, new FreezerHole(0)));
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
    }

    private Term substituteVariable(Term term, Variable variable, Term replacement) throws TransformerException {
        return substituteSubstitutable(term, variable, replacement);
   }

    private Term substituteSubstitutable(Term term, Term variable, Term replacement) throws TransformerException {
        HashMap<Term, Term> hashMap = new HashMap<Term, Term>();
        hashMap.put(variable, replacement);
        Substitution substitution = new Substitution(hashMap, context);
        if (term == null) {
            return null;
        }
        return (Term)term.accept(substitution);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
        Term body = (Term) node.getBody().accept(new ResolveAnonymousVariables(context));
        int countHoles = MetaK.countHoles(body, context);
        if (countHoles == 0) {
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR,
                            KExceptionGroup.CRITICAL,
                            "Contexts must have at least one HOLE.",
                            getName(),
                            node.getLocation(),
                            node.getFilename()));
        }
        Integer countRewrites = MetaK.countRewrites(body, context);
        if (countRewrites > 1) {
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR,
                            KExceptionGroup.CRITICAL,
                            "Contexts can contain at most one rewrite",
                            getName(),
                            node.getLocation(),
                            node.getFilename()));
        } else if (countRewrites == 0) {
            body = substituteHole(body, new Rewrite(Hole.KITEM_HOLE, Hole.KITEM_HOLE, context));
        }
        List<Term> r = splitRewrite(body);
        Term rewriteContext = r.get(0);
        Variable freshVariable = (Variable)r.get(1);
        Term left = r.get(2);
        Term right = r.get(3);
        if (!(left instanceof Hole)) {
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR,
                            KExceptionGroup.CRITICAL,
                            "Only the HOLE can be rewritten in a context definition",
                            getName(),
                            node.getLocation(),
                            node.getFilename()));
        }
        Term lhsHeat = rewriteContext;
        List<Term> rewriteList = new ArrayList<Term>();
        rewriteList.add(substituteHole(right, freshVariable));
        rewriteList.add(new Freezer(substituteVariable(rewriteContext, freshVariable, new FreezerHole(0))));
        Term rhsHeat = new KSequence(rewriteList);
        Rule heatingRule = new Rule(lhsHeat, rhsHeat, context);
        heatingRule.setRequires(substituteHole(node.getRequires(), freshVariable));
        heatingRule.setEnsures(substituteHole(node.getEnsures(), freshVariable));
        heatingRule.getAttributes().getContents().addAll(node.getAttributes().getContents());
        heatingRule.putAttribute(MetaK.Constants.heatingTag,"");
        if (kompileOptions.experimental.testGen) {
            // TODO(YilongL): 1) is the body always a TermCons? 2) the following
            // naming convention may not guarantee a unique label for each
            // generated heating rule; need to be revised later
            for (int i = 0; i < ((TermCons) body).getContents().size(); i++) {
                if (((TermCons) body).getContents().get(i) instanceof Rewrite) {
                    heatingRule.setLabel(MetaK.Constants.heatingTag + "("
                            + node.getAttribute("klabel") + "," + i + ")");
                    break;
                }
            }
        }
        rules.add(heatingRule);

        Rule coolingRule = new Rule(rhsHeat, lhsHeat, context);
        coolingRule.getAttributes().getContents().addAll(node.getAttributes().getContents());
        coolingRule.putAttribute(MetaK.Constants.coolingTag,"");
        if (kompileOptions.experimental.testGen) {
            // TODO(YilongL): the following naming convention may not guarantee
            // a unique label for each generated cooling rule; need to be
            // revised later
            for (int i = 0; i < ((TermCons) body).getContents().size(); i++) {
                if (((TermCons) body).getContents().get(i) instanceof Rewrite) {
                    coolingRule.setLabel(MetaK.Constants.coolingTag + "("
                            + node.getAttribute("klabel") + "," + i + ")");
                    break;
                }
            }
        }        
        rules.add(coolingRule);
        
        return null;
    }

    @Override
    public ASTNode transform(Syntax node) {
        return node;
    }

    @Override
    public ASTNode transform(Rule node) {
        return node;
    }

    @Override
    public ASTNode transform(Configuration node) {
        return node;
    }
}
