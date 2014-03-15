package org.kframework.kil.visitors;

import java.util.*;

import org.kframework.kil.*;
import org.kframework.kil.Collection;
import org.kframework.kil.List;
import org.kframework.kil.Map;
import org.kframework.kil.Set;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ExperimentalParserOptions;


/**
 * Default implementations of methods visit non-attribute children, and then call the transform method for the parent class on the current node.
 */
public class BasicTransformer implements Transformer {
    protected Context context;
    private String name;
    
    protected KompileOptions kompileOptions;
    protected GlobalOptions globalOptions;
    protected ExperimentalParserOptions experimentalParserOptions;

    public BasicTransformer(String name, Context context) {
        this.name = name;
        this.context = context;
        this.kompileOptions = context.kompileOptions;
        this.globalOptions = context.globalOptions;
        this.experimentalParserOptions = context.experimentalParserOptions;
    }

    @Override
    public ASTNode transform(ASTNode node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(ParseError node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Definition node) throws TransformerException {
        for (int i = 0; i < node.getItems().size(); i++) {
            node.getItems().set(i, (DefinitionItem) node.getItems().get(i).accept(this));
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(DefinitionItem node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(LiterateDefinitionComment node) throws TransformerException {
        return transform((DefinitionItem) node);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        for (int i = 0; i < node.getItems().size(); i++) {
            node.getItems().set(i, (ModuleItem) node.getItems().get(i).accept(this));
        }
        return transform((DefinitionItem) node);
    }

    @Override
    public ASTNode transform(ModuleItem node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Import node) throws TransformerException {
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(LiterateModuleComment node) throws TransformerException {
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(Sentence node) throws TransformerException {
        Term body = (Term) node.getBody().accept(this);
        Term requires = node.getRequires();
        if (requires != null)
            requires = (Term) requires.accept(this);
        Term ensures = node.getEnsures();
        if (ensures != null)
            ensures = (Term) ensures.accept(this);
        node.setBody(body);
        node.setRequires(requires);
        node.setEnsures(ensures);
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        Configuration c = node.shallowCopy();
        return transform((Sentence) c);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
        org.kframework.kil.Context c = node.shallowCopy();
        return transform((Sentence) c);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        Rule r = node.shallowCopy();
        return transform((Sentence) r);
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        node.setSort((Sort) node.getSort().accept(this));
        for (int i = 0; i < node.getPriorityBlocks().size(); i++) {
            node.getPriorityBlocks().set(i, (PriorityBlock) node.getPriorityBlocks().get(i).accept(this));
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityExtended node) throws TransformerException {
        for (int i = 0; i < node.getPriorityBlocks().size(); i++) {
            node.getPriorityBlocks().set(i, (PriorityBlockExtended) node.getPriorityBlocks().get(i).accept(this));
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException {
        for (int i = 0; i < node.getTags().size(); i++) {
            node.getTags().set(i, (KLabelConstant) node.getTags().get(i).accept(this));
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityBlock node) throws TransformerException {
        for (int i = 0; i < node.getProductions().size(); i++) {
            node.getProductions().set(i, (Production) node.getProductions().get(i).accept(this));
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(PriorityBlockExtended node) throws TransformerException {
        for (int i = 0; i < node.getProductions().size(); i++) {
            node.getProductions().set(i, (KLabelConstant) node.getProductions().get(i).accept(this));
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Production node) throws TransformerException {
        for (int i = 0; i < node.getItems().size(); i++) {
            node.getItems().set(i, (ProductionItem) node.getItems().get(i).accept(this));
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(ProductionItem node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Sort node) throws TransformerException {
        return transform((ProductionItem) node);
    }

    @Override
    public ASTNode transform(Terminal node) throws TransformerException {
        return transform((ProductionItem) node);
    }

    @Override
    public ASTNode transform(Lexical node) throws TransformerException {
        return transform((ProductionItem) node);
    }

    @Override
    public ASTNode transform(UserList node) throws TransformerException {
        return transform((ProductionItem) node);
    }

    @Override
    public ASTNode transform(Term node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Cell node) throws TransformerException {
        Cell result = node.shallowCopy();
        result.setContents((Term) node.getContents().accept(this));
        return transform((Term) result);
    }

    @Override
    public ASTNode transform(Collection node) throws TransformerException {
        for (int i = 0; i < node.getContents().size(); i++) {
            node.getContents().set(i, (Term) node.getContents().get(i).accept(this));
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Ambiguity node) throws TransformerException {
        TransformerException exception = null;
        ArrayList<Term> terms = new ArrayList<Term>();
        for (Term t : node.getContents()) {
            ASTNode result;
            try {
                result = t.accept(this);
                terms.add((Term) result);
            } catch (TransformerException e) {
                exception = e;
            }
        }
        if (terms.isEmpty())
            throw exception;
        if (terms.size() == 1) {
            return terms.get(0);
        }
        node.setContents(terms);
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Bag node) throws TransformerException {
        Bag result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(KSequence node) throws TransformerException {
        KSequence result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(List node) throws TransformerException {
        List result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(KList node) throws TransformerException {
        KList result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(Map node) throws TransformerException {
        Map result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(Set node) throws TransformerException {
        Set result = node.shallowCopy();
        return transform((Collection) result);
    }

    @Override
    public ASTNode transform(CollectionItem node) throws TransformerException {
        node.setItem((Term) node.getItem().accept(this));
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(BagItem node) throws TransformerException {
        BagItem result = node.shallowCopy();
        return transform((CollectionItem) result);
    }

    @Override
    public ASTNode transform(ListItem node) throws TransformerException {
        ListItem result = node.shallowCopy();
        return transform((CollectionItem) result);
    }

    @Override
    public ASTNode transform(MapItem node) throws TransformerException {
        MapItem result = node.shallowCopy();
        result.setKey((Term) node.getKey().accept(this));
        result.setValue((Term) node.getValue().accept(this));
        return transform((CollectionItem) result);
    }

    @Override
    public ASTNode transform(SetItem node) throws TransformerException {
        SetItem result = node.shallowCopy();
        return transform((CollectionItem) result);
    }

    @Override
    public ASTNode transform(CollectionBuiltin node) throws TransformerException {
        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
        }

        ArrayList<Term> elements = new ArrayList<Term>(node.elements().size());
        for (Term term : node.elements()) {
            Term transformedTerm = (Term) term.accept(this);
            elements.add(transformedTerm);
        }

        return CollectionBuiltin.of(node.sort(), terms, elements);
    }

    @Override
    public ASTNode transform(SetBuiltin node) throws TransformerException {
        return transform((CollectionBuiltin) node);
    }

    @Override
    public ASTNode transform(SetLookup node) throws TransformerException {
        Variable set = (Variable) node.base().accept(this);
        Term value = (Term) node.key().accept(this);
        return new SetLookup(set, value, node.choice());
    }

    @Override
    public ASTNode transform(SetUpdate node) throws TransformerException {
        Variable set = (Variable) node.set().accept(this);

        HashSet<Term> removeEntries = new HashSet<Term>(node.removeEntries().size());
        for (Term term : node.removeEntries()) {
            Term transformedTerm = (Term) term.accept(this);
            removeEntries.add(transformedTerm);
        }

        return new SetUpdate(set, removeEntries);
    }

    @Override
    public ASTNode transform(ListBuiltin node) throws TransformerException {
        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
        }

        ArrayList<Term> elementsLeft = new ArrayList<Term>(node.elementsLeft().size());
        for (Term entry : node.elementsLeft()) {
            Term transformedEntry = (Term) entry.accept(this);
            elementsLeft.add(transformedEntry);
        }

        ArrayList<Term> elementsRight = new ArrayList<Term>(node.elementsRight().size());
        for (Term entry : node.elementsRight()) {
            Term transformedEntry = (Term) entry.accept(this);
            elementsRight.add(transformedEntry);
        }

        return ListBuiltin.of(node.sort(), elementsLeft, elementsRight, terms);
    }

    @Override
    public ASTNode transform(ListLookup node) throws TransformerException {
        Variable base = (Variable) node.base().accept(this);
        Term key = (Term) node.key().accept(this);
        Term value = (Term) node.value().accept(this);
        return new ListLookup(base, key, value, node.kind());
    }

    @Override
    public ASTNode transform(ListUpdate node) throws TransformerException {
        Variable base = (Variable) node.base().accept(this);

        ArrayList<Term> removeLeft = new ArrayList<Term>(node.removeLeft().size());
        for (Term entry : node.removeLeft()) {
            Term transformedEntry = (Term) entry.accept(this);
            removeLeft.add(transformedEntry);
        }

        ArrayList<Term> removeRight = new ArrayList<Term>(node.removeRight().size());
        for (Term entry : node.removeRight()) {
            Term transformedEntry = (Term) entry.accept(this);
            removeRight.add(transformedEntry);
        }

        return new ListUpdate(base, removeLeft, removeRight);
    }

    @Override
    public ASTNode transform(MapBuiltin node) throws TransformerException {
        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
        }

        HashMap<Term, Term> elements = new HashMap<Term, Term>(node.elements().size());
        for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            elements.put(transformedKey, transformedValue);
        }

        return new MapBuiltin(node.sort(), terms, elements);
    }

    @Override
    public ASTNode transform(MapLookup node) throws TransformerException {
        Variable map = (Variable) node.base().accept(this);
        Term key = (Term) node.key().accept(this);
        Term value = (Term) node.value().accept(this);
        return new MapLookup(map, key, value, node.kind(), node.choice());
    }

    @Override
    public ASTNode transform(MapUpdate node) throws TransformerException {
        Variable map = (Variable) node.map().accept(this);

        HashMap<Term, Term> removeEntries = new HashMap<Term, Term>(node.removeEntries().size());
        for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            removeEntries.put(transformedKey, transformedValue);
        }

        HashMap<Term, Term> updateEntries = new HashMap<Term, Term>(node.updateEntries().size());
        for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            updateEntries.put(transformedKey, transformedValue);
        }

        return new MapUpdate(map, removeEntries, updateEntries);
    }

    @Override
    public ASTNode transform(Token node) throws TransformerException {
        /* an instance of class Token is immutable */
        return transform((KLabel) node);
    }

    @Override
    public ASTNode transform(BoolBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(IntBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(StringBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(GenericToken node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(ListTerminator node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Hole node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        KApp result = node.shallowCopy();
        result.setLabel((Term) node.getLabel().accept(this));
        Term resultChild = (Term) node.getChild().accept(this);
        if (!(resultChild.getSort().equals(KSorts.KLIST) || resultChild instanceof Ambiguity)) {
            result.setChild(new KList(Collections.<Term>singletonList(resultChild)));
        } else {
            result.setChild(resultChild);
        }
        return transform((Term) result);
    }

    @Override
    public ASTNode transform(KItemProjection node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        node = node.shallowCopy();
        node.setTerm(term);
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(KLabel node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(KLabelConstant node) throws TransformerException {
        return transform((KLabel) node);
    }

    @Override
    public ASTNode transform(KLabelInjection node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        node = node.shallowCopy();
        node.setTerm(term);
        return transform((KLabel) node);
    }

    @Override
    public ASTNode transform(Rewrite node) throws TransformerException {
        Rewrite result = node.shallowCopy();
        result.replaceChildren(
                (Term) node.getLeft().accept(this),
                (Term) node.getRight().accept(this),
                context);
        return transform((Term) result);
    }

    @Override
    public ASTNode transform(TermCons node) throws TransformerException {
        for (int i = 0; i < node.getContents().size(); i++) {
            node.getContents().set(i, (Term) node.getContents().get(i).accept(this));
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Bracket node) throws TransformerException {
        node.setContent((Term) node.getContent().accept(this));
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Cast node) throws TransformerException {
        node.setContent((Term) node.getContent().accept(this));
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Freezer node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        Freezer result = node.shallowCopy();
        result.setTerm(term);
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(BackendTerm term) throws TransformerException {
        return transform((Term) term);
    }

    @Override
    public ASTNode transform(Attributes node) throws TransformerException {
        for (int i = 0; i < node.getContents().size(); i++) {
            node.getContents().set(i, (Attribute) node.getContents().get(i).accept(this));
        }
        return node;
    }

    @Override
    public ASTNode transform(Attribute node) throws TransformerException {
        return transform((Attribute) node);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public ASTNode transform(KInjectedLabel node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        KInjectedLabel result = node.shallowCopy();
        result.setTerm(term);
        return transform((Term) result);
    }

    @Override
    public ASTNode transform(FreezerHole node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(FreezerLabel node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        FreezerLabel result = node.shallowCopy();
        result.setTerm(term);
        return transform((Term) result);
    }

    @Override
    public ASTNode transform(StringSentence node) throws TransformerException {
        return node;
    }

    @Override
    public ASTNode transform(Restrictions node) throws TransformerException {
        return node;
    }
}
