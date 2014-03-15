package org.kframework.kil.visitors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;


public class CopyOnWriteTransformer implements Transformer {
    String name;
    protected Context context;
    protected KompileOptions kompileOptions;

    public CopyOnWriteTransformer(String name, Context context) {
        this.name = name;
        this.context = context;
        this.kompileOptions = context.kompileOptions;
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
        boolean change = false;
        ArrayList<DefinitionItem> items = new ArrayList<DefinitionItem>();
        for (DefinitionItem di : node.getItems()) {
            ASTNode result = di.accept(this);
            if (result != di)
                change = true;
            if (result != null) {
                if (!(result instanceof DefinitionItem)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting DefinitionItem, but got " + result.getClass() + ".", getName(), di
                            .getFilename(), di.getLocation()));
                }
                items.add((DefinitionItem) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setItems(items);
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
        boolean change = false;
        ArrayList<ModuleItem> items = new ArrayList<ModuleItem>();
        for (ModuleItem mi : node.getItems()) {
            ASTNode result = mi.accept(this);
            if (result != mi)
                change = true;
            if (result != null) {
                if (!(result instanceof ModuleItem)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting ModuleItem, but got " + result.getClass() + ".", getName(), mi.getFilename(),
                            mi.getLocation()));
                }
                items.add((ModuleItem) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setItems(items);
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
        boolean change = false;
        Term body = node.getBody();
        ASTNode bodyAST = body.accept(this);
        if (bodyAST != body)
            change = true;
        if (null == bodyAST)
            return null;
        if (!(bodyAST instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + bodyAST.getClass() + ".", getName(), body.getFilename(), body
                    .getLocation()));
        }
        body = (Term) bodyAST;
        Term requires = node.getRequires();
        if (requires != null) {
            ASTNode requiresAST = requires.accept(this);
            if (requiresAST != requires)
                change = true;
            if (null == requiresAST)
                return null;
            if (!(requiresAST instanceof Term)) {
                String msg = "Expecting Term, but got " + requiresAST.getClass() + " while transforming.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, msg, requires
                        .getFilename(), requires.getLocation()));
            }
            requires = (Term) requiresAST;
        }
        Term ensures = node.getEnsures();
        if (ensures != null) {
            ASTNode ensuresAST = ensures.accept(this);
            if (ensuresAST != ensures)
                change = true;
            if (null == ensuresAST)
                return null;
            if (!(ensuresAST instanceof Term)) {
                String msg = "Expecting Term, but got " + ensuresAST.getClass() + " while transforming.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, msg, ensures
                        .getFilename(), ensures.getLocation()));
            }
            ensures = (Term) ensuresAST;
        }
        if (change) {
            node = node.shallowCopy();
            node.setBody(body);
            node.setRequires(requires);
            node.setEnsures(ensures);
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(Configuration node) throws TransformerException {
        return transform((Sentence) node);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
        return transform((Sentence) node);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        return transform((Sentence) node);
    }

    @Override
    public ASTNode transform(Syntax node) throws TransformerException {
        boolean change = false;
        ArrayList<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
        for (PriorityBlock pb : node.getPriorityBlocks()) {
            ASTNode result = pb.accept(this);
            if (result != pb)
                change = true;
            if (result != null) {
                if (!(result instanceof PriorityBlock)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting PriorityBlock, but got " + result.getClass() + " while transforming.",
                            getName(), pb.getFilename(), pb.getLocation()));
                }
                pbs.add((PriorityBlock) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setPriorityBlocks(pbs);
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityExtended node) throws TransformerException {
        boolean change = false;
        ArrayList<PriorityBlockExtended> pbs = new ArrayList<PriorityBlockExtended>();
        for (PriorityBlockExtended pb : node.getPriorityBlocks()) {
            ASTNode result = pb.accept(this);
            if (result != pb)
                change = true;
            if (result != null) {
                if (!(result instanceof PriorityBlockExtended)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting PriorityBlock, but got " + result.getClass() + " while transforming.",
                            getName(), pb.getFilename(), pb.getLocation()));
                }
                pbs.add((PriorityBlockExtended) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setPriorityBlocks(pbs);
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException {
        boolean change = false;
        ArrayList<KLabelConstant> pbs = new ArrayList<KLabelConstant>();
        for (KLabelConstant pb : node.getTags()) {
            ASTNode result = pb.accept(this);
            if (result != pb)
                change = true;
            if (result != null) {
                if (!(result instanceof KLabelConstant)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Constant, but got " + result.getClass() + " while transforming.", getName(),
                            pb.getFilename(), pb.getLocation()));
                }
                pbs.add((KLabelConstant) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setTags(pbs);
        }
        return transform((ModuleItem) node);
    }

    @Override
    public ASTNode transform(PriorityBlock node) throws TransformerException {
        boolean change = false;
        ArrayList<Production> prods = new ArrayList<Production>();
        for (Production p : node.getProductions()) {
            ASTNode result = p.accept(this);
            if (result != p)
                change = true;
            if (result != null) {
                if (!(result instanceof Production)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Production, but got " + result.getClass() + ".", getName(), p.getFilename(), p
                            .getLocation()));
                }
                prods.add((Production) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setProductions(prods);
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(PriorityBlockExtended node) throws TransformerException {
        boolean change = false;
        ArrayList<KLabelConstant> prods = new ArrayList<KLabelConstant>();
        for (KLabelConstant p : node.getProductions()) {
            ASTNode result = p.accept(this);
            if (result != p)
                change = true;
            if (result != null) {
                if (!(result instanceof KLabelConstant)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Constant, but got " + result.getClass() + ".", getName(), p.getFilename(), p
                            .getLocation()));
                }
                prods.add((KLabelConstant) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setProductions(prods);
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Production node) throws TransformerException {
        boolean change = false;
        ArrayList<ProductionItem> pis = new ArrayList<ProductionItem>();
        for (ProductionItem pi : node.getItems()) {
            ASTNode result = pi.accept(this);
            if (result != pi)
                change = true;
            if (result != null) {
                if (!(result instanceof ProductionItem)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Production, but got " + result.getClass() + ".", getName(), pi.getFilename(),
                            pi.getLocation()));
                }
                pis.add((ProductionItem) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setItems(pis);
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
        Term term = node.getContents();
        ASTNode result = term.accept(this);
        if (result == null) {
            result = MetaK.defaultTerm(term, context);
        }
        if (!(result instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (result != term) {
            node = node.shallowCopy();
            node.setContents((Term) result);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Collection node) throws TransformerException {
        boolean change = false;
        ArrayList<Term> terms = new ArrayList<Term>();
        for (Term t : node.getContents()) {
            ASTNode result = t.accept(this);
            if (result != t)
                change = true;
            if (result != null) {
                if (!(result instanceof Term)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), t.getFilename(), t
                            .getLocation()));
                }
                terms.add((Term) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setContents(terms);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Ambiguity node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(Bag node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(KSequence node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(List node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(KList node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(Map node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(Set node) throws TransformerException {
        return transform((Collection) node);
    }

    @Override
    public ASTNode transform(CollectionItem node) throws TransformerException {
        Term term = node.getItem();
        ASTNode result = term.accept(this);
        if (result == null)
            return null;
        if (!(result instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (result != term) {
            node = node.shallowCopy();
            node.setItem((Term) result);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(BagItem node) throws TransformerException {
        return transform((CollectionItem) node);
    }

    @Override
    public ASTNode transform(ListItem node) throws TransformerException {
        return transform((CollectionItem) node);
    }

    @Override
    public ASTNode transform(MapItem node) throws TransformerException {
        boolean change = false;
        Term term = node.getKey();
        ASTNode key = term.accept(this);
        if (key == null)
            return null;
        if (!(key instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + key.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (key != term) {
            change = true;
        }
        term = node.getValue();
        ASTNode value = term.accept(this);
        if (value == null)
            return null;
        if (!(value instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + value.getClass() + " while transforming.", term.getFilename(), term
                    .getLocation()));
        }
        if (value != term) {
            change = true;
        }
        if (change) {
            node = node.shallowCopy();
            node.setKey((Term) key);
            node.setValue((Term) value);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(SetItem node) throws TransformerException {
        return transform((CollectionItem) node);
    }

    @Override
    public ASTNode transform(CollectionBuiltin node) throws TransformerException {
        boolean change = false;

        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
            change = change || transformedTerm != term;
        }

        ArrayList<Term> elements = new ArrayList<Term>(node.elements().size());
        for (Term term : node.elements()) {
            Term transformedTerm = (Term) term.accept(this);
            elements.add(transformedTerm);
            change = change || transformedTerm != term;
        }

        if (change) {
            return CollectionBuiltin.of(node.sort(), terms, elements);
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(SetBuiltin node) throws TransformerException {
       return transform((CollectionBuiltin)node);
    }

    @Override
    public ASTNode transform(SetLookup node) throws TransformerException {
        Variable set = (Variable) node.base().accept(this);
        Term value = (Term) node.key().accept(this);

        if (set != node.base() || value != node.key()) {
            return new SetLookup(set, value, node.choice());
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(SetUpdate node) throws TransformerException {
        boolean change = false;

        Variable set = (Variable) node.set().accept(this);

        HashSet<Term> removeEntries = new HashSet<Term>(node.removeEntries().size());
        for (Term term : node.removeEntries()) {
            Term transformedTerm = (Term) term.accept(this);
            removeEntries.add(transformedTerm);
            change = change || transformedTerm != term;
        }

        if (change) {
            return new SetUpdate(set, removeEntries);
        } else {
            return node;
        }
    }


    @Override
    public ASTNode transform(ListBuiltin node) throws TransformerException {
        boolean change = false;

        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
            change = change || transformedTerm != term;
        }

        ArrayList<Term> elementsLeft = new ArrayList<Term>(node.elementsLeft().size());
        for (Term entry : node.elementsLeft()) {
            Term transformedEntry = (Term) entry.accept(this);
            elementsLeft.add(transformedEntry);
            change = change || transformedEntry != entry;
        }

        ArrayList<Term> elementsRight = new ArrayList<Term>(node.elementsRight().size());
        for (Term entry : node.elementsRight()) {
            Term transformedEntry = (Term) entry.accept(this);
            elementsRight.add(transformedEntry);
            change = change || transformedEntry != entry;
        }

        if (change) {
            return ListBuiltin.of(node.sort(), elementsLeft, elementsRight, terms);
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(ListLookup node) throws TransformerException {
        Variable base = (Variable) node.base().accept(this);
        Term key = (Term) node.key().accept(this);
        Term value = (Term) node.value().accept(this);

        if (base != node.base() || key != node.key() || value != node.value()) {
            return new ListLookup(base, key, value, node.kind());
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(ListUpdate node) throws TransformerException {
        boolean change = false;

        Variable base = (Variable) node.base().accept(this);

        ArrayList<Term> removeLeft = new ArrayList<Term>(node.removeLeft().size());
        for (Term entry : node.removeLeft()) {
            Term transformedEntry = (Term) entry.accept(this);
            removeLeft.add(transformedEntry);
            change = change || transformedEntry != entry;
        }

        ArrayList<Term> removeRight = new ArrayList<Term>(node.removeRight().size());
        for (Term entry : node.removeRight()) {
            Term transformedEntry = (Term) entry.accept(this);
            removeRight.add(transformedEntry);
            change = change || transformedEntry != entry;
        }

        if (change) {
            return new ListUpdate(base, removeLeft, removeRight);
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(MapBuiltin node) throws TransformerException {
        boolean change = false;

        ArrayList<Term> terms = new ArrayList<Term>(node.baseTerms().size());
        for (Term term : node.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            terms.add(transformedTerm);
            change = change || transformedTerm != term;
        }

        HashMap<Term, Term> elements = new HashMap<Term, Term>(node.elements().size());
        for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            elements.put(transformedKey, transformedValue);
            change = change || transformedKey != entry.getKey()
                     || transformedValue != entry.getValue();
        }

        if (change) {
            return new MapBuiltin(node.sort(), terms, elements);
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(MapLookup node) throws TransformerException {
        Variable map = (Variable) node.base().accept(this);
        Term key = (Term) node.key().accept(this);
        Term value = (Term) node.value().accept(this);

        if (map != node.base() || key != node.key() || value != node.value()) {
            return new MapLookup(map, key, value, node.kind(), node.choice());
        } else {
            return node;
        }
    }

    @Override
    public ASTNode transform(MapUpdate node) throws TransformerException {
        boolean change = false;

        Variable map = (Variable) node.map().accept(this);

        HashMap<Term, Term> removeEntries = new HashMap<Term, Term>(node.removeEntries().size());
        for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            removeEntries.put(transformedKey, transformedValue);
            change = change || transformedKey != entry.getKey()
                     || transformedValue != entry.getValue();
        }

        HashMap<Term, Term> updateEntries = new HashMap<Term, Term>(node.updateEntries().size());
        for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
            Term transformedKey = (Term) entry.getKey().accept(this);
            Term transformedValue = (Term) entry.getValue().accept(this);
            updateEntries.put(transformedKey, transformedValue);
            change = change || transformedKey != entry.getKey()
                     || transformedValue != entry.getValue();
        }

        if (change) {
            return new MapUpdate(map, removeEntries, updateEntries);
        } else {
            return node;
        }
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
        boolean change = false;
        Term term = node.getLabel();
        ASTNode label = term.accept(this);
        if (label == null)
            return null;
        if (!(label instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + label.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (label != term) {
            change = true;
        }
        term = node.getChild();
        ASTNode child = term.accept(this);
        if (child == null)
            return null;
        if (!(child instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + child.getClass() + " while transforming.", term.getFilename(), term
                    .getLocation()));
        }
        if (child != term) {
            change = true;
        }
        if (change) {
            node = node.shallowCopy();
            node.setLabel((Term) label);
            Term childTerm = (Term) child;
            if (!(childTerm.getSort().equals(KSorts.KLIST) || childTerm instanceof Ambiguity)) {
                node.setChild(new KList(Collections.<Term>singletonList(childTerm)));
            } else {
                node.setChild(childTerm);
            }

        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(KItemProjection node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        if (term != node.getTerm()) {
            node = node.shallowCopy();
            node.setTerm(term);
        }
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
        if (term != node.getTerm()) {
            node = node.shallowCopy();
            node.setTerm(term);
        }
        return transform((KLabel) node);
    }

    @Override
    public ASTNode transform(Rewrite node) throws TransformerException {
        boolean change = false;
        Term term = node.getLeft();
        ASTNode left = term.accept(this);
        if (left == null)
            return null;
        if (!(left instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + left.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (left != term) {
            change = true;
        }
        term = node.getRight();
        ASTNode right = term.accept(this);
        if (right == null)
            return null;
        if (!(right instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + right.getClass() + " while transforming.", term.getFilename(), term
                    .getLocation()));
        }
        if (right != term) {
            change = true;
        }
        if (change) {
            node = node.shallowCopy();
            node.replaceChildren((Term) left, (Term) right, context);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(TermCons node) throws TransformerException {
        boolean change = false;
        ArrayList<Term> terms = new ArrayList<Term>();
        for (Term t : node.getContents()) {
            ASTNode result = t.accept(this);
            if (result != t)
                change = true;
            if (result != null) {
                if (!(result instanceof Term)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), t.getFilename(), t
                            .getLocation()));
                }
                terms.add((Term) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setContents(terms);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Bracket node) throws TransformerException {
        Term term = node.getContent();
        ASTNode result = term.accept(this);
        if (result == null)
            return null;
        if (!(result instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (result != term) {
            node = node.shallowCopy();
            node.setContent((Term) result);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Cast node) throws TransformerException {
        Term term = node.getContent();
        ASTNode result = term.accept(this);
        if (result == null)
            return null;
        if (!(result instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (result != term) {
            node = node.shallowCopy();
            node.setContent((Term) result);
        }
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Freezer node) throws TransformerException {
        Term term = node.getTerm();
        ASTNode result = term.accept(this);
        if (result == null)
            return null;
        if (!(result instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + result.getClass() + ".", getName(), term.getFilename(), term
                    .getLocation()));
        }
        if (result != term) {
            node = node.shallowCopy();
            node.setTerm((Term) result);
        }

        return transform((Term) node);
    }

    @Override
    public ASTNode transform(BackendTerm term) throws TransformerException {
        return transform((Term) term);
    }

    @Override
    public ASTNode transform(Attributes node) throws TransformerException {
        boolean change = false;
        java.util.List<Attribute> contents = new ArrayList<Attribute>();
        for (Attribute at : node.getContents()) {
            ASTNode result = at.accept(this);
            if (result != at)
                change = true;
            if (result != null) {
                if (!(result instanceof Attribute)) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Attribute, but got " + result.getClass() + " while transforming.", getName(),
                            at.getFilename(), at.getLocation()));
                }
                contents.add((Attribute) result);
            }
        }
        if (change) {
            node = node.shallowCopy();
            node.setContents(contents);
        }
        return transform((ASTNode) node);
    }

    @Override
    public ASTNode transform(Attribute node) throws TransformerException {
        return transform((ASTNode) node);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public ASTNode transform(KInjectedLabel node) throws TransformerException {
        boolean change = false;
        Term body = node.getTerm();
        ASTNode bodyAST = body.accept(this);
        if (bodyAST != body)
            change = true;
        if (null == bodyAST)
            return null;
        if (!(bodyAST instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + bodyAST.getClass() + ".", getName(), body.getFilename(), body
                    .getLocation()));
        }
        body = (Term) bodyAST;
        if (change) {
            node = node.shallowCopy();
            node.setTerm(body);
        }
        return node;
    }

    @Override
    public ASTNode transform(FreezerLabel node) throws TransformerException {
        boolean change = false;
        Term body = node.getTerm();
        ASTNode bodyAST = body.accept(this);
        if (bodyAST != body)
            change = true;
        if (null == bodyAST)
            return null;
        if (!(bodyAST instanceof Term)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Expecting Term, but got " + bodyAST.getClass() + ".", getName(), body.getFilename(), body
                    .getLocation()));
        }
        body = (Term) bodyAST;
        if (change) {
            node = node.shallowCopy();
            node.setTerm(body);
        }
        return node;
    }

    @Override
    public ASTNode transform(FreezerHole node) throws TransformerException {
        return transform((Term) node);
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
