package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collection;
import java.util.Collections;


/**
 *
 *
 * @author AndreiS
 */
public class CollectionBuiltin extends DataStructureBuiltin {

    private final Collection<Term> elements;

    public CollectionBuiltin(
            DataStructureSort sort,
            Collection<Term> baseTerms,
            Collection<Term> elements) {
        super(sort, baseTerms);
        this.elements = elements;
    }

    public static CollectionBuiltin of(DataStructureSort sort,
                                       Collection<Term> baseTerms,
                                       Collection<Term> elements) {
        if (sort.type().equals(KSorts.LIST)) {
            return new CollectionBuiltin(sort, baseTerms, elements);
        }
        return new SetBuiltin(sort, baseTerms, elements);
    }

    public Collection<Term> elements() {
        return Collections.unmodifiableCollection(elements);
    }

    @Override
    public boolean isEmpty() {
        return elements.isEmpty() && super.baseTerms.isEmpty();
    }

    @Override
    public Term shallowCopy() {
        return new CollectionBuiltin(dataStructureSort, baseTerms, elements);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + super.hashCode();
        hash = hash * Context.HASH_PRIME + elements.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof CollectionBuiltin)) {
            return false;
        }

        CollectionBuiltin collectionBuiltin = (CollectionBuiltin) object;
        return super.equals(collectionBuiltin) && elements.equals(collectionBuiltin.elements);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

	@Override
	public Term kilToKore() {
		
		KLabel tempLabel = new KLabelConstant("CollectionBuiltin");
		
		java.util.List<Term> tempList = new java.util.ArrayList<Term>();
		tempList.addAll(this.elements);
		tempList.addAll(this.baseTerms);
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = KSequence.adjust((tempList.get(i).kilToKore()));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}
}
