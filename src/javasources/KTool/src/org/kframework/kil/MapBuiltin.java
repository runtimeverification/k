package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;


/**
 * A builtin map.
 *
 * @author AndreiS
 */
public class MapBuiltin extends DataStructureBuiltin {

    private final Map<Term, Term> elements;

    public MapBuiltin(DataStructureSort sort, Collection<Term> baseTerms, Map<Term, Term> elements) {
        super(sort, baseTerms);
        this.elements = elements;
    }

    public Map<Term, Term> elements() {
        return Collections.unmodifiableMap(elements);
    }

    @Override
    public boolean isEmpty() {
        return elements.isEmpty() && super.baseTerms.isEmpty();
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
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

        if (!(object instanceof MapBuiltin)) {
            return false;
        }

        MapBuiltin mapBuiltin = (MapBuiltin) object;
        return super.equals(mapBuiltin) && elements.equals(mapBuiltin.elements);
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
		
		KLabel tempLabel = new KLabelConstant("MapBuiltin");
		
		java.util.List<Term> tempList = new java.util.ArrayList<Term>();

		for (java.util.Map.Entry<Term, Term> entry : this.elements().entrySet()) {
			
			KSequence keyTerm = KSequence.adjust(entry.getKey().kilToKore());
			KSequence valueTerm = KSequence.adjust(entry.getValue().kilToKore());
			
			ArrayList<Term> newList = new ArrayList<Term>();
			newList.add(keyTerm);
			newList.add(valueTerm);
			tempList.add(KSequence.adjust(new KApp(new KLabelConstant("_|->_"),new KList(newList))));
		}
		
		ArrayList<Term> newList = new ArrayList<Term>(this.baseTerms);
		for(int i=0;i<newList.size();i++){
			
			KSequence elem = KSequence.adjust(newList.get(i).kilToKore());
			tempList.add(elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}

}
