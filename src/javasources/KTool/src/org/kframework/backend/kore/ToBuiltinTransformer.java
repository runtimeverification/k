package org.kframework.backend.kore;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.kil.ASTNode;
import org.kframework.kil.BagItem;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.List;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapItem;
import org.kframework.kil.Set;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ToBuiltinTransformer extends CopyOnWriteTransformer {

	public ToBuiltinTransformer(String name, Context context) {
		super(name, context);
	}
	
	@Override
	public ASTNode transform(ListItem node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>();
		temp.add((Term) node.getItem().accept(this));
		
		return new ListBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT),
				new ArrayList<Term>(),temp,new ArrayList<Term>());

	}
	
	@Override
	public ASTNode transform(MapItem node) throws TransformerException{
		
		HashMap<Term,Term> temp = new HashMap<Term,Term>();
		temp.put((Term) node.getKey().accept(this), (Term) node.getValue().accept(this));
		
		return new MapBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_MAP_SORT),new ArrayList<Term>(),temp);
	}
	
	@Override
	public ASTNode transform(SetItem node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>();
		temp.add((Term) node.getItem().accept(this));
		
		return new SetBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_SET_SORT),new ArrayList<Term>(),temp);
	}

	@Override
	public ASTNode transform(Set node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
		SetBuiltin result = new SetBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_SET_SORT),new ArrayList<Term>(),new ArrayList<Term>());
		
		for(int i = 0; i < temp.size(); ++i){
			
			if(temp.get(i) instanceof SetItem){
				result.elements().add((Term) ((SetItem)temp.get(i)).getItem().accept(this));
			} else {
				result.baseTerms().add((Term) temp.get(i).accept(this));
			}
		}
		return result;
	}
	
	@Override
	public ASTNode transform(Map node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
		MapBuiltin result = new MapBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_MAP_SORT)
				,new ArrayList<Term>(),new HashMap<Term,Term>());
		
		for(int i = 0;i < temp.size(); ++i){
			
			if(temp.get(i) instanceof MapItem){
				result.elements().put((Term)((MapItem)temp.get(i)).getKey().accept(this),
						(Term)((MapItem)temp.get(i)).getValue().accept(this));
			} else {
				result.baseTerms().add((Term) temp.get(i).accept(this));
			}
		}
		return result;
	}
	
	private int dealWithBaseItem(ListBuiltin result,ArrayList<Term> list,int left,int right) throws TransformerException{
		
		int index = left;
		for( ;index <= right; ++index){
			
			if(list.get(index) instanceof ListItem){
				result.elementsRight().add((Term) ((ListItem)list.get(index)).getItem().accept(this));
			} else {
				break;
			}
		}
		return index;
	}
	
	@Override
	public ASTNode transform(List node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
		ListBuiltin result = new ListBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT),
				new ArrayList<Term>(),new ArrayList<Term>(),new ArrayList<Term>());
		
		int i = 0;
		for( ;i < temp.size(); ++i){
			
			if(temp.get(i) instanceof ListItem){
				result.elementsLeft().add((Term) ((ListItem)temp.get(i)).getItem().accept(this));
			} else {
				break;
			}
		}
		
		int j=temp.size()-1;
		for( ;j >= i; --j){
			
			if(temp.get(j) instanceof ListItem){
				result.elementsRight().add((Term) ((ListItem)temp.get(i)).getItem().accept(this));
			} else {
				break;
			}
		}
		
		while(i<=j){
			
			ArrayList<Term> tempBase = new ArrayList<Term>();
			tempBase.add((Term) temp.get(i).accept(this));
			i++;
			ListBuiltin newAdd = new ListBuiltin(this.context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT),
					tempBase, new ArrayList<Term>(), new ArrayList<Term>());
			i=this.dealWithBaseItem(newAdd, temp, i, j);
			result.baseTerms().add(newAdd);
		}
		
		return result;
	}
}
