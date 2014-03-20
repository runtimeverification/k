package org.kframework.backend.kore;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KSorts;
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

/*
 * this class will translate List,Set,Map to Builtins
 */
public class ToBuiltinTransformer extends CopyOnWriteTransformer {

    public ToBuiltinTransformer(String name, Context context) {
        super(name, context);
    }
    
    public ToBuiltinTransformer(Context context) {
        super("Transform OLD into NEW", context);
    }
    
    @Override
    public ASTNode transform(ListItem node) throws TransformerException{
        
        ArrayList<Term> temp = new ArrayList<Term>();
        temp.add((Term) node.getItem().accept(this));
        return new ListBuiltin(this.context.dataStructureSortOf(DataStructureSort.DEFAULT_LIST_SORT),
                new ArrayList<Term>(),temp,new ArrayList<Term>());

    }
    
    @Override
    public ASTNode transform(MapItem node) throws TransformerException{
        
        HashMap<Term,Term> temp = new HashMap<Term,Term>();
        temp.put((Term) node.getKey().accept(this), (Term) node.getValue().accept(this));
        
        return new MapBuiltin(this.context.dataStructureSortOf(DataStructureSort.DEFAULT_MAP_SORT),new ArrayList<Term>(),temp);
    }
    
    @Override
    public ASTNode transform(SetItem node) throws TransformerException{
        
        ArrayList<Term> temp = new ArrayList<Term>();
        temp.add((Term) node.getItem().accept(this));
        
        return new SetBuiltin(new DataStructureSort(DataStructureSort.DEFAULT_SET_SORT, KSorts.SET, DataStructureSort.DEFAULT_SET_LABEL, 
                DataStructureSort.DEFAULT_SET_ITEM_LABEL, DataStructureSort.DEFAULT_SET_UNIT_LABEL, new HashMap<String,String>()),new ArrayList<Term>(),temp);
    }

    @Override
    public ASTNode transform(Set node) throws TransformerException{
        
        ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
        ArrayList<Term> elements = new ArrayList<Term>();
        ArrayList<Term> baseTerms = new ArrayList<Term>();
        
        for(int i = 0; i < temp.size(); ++i){
            
            if(temp.get(i) instanceof SetItem){
                elements.add((Term) ((SetItem)temp.get(i)).getItem().accept(this));
            } else {
                baseTerms.add((Term) temp.get(i).accept(this));
            }
        }
        
        return new SetBuiltin(new DataStructureSort(DataStructureSort.DEFAULT_SET_SORT, KSorts.SET, DataStructureSort.DEFAULT_SET_LABEL, 
                DataStructureSort.DEFAULT_SET_ITEM_LABEL, DataStructureSort.DEFAULT_SET_UNIT_LABEL, new HashMap<String,String>()),
                baseTerms,elements);
    }
    
    @Override
    public ASTNode transform(Map node) throws TransformerException{
        
        ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
        HashMap<Term,Term> elements = new HashMap<Term,Term>();
        ArrayList<Term> baseTerms = new ArrayList<Term>();
        
        for(int i = 0;i < temp.size(); ++i){
            
            if(temp.get(i) instanceof MapItem){
                elements.put((Term)((MapItem)temp.get(i)).getKey().accept(this),
                        (Term)((MapItem)temp.get(i)).getValue().accept(this));
            } else {
                baseTerms.add((Term) temp.get(i).accept(this));
            }
        }
        return new MapBuiltin(this.context.dataStructureSortOf(DataStructureSort.DEFAULT_MAP_SORT)
                ,baseTerms,elements);
    }
    
    private int dealWithBaseItem(ArrayList<Term> elementRight,ArrayList<Term> list,int left,int right) throws TransformerException{
        
        int index = left;
        for( ;index <= right; ++index){
            
            if(list.get(index) instanceof ListItem){
                elementRight.add((Term) ((ListItem)list.get(index)).getItem().accept(this));
            } else {
                break;
            }
        }
        return index;
    }
    
    @Override
    public ASTNode transform(List node) throws TransformerException{
        
        ArrayList<Term> temp = new ArrayList<Term>(node.getContents());
        ArrayList<Term> elementLeft = new ArrayList<Term>();
        ArrayList<Term> elementRight = new ArrayList<Term>();
        ArrayList<Term> baseTerms = new ArrayList<Term>();

        int i = 0;
        for( ;i < temp.size(); ++i){
            
            if(temp.get(i) instanceof ListItem){
                elementLeft.add((Term) ((ListItem)temp.get(i)).getItem().accept(this));
            } else {
                break;
            }
        }
        
        int j=temp.size()-1;
        for( ;j >= i; --j){
            
            if(temp.get(j) instanceof ListItem){
                elementRight.add((Term) ((ListItem)temp.get(j)).getItem().accept(this));
            } else {
                break;
            }
        }
        
        while(i<=j){
            
            ArrayList<Term> tempBase = new ArrayList<Term>();
            ArrayList<Term> newRight = new ArrayList<Term>();
            tempBase.add((Term) temp.get(i).accept(this));
            i++;
            i=this.dealWithBaseItem(newRight, temp, i, j);
            baseTerms.add(new ListBuiltin(this.context.dataStructureSortOf(DataStructureSort.DEFAULT_LIST_SORT),
                    tempBase, new ArrayList<Term>(), newRight));
        }
        
        return new ListBuiltin(this.context.dataStructureSortOf(DataStructureSort.DEFAULT_LIST_SORT),
                baseTerms,elementLeft,elementRight);
    }
}
