// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;

import org.kframework.backend.unparser.UnparserFilterNew;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListLookup;
import org.kframework.kil.ListUpdate;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapLookup;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.SetLookup;
import org.kframework.kil.SetUpdate;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import com.davekoelle.AlphanumComparator;

/*
 * 
 * this Class will translate kil components to KLabel Form
 * 
 */
public class ToKAppTransformer extends CopyOnWriteTransformer {

    public ToKAppTransformer(String name, Context context) {
        super(name, context);
    }
    
    public ToKAppTransformer(Context context) {
        super("Transform NEW into KAPP", context);
    }
    
    @Override
    public ASTNode visit(SetLookup node, Void _) {
        
        ArrayList<Term> temp = new ArrayList<Term>();
        temp.add((Term) this.visitNode(node.base()));
        temp.add((Term) this.visitNode(node.key()));
        temp.add((Term) this.visitNode(node.value()));
        
        return new KApp(new KLabelConstant("Set:lookup"),new KList(temp));
    }
    
    @Override
    public ASTNode visit(ListLookup node, Void _) {
        
        ArrayList<Term> temp = new ArrayList<Term>();
        temp.add((Term) this.visitNode(node.base()));
        temp.add((Term) this.visitNode(node.key()));
        temp.add((Term) this.visitNode(node.value()));
        
        return new KApp(new KLabelConstant("List:lookup"),new KList(temp));
    }
    
    @Override
    public ASTNode visit(MapLookup node, Void _) {
        
        ArrayList<Term> temp = new ArrayList<Term>();
        temp.add((Term) this.visitNode(node.base()));
        temp.add((Term) this.visitNode(node.key()));
        temp.add((Term) this.visitNode(node.value()));
        
        return new KApp(new KLabelConstant("Map:lookup"),new KList(temp));
    }
    
    @Override
    public ASTNode visit(SetUpdate node, Void _) {
        
        ArrayList<Term> temp = new ArrayList<Term>(node.removeEntries());
        for(int i = 0; i < temp.size(); ++i){
            
            temp.set(i,(Term) this.visitNode(temp.get(i)));
        }                
        KList newTerm = new KList(temp);
        
        ArrayList<Term> termSeq = new ArrayList<Term>();
        termSeq.add(newTerm);
        KSequence newEntryTerm = new KSequence(termSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) this.visitNode(node.set()));
        newArg.add(newEntryTerm);
        
        return new KApp(new KLabelConstant("Set:update"),new KList(newArg));
    }
    
    @Override
    public ASTNode visit(ListUpdate node, Void _) {
        
        ArrayList<Term> tempLeft = new ArrayList<Term>(node.removeLeft());
        for(int i = 0; i < tempLeft.size(); ++i){
            
            tempLeft.set(i,(Term) this.visitNode(tempLeft.get(i)));
        }
        
        ArrayList<Term> tempRight = new ArrayList<Term>(node.removeRight());
        for(int i = 0; i < tempRight.size(); ++i){
            
            tempRight.set(i,(Term) this.visitNode(tempRight.get(i)));
        }
    
        KList newLeftList = new KList(tempLeft);
        
        KList newRightList = new KList(tempRight);
        
        ArrayList<Term> newLeftSeq = new ArrayList<Term>();
        newLeftSeq.add(newLeftList);
        ArrayList<Term> newRightSeq = new ArrayList<Term>();
        newRightSeq.add(newRightList);
        KSequence newLeftTerm = new KSequence(newLeftSeq);
        KSequence newRightTerm = new KSequence(newRightSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) this.visitNode(node.base()));
        newArg.add(newLeftTerm);
        newArg.add(newRightTerm);
        
        return new KApp(new KLabelConstant("List:update"),new KList(newArg));
    }
    
    @Override
    public ASTNode visit(MapUpdate node, Void _) {
        
        
        HashMap<Term,Term> removeMap = new HashMap<Term,Term>(node.removeEntries());
        ArrayList<Term> removeList = new ArrayList<Term>();
        
        for (java.util.Map.Entry<Term, Term> entry : removeMap.entrySet()) {
            
            ArrayList<Term> tempList = new ArrayList<Term>();
            tempList.add((Term) this.visitNode(entry.getKey()));
            tempList.add((Term) this.visitNode(entry.getValue()));

            KApp temp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_ITEM_LABEL),new KList(tempList));
            removeList.add(temp);
        }
        
        HashMap<Term,Term> updateMap = new HashMap<Term,Term>(node.updateEntries());
        ArrayList<Term> updateList = new ArrayList<Term>();
        
        for (java.util.Map.Entry<Term, Term> entry : updateMap.entrySet()) {
            
            ArrayList<Term> tempList = new ArrayList<Term>();
            tempList.add((Term) this.visitNode(entry.getKey()));
            tempList.add((Term) this.visitNode(entry.getValue()));

            KApp temp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_ITEM_LABEL),new KList(tempList));
            updateList.add(temp);
        }
    
        KList newLeftList = new KList(removeList);
        
        KList newRightList = new KList(updateList);
        
        ArrayList<Term> newLeftSeq = new ArrayList<Term>();
        newLeftSeq.add(newLeftList);
        ArrayList<Term> newRightSeq = new ArrayList<Term>();
        newRightSeq.add(newRightList);
        KSequence newLeftTerm = new KSequence(newLeftSeq);
        KSequence newRightTerm = new KSequence(newRightSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) this.visitNode(node.map()));
        newArg.add(newLeftTerm);
        newArg.add(newRightTerm);
        
        return new KApp(new KLabelConstant("Map:update"),new KList(newArg));
    }
    
    @Override
    public ASTNode visit(SetBuiltin node, Void _) {
        return ((SetBuiltin)super.visit(node, _)).toKApp(context);
    }
    
    @Override
    public ASTNode visit(ListBuiltin node, Void _) {
        return ((ListBuiltin)super.visit(node, _)).toKApp(context);
    }
    
    @Override
    public ASTNode visit(MapBuiltin node, Void _) {
        return ((MapBuiltin)super.visit(node, _)).toKApp(context);
    }
    
}
