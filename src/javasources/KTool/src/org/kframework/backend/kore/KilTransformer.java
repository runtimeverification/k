// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ColorSetting;


public class KilTransformer {
    
    FlattenSyntax kilTermCons;
    ToKAppTransformer kappTrans;
    KoreFilter koreTrans;
    
    public KilTransformer(Context context){
        
        koreTrans = new KoreFilter(context);
        kappTrans = new ToKAppTransformer(context);

    }
    
    public KilTransformer(boolean inConfiguration, ColorSetting color, org.kframework.kil.loader.Context context){
        
        koreTrans = new KoreFilter(inConfiguration, color, context);
        kappTrans = new ToKAppTransformer(context);

    }
    
    public String kilToKore(ASTNode node){

        node = kappTrans.visitNode(node);
        koreTrans.visitNode(node);
        return koreTrans.getResult();
    }
}
