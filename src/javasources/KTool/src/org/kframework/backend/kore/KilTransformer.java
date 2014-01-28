package org.kframework.backend.kore;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ColorSetting;


public class KilTransformer {
	
	ToBuiltinTransformer builtinTrans;
	ToKAppTransformer kappTrans;
	KoreFilter koreTrans;
	
	public KilTransformer(Context context){
		
	    koreTrans = new KoreFilter(context);
	    builtinTrans = new ToBuiltinTransformer(context);
	    kappTrans = new ToKAppTransformer(context);

	}
	
	public KilTransformer(boolean inConfiguration, ColorSetting color, boolean addParentheses, org.kframework.kil.loader.Context context){
		
	    koreTrans = new KoreFilter(inConfiguration, color, addParentheses, context);
	    builtinTrans = new ToBuiltinTransformer(context);
	    kappTrans = new ToKAppTransformer(context);

	}
	
	public String kilToKore(ASTNode node){

	    try {
			node.accept(builtinTrans).accept(kappTrans).accept(koreTrans);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    return "\n\n+++KORE+++\n"+koreTrans.getResult();
	}
}
