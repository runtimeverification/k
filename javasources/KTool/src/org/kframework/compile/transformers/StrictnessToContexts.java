package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Context;
import org.kframework.kil.Hole;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.TermCons;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class StrictnessToContexts extends CopyOnWriteTransformer {

	private List<ModuleItem> items = new ArrayList<ModuleItem>();

	public StrictnessToContexts() {
		super("Strict Ops To Context");
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		
		//collect the productions which have the attributes strict and seqstrict
		List<Production> prods = GetSyntaxByTag.applyVisitor(node, "strict");
		prods.addAll(GetSyntaxByTag.applyVisitor(node, "seqstrict"));
		if (prods.isEmpty())
			return node;

		items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();

		String arg, attr;

		for (Production prod : prods) {
			
			if(prod.isSubsort()) continue;
						
			//set the attribute: strict or seqstrict
			//arg: arguments of the attribute, e.g. (1) 
			attr = "strict";
			arg = prod.getAttribute(attr);

			if(arg == null){
				attr = "seqstrict";
				arg = prod.getAttribute(attr);
				
				if(arg == null) continue;
			}

			//strict in only one argument
			if(!arg.equalsIgnoreCase("") && arg.indexOf(",") == -1){
				strictInOne(attr, prod, arg);

				//strict in all arguments
			}else if(arg.equalsIgnoreCase("")){
				strictInAll(attr, prod);

				//strict in more than one arguments
			}else{
				strictInMore(attr, prod, arg);
			}

			//remove strictness after adding contexts
			prod.getAttributes().remove(attr);
		}
		
		node.setItems(items);

		return node;
	}


	private void strictInMore(String attr, Production prod, String arg) {

		int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

		//case: (1,) or (,)
		if(arg.endsWith(",")){
			String msg ="Make sure the given argument is correct (" + arg + ")";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
		}

		String[] s = arg.split("[,]+");

		for (int i = 0; i < s.length; i++) {
			s[i] = s[i].trim();

			//case: (,2)
			if(s[i].equalsIgnoreCase("")){
				String msg ="Wrong argument (" + arg + ") given to strict attribute";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
			}

			//case: strict(1,3) when there are only 2 terms
			if(Integer.parseInt(s[i]) > size){
				String msg ="Production does not have this (" + Integer.parseInt(s[i]) + ") many terms";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
			}

		}

		int co = 0, i = 0;

		while(co < s.length){
			TermCons tc = (TermCons) MetaK.getTerm(prod);

			while(i < size){

				if(i == Integer.parseInt(s[co])-1){
					//insert HOLE instead of the term
					tc.getContents().set(i, new Hole("K"));

					if(attr.equalsIgnoreCase("seqstrict") && co > 0){
						for (int j = 0; j < co; j++) {
							//the terms listed in the argument before the current one should be KResults
							tc.getContents().get(Integer.parseInt(s[j])-1).setSort("KResult");
						}
					}
				}else
					//the others are fresh variables (anonymous) of sort K
					tc.getContents().set(i, MetaK.getFreshVar("K"));


				i++;
			}

			Context ctx = new Context();
			ctx.setBody(tc);

			items.add(ctx);

			co++;
			i = 0;
		}
	}

	private void strictInOne(String attr, Production prod, String arg) {

		int argi = 0;

		try{
			//if terms are listed without commas in between
			argi = Integer.parseInt(arg);
		}catch(NumberFormatException nfe){

			//case: (1 2)
			String msg = "Wrong argument (" + arg + ") given to strict attribute. Make sure arguments are separated by a comma.";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
		}

		int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

		//case: strict(3) when there are only 2 terms
		if(argi > size){
			String msg ="Production does not have this (" + argi + ") many terms";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
		}

		int co = 0;

		TermCons tc = (TermCons) MetaK.getTerm(prod);

		while(co < size){
			if(co == argi-1){
				//insert HOLE instead of the term
				tc.getContents().set(co, new Hole("K"));
			}
			else{
				//the others are fresh variables (anonymous) of sort K
				tc.getContents().set(co, MetaK.getFreshVar("K"));
			}
			co++;
		}

		Context ctx = new Context();
		ctx.setBody(tc);

		items.add(ctx);
	}


	private void strictInAll(String attr, Production prod){

		int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

		int co = 0, i = 0;

		while(co < size){
			TermCons tc = (TermCons) MetaK.getTerm(prod);

			while(i < size){

				if(i == co){
					//insert HOLE instead of the term
					tc.getContents().set(i, new Hole("K"));

					if(attr.equalsIgnoreCase("seqstrict")){
						//previous terms should be KResults
						for (int j = 0; j < i; j++) {
							tc.getContents().get(j).setSort("KResult");
						}
					}
				}else
					//the others are fresh variables (anonymous) of sort K
					tc.getContents().set(i, MetaK.getFreshVar("K"));

				i++;

			}

			Context ctx = new Context();
			ctx.setBody(tc);

			items.add(ctx);

			i = 0;
			co++;
		}
	}
}
