package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
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

	private List<ModuleItem> items;

	public StrictnessToContexts() {
		super("Strict Ops To Context");
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {

//		List<ModuleItem> contexts = node.getItems();
//
//		for (int i = 0; i < contexts.size(); i++) {
//			System.out.println(contexts.get(i));
//		}

		//collect productions that are strict or seqstrict
		List<Production> prods = GetSyntaxByTag.applyVisitor(node, "strict");
		prods.addAll(GetSyntaxByTag.applyVisitor(node, "seqstrict"));

//		System.out.println("------------------");	

		if (prods.isEmpty()) return node;
		items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();

		String arg, attr = "";

		for (Production prod : prods) {

			//			System.out.println(prod.toString());

			Attributes attributes = prod.getAttributes();

			if (attributes.containsKey("strict")){
				attr = "strict";
			}else if(attributes.containsKey("seqstrict")){
				attr = "seqstrict";
			}else continue;

			arg = attributes.get(attr);
			//			System.out.println(attr + ": " + arg);

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

			prod.getAttributes().remove(attr);
		}

		node.setItems(items);	

//		contexts = node.getItems();
//
//		for (int i = 0; i < contexts.size(); i++) {
//			System.out.println(contexts.get(i));
//		}

		return node;
	}


	private void strictInMore(String attr, Production prod, String arg) {
		//		ArrayList<Integer> seqargs = new ArrayList<Integer>();

		int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

		//		System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

		//case: (1,) or (,)
		if(arg.endsWith(",")){
			String msg ="Make sure the given argument is correct (" + arg + ")";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
		}

		String[] s = arg.split("[,]+");

		for (int i = 0; i < s.length; i++) {
			s[i] = s[i].trim();

			//			System.out.println("trim" + s[i] + "trim");

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

			//			if(attr.equalsIgnoreCase("seqstrict"))
			//				seqargs.add(Integer.parseInt(s[i]));
		}

		//		for (int i = 0; i < s.length; i++) {
		//			System.out.println("s"+i+": " + s[i]);
		//		}

		int co = 0, i = 0;

		while(co < s.length){
			TermCons tc = (TermCons) MetaK.getTerm(prod);

			while(i < size){

				if(i == Integer.parseInt(s[co])-1){
					//					System.out.println("i: " + i + " s[co]: " + s[co]);
					tc.getContents().set(i, new Hole("K"));

					if(attr.equalsIgnoreCase("seqstrict") && co > 0){
						for (int j = 0; j < co; j++) {
							//							tc.getContents().set(seqargs.get(j), MetaK.getFreshVar("KResult"));
							tc.getContents().get(Integer.parseInt(s[j])-1).setSort("KResult");
						}
					}
				}else
					tc.getContents().set(i, MetaK.getFreshVar(tc.getContents().get(i).getSort()));


				i++;
			}

			Context ctx = new Context();
			ctx.setBody(tc);

			//			System.out.println(ctx.toString());

			items.add(ctx);

			co++;
			i = 0;
		}
	}

	private void strictInOne(String attr, Production prod, String arg) {

		int argi = 0;

		try{
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

		//		System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

		int co = 0;

		TermCons tc = (TermCons) MetaK.getTerm(prod);

		while(co < size){
			if(co == argi-1){
				tc.getContents().set(co, new Hole("K"));
			}
			else{
				tc.getContents().set(co, MetaK.getFreshVar(tc.getContents().get(co).getSort()));
			}
			co++;
		}

		Context ctx = new Context();
		ctx.setBody(tc);

		//		System.out.println(ctx.toString());

		items.add(ctx);
	}


	private void strictInAll(String attr, Production prod){

		int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

		//		System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

		int co = 0, i = 0;

		while(co < size){
			TermCons tc = (TermCons) MetaK.getTerm(prod);

			while(i < size){

				if(i == co){
					tc.getContents().set(i, new Hole("K"));

					if(attr.equalsIgnoreCase("seqstrict")){

						for (int j = 0; j < i; j++) {
							//								tc.getContents().set(seqargs.get(j), MetaK.getFreshVar("KResult"));
							tc.getContents().get(j).setSort("KResult");
						}
					}
				}else
					tc.getContents().set(i, MetaK.getFreshVar(tc.getContents().get(i).getSort()));

				i++;

			}

			Context ctx = new Context();
			ctx.setBody(tc);

			//			System.out.println(ctx.toString());

			items.add(ctx);

			i = 0;
			co++;
		}
	}
}
