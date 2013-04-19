package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Context;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSort;
import org.kframework.kil.KList;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
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
		Set<Production> prods = SyntaxByTag.get(node, "strict");
		prods.addAll(SyntaxByTag.get(node, "seqstrict"));
		if (prods.isEmpty())
			return node;

		items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();

		String arg, attr;

		for (Production prod : prods) {
		

			if(prod.getSort().equalsIgnoreCase("KLabel")) {
        attr = "strict";
        if(prod.getAttribute(attr) != null){
          kLabelStrict(attr, prod);
          continue;
        }
        attr = "seqstrict";
        if(prod.getAttribute(attr) != null) {
          kLabelSeqStrict(attr, prod);
          continue;
        } 
        assert false : "KLabel " + prod + " is neither strict nor seqstrict," 
                     + "  how did we get here?";
      }


			if(prod.isSubsort()){
				String msg ="Production is a subsort and cannot be strict.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
			}
			
			if(prod.isConstant()){
				String msg ="Production is a constant and cannot be strict.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), prod.getFilename(), prod.getLocation()));
			}
			
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
					tc.getContents().set(i, new Hole(KSort.getKSort(tc.getContents().get(i).getSort()).toString()));

					if(attr.equalsIgnoreCase("seqstrict") && co > 0){
						for (int j = 0; j < co; j++) {
							//the terms listed in the argument before the current one should be KResults
							tc.getContents().get(Integer.parseInt(s[j])-1).setSort("KResult");
						}
					}
				}else{
					//the others are fresh variables (anonymous) of sort K
					tc.getContents().set(i, MetaK.getFreshVar(KSort.getKSort(tc.getContents().get(i).getSort()).toString()));
				}


				i++;
			}

			Context ctx = new Context();
			ctx.setBody(tc);
			ctx.setAttributes(prod.getAttributes());
			ctx.getAttributes().remove(attr);
			
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
				tc.getContents().set(co, new Hole(KSort.getKSort(tc.getContents().get(co).getSort()).toString()));
			}
			else{
				//the others are fresh variables (anonymous) of sort K
				tc.getContents().set(co, MetaK.getFreshVar(KSort.getKSort(tc.getContents().get(co).getSort()).toString()));
			}
			co++;
		}

		Context ctx = new Context();
		ctx.setBody(tc);
		ctx.setAttributes(prod.getAttributes());
		ctx.getAttributes().remove(attr);

		items.add(ctx);
	}

  //KLabels are applied to associative KList,
  //so the context we must generate is the fairly
  //easy context KLabel(KList1 ,, HOLE ,, KList2)
  private void kLabelStrict(String attr, Production prod){
    List<Term> contents = new ArrayList<Term>(3);
    //first argument is a variable of sort K
    contents.add(MetaK.getFreshVar(MetaK.Constants.KList));
    //second is a HOLE
    contents.add(new Hole("K"));
    //third argument is a variable of sort K
    contents.add(MetaK.getFreshVar(MetaK.Constants.KList));
    KApp kapp = new KApp(MetaK.getTerm(prod), new KList(contents)); 
    //make a context from the TermCons
		Context ctx = new Context();
		ctx.setBody(kapp);
		ctx.setAttributes(prod.getAttributes());
		ctx.getAttributes().remove(attr);
    //add the context
		items.add(ctx);
  }

  //Same as above but with the condition
  //isKResult(KList1)
  private void kLabelSeqStrict(String attr, Production prod){
    List<Term> contents = new ArrayList<Term>(3);
    //first argument is a variable of sort K
    Term Var1 = MetaK.getFreshVar(MetaK.Constants.KList);
    contents.add(Var1);
    //second is a HOLE
    contents.add(new Hole("K"));
    //third argument is a variable of sort K
    contents.add(MetaK.getFreshVar(MetaK.Constants.KList));
    KApp kapp = new KApp(MetaK.getTerm(prod), new KList(contents)); 
    //make a context from the TermCons
		Context ctx = new Context();
		ctx.setBody(kapp);
		ctx.setAttributes(prod.getAttributes());
		ctx.getAttributes().remove(attr);
    //set the condition
    KApp condApp = new KApp(KLabelConstant.KRESULT_PREDICATE, Var1);
    ctx.setCondition(condApp);
    //add the context
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
					tc.getContents().set(i, new Hole(KSort.getKSort(tc.getContents().get(i).getSort()).toString()));

					if(attr.equalsIgnoreCase("seqstrict")){
						//previous terms should be KResults
						for (int j = 0; j < i; j++) {
							tc.getContents().get(j).setSort("KResult");
						}
					}
				}else{
					//the others are fresh variables (anonymous) of sort K
					tc.getContents().set(i, MetaK.getFreshVar(KSort.getKSort(tc.getContents().get(i).getSort()).toString()));
				}

				i++;

			}

			Context ctx = new Context();
			ctx.setBody(tc);
			ctx.setAttributes(prod.getAttributes());
			ctx.getAttributes().remove(attr);
			items.add(ctx);

			i = 0;
			co++;
		}
	}
}
