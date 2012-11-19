package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

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

public class StrictnessToContexts extends CopyOnWriteTransformer {

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

		if (prods.isEmpty()) return node;
		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();

//		System.out.println();		

		for (Production prod : prods) {

//			System.out.println(prod.toString());

			Attributes attributes = prod.getAttributes();

			if (attributes.containsKey("strict")){
				String arg = attributes.get("strict");
//				System.out.println("strict: " + arg);

				//strict in only one argument
				if(!arg.equalsIgnoreCase("") && arg.indexOf(",") == -1){
					int argi = Integer.parseInt(arg);

					int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

//					System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

					int co = 0;

					TermCons tc = (TermCons) MetaK.getTerm(prod);

					while(co < size){
						if(co == argi-1){
							tc.getContents().set(co, new Hole("K"));
						}
						//						else{
						//							tc.getContents().set(co, MetaK.getFreshVar(tc.getContents().get(co).getSort()));
						//						}
						co++;
					}

					Context ctx = new Context();
					ctx.setBody(tc);

//					System.out.println(ctx.toString());

					items.add(ctx);

					//strict in all arguments
				}else if(arg.equalsIgnoreCase("")){

					int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

//					System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

					int co = 0, i = 0;

					while(co < size){
						TermCons tc = (TermCons) MetaK.getTerm(prod);

						while(i < size){

							if(i == co)
								tc.getContents().set(i, new Hole("K"));
							//							else
							//								tc.getContents().set(i, MetaK.getFreshVar(tc.getContents().get(i).getSort()));

							i++;

						}

						Context ctx = new Context();
						ctx.setBody(tc);

//						System.out.println(ctx.toString());

						items.add(ctx);

						i = 0;
						co++;
					}


					//strict in more than one arguments
				}else{

					StringTokenizer st = new StringTokenizer(arg, ", ");

					String[] s = new String[st.countTokens()];
					int j = 0;

					while(st.hasMoreTokens()){s[j] = st.nextToken(); j++;}

					int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

//					System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

					int co = 0, i = 0;

					while(co < s.length){
						TermCons tc = (TermCons) MetaK.getTerm(prod);

						while(i < size){

							if(i == Integer.parseInt(s[co])-1)
								tc.getContents().set(i, new Hole("K"));
							//							else
							//								tc.getContents().set(i, MetaK.getFreshVar(tc.getContents().get(i).getSort()));

							i++;
						}

						Context ctx = new Context();
						ctx.setBody(tc);

//						System.out.println(ctx.toString());

						items.add(ctx);

						co++;
						i = 0;
					}
				}

				prod.getAttributes().remove("strict");
			}

			if (attributes.containsKey("seqstrict")){
//				System.out.println("seqstrict: " + attributes.get("seqstrict"));

				int size = ((TermCons) MetaK.getTerm(prod)).getContents().size(); 

//				System.out.println("Contents: " + ((TermCons) MetaK.getTerm(prod)).getContents() + "\nsize: " + size);

				int co = 0, i = 0;

				while(co < size){
					TermCons tc = (TermCons) MetaK.getTerm(prod);

					while(i < size){

						if(i == co)
							tc.getContents().set(i, new Hole("K"));
						//						else
						//							tc.getContents().set(i, MetaK.getFreshVar(tc.getContents().get(i).getSort()));

						i++;

					}

					Context ctx = new Context();
					ctx.setBody(tc);

//					System.out.println(ctx.toString());

					items.add(ctx);

					i = 0;
					co++;
				}

				prod.getAttributes().remove("seqstrict");
			}

		}

		node.setItems(items);

		return node;
	}
}
