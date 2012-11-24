package org.kframework.compile.transformers;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class ResolveBinder extends CopyOnWriteTransformer {

	private static final Constant BINDER_PREDICATE
			= new Constant("KLabel", AddPredicates.predicate("Binder"));
	//    private static final Constant BINDER_STAR_PREDICATE
//            = new Constant("KLabel", AddPredicates.predicate("BinderStar"));
	private static final Constant BOUNDED_PREDICATE
			= new Constant("KLabel", AddPredicates.predicate("Bound"));
	private static final Constant BOUNDING_PREDICATE
			= new Constant("KLabel", AddPredicates.predicate("Bounding"));

	private static final String REGEX
			//= "\\s*(\\d+)(\\*?)\\s*-\\>\\s*(\\d+)\\s*(,\\s*(\\d+)(\\*?)\\s*-\\>\\s*(\\d+)\\s*)*";
			= "\\s*(\\d+)(\\*?)\\s*-\\>\\s*(\\d+)\\s*(,?)";

	public ResolveBinder() {
		super("Resolve binder");
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		List<Production> prods = GetSyntaxByTag.applyVisitor(node, "binder");
		if (prods.isEmpty()) return node;
		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();
		for (Production prod : prods) {
			String bindInfo = prod.getAttributes().get("binder");
			if (bindInfo == null)
				bindInfo = "";
			if (bindInfo == "") {
				bindInfo = "1->" + prod.getArity();
			}
			Pattern p = Pattern.compile(REGEX);
			Matcher m = p.matcher(bindInfo);

			int bndIdx = -1;
			Boolean isStar = false;
			while (m.regionStart() < m.regionEnd()) {
				if (!m.lookingAt()) {
					System.err.println("[error:] could not parse binder attribute \"" + bindInfo.substring(m.regionStart(), m.regionEnd()) + "\"");
					System.exit(1);
				}
				if (m.end() < m.regionEnd()) {
					if (!m.group(4).equals(",")) {
						System.err.println("[error:] expecting ',' after \"" + m.group() + "\"");
						System.exit(1);
					}
				} else {
					if (!m.group(4).equals("")) {
						System.err.println("[error:] unexpected ',' after \"" + m.group() + "\"");
						System.exit(1);
					}
				}

				if (bndIdx != -1) {
					if (bndIdx != Integer.parseInt(m.group(1))) {
						System.err.println("[error:] multiple bounded arguments: " + bndIdx + "," + m.group(1));
						System.exit(1);
					}
					if (isStar != m.group(2).equals("*")) {
						System.err.println("[error:] argument " + bndIdx + " is declared as variable and collection");
						System.exit(1);
					}
				} else {
					bndIdx = Integer.parseInt(m.group(1));
					if (bndIdx == 0 || bndIdx > prod.getArity())  {
						System.err.println("[error:] argument index out of bounds: " + bndIdx);
						System.exit(1);
					}
					isStar = m.group(2).equals("*");
				}

				int termIdx = Integer.parseInt(m.group(3));

				Constant klblCt = new Constant("KLabel", prod.getKLabel());
				Term kapp = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);
				ListOfK list = new ListOfK();
				list.getContents().add(kapp);
				list.getContents().add(new Constant("Int", Integer.toString(termIdx)));
				Rule rule = new Rule(
						new KApp(new Constant("KLabel", "isBounding"), list),
						Constant.TRUE);
				rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
				items.add(rule);

				m.region(m.end(), m.regionEnd());
			}

			Rule rule = new Rule(
					new KApp(new Constant("KLabel", "isBinder"), MetaK.getTerm(prod)),
					Constant.TRUE);
			rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			items.add(rule);

//      if (isStar) {
//        rule = new Rule(
//            new KApp(new Constant("KLabel", "isStarBinder"), MetaK.getTerm(prod)),
//            Constant.TRUE);
//        rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
//			  items.add(rule);
//      }

			Constant klblCt = new Constant("KLabel", prod.getKLabel());
			Term kapp = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);
			ListOfK list = new ListOfK();
			list.getContents().add(kapp);
			list.getContents().add(new Constant("Int", Integer.toString(bndIdx)));
			Term term = Constant.TRUE;
			if (isStar) {
				term = Constant.STAR;
			}
			rule = new Rule(
					new KApp(new Constant("KLabel", "isBound"), list),
					term);
			rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			items.add(rule);

		}
		node.setItems(items);
		return node;
	}
}
