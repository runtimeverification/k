package org.kframework.compile.transformers;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class ResolveBinder extends CopyOnWriteTransformer {

  private static final Constant BINDER_PREDICATE 
    = new Constant("KLabel", AddPredicates.predicate("Binder"));
  private static final Constant BOUNDED_PREDICATE
    = new Constant("KLabel", AddPredicates.predicate("Bound"));
  private static final Constant BOUNDING_PREDICATE
    = new Constant("KLabel", AddPredicates.predicate("Bounding"));

  private static final String REGEX
    = "\\s*(\\d+)(\\s*-\\>\\s*(\\d+))?\\s*(,?)";

	public ResolveBinder() {
		super("Resolve binder");
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		List<Production> prods = GetSyntaxByTag.applyVisitor(node, "binder");
		if (prods.isEmpty())
      return node;

		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		node = node.shallowCopy();
		node.setItems(items);

		for (Production prod : prods) {
      String bindInfo = prod.getAttributes().get("binder");
      if (bindInfo == null || bindInfo.equals(""))
        bindInfo = "1->" + prod.getArity();
      Pattern p = Pattern.compile(REGEX);
      Matcher m = p.matcher(bindInfo);
      Map<Integer, Integer> bndMap = new HashMap<Integer, Integer>();

      while (m.regionStart() < m.regionEnd()) {
        if (!m.lookingAt()) {
          System.err.println("[error:] could not parse binder attribute \"" + bindInfo.substring(m.regionStart(), m.regionEnd()) + "\"");
          System.exit(1);
        }
        if (m.end() < m.regionEnd()) {
          if (!m.group(4).equals(",")) {
            System.err.println("[error:] expecting ',' at the end \"" + m.group() + "\"");
            System.exit(1);
          }
        } else {
          if (!m.group(4).equals("")) {
            System.err.println("[error:] unexpected ',' at the end \"" + m.group() + "\"");
            System.exit(1);
          }
        }

        int bndIdx = Integer.parseInt(m.group(1));
        if (m.group(3) == null) {
          for (int idx = 1; idx <= prod.getArity(); idx++) {
            if (idx != bndIdx)
              bndMap.put(bndIdx, idx);
          }
        } else {
          bndMap.put(bndIdx, Integer.parseInt(m.group(3)));
        }

        m.region(m.end(), m.regionEnd());
      } 

      Rule rule = new Rule(
          new KApp(BINDER_PREDICATE, MetaK.getTerm(prod)),
          Constant.TRUE);
      rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			items.add(rule);

      Constant klblCt = new Constant("KLabel", prod.getKLabel());
      Term klblK = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);

      for (int bndIdx : bndMap.keySet()) {
        ListOfK list = new ListOfK();
        list.getContents().add(klblK);
        list.getContents().add(new Constant("Int", Integer.toString(bndIdx)));
        rule = new Rule(new KApp(BOUNDED_PREDICATE, list), Constant.TRUE);
			  rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			  items.add(rule);
      }

      for (int bodyIdx : bndMap.values()) {
        ListOfK list = new ListOfK();
        list.getContents().add(klblK);
        list.getContents().add(new Constant("Int", Integer.toString(bodyIdx)));
        rule = new Rule(new KApp(BOUNDING_PREDICATE, list), Constant.TRUE);
			  rule.getAttributes().getContents().add(new Attribute("anywhere", ""));
			  items.add(rule);
      }

/*
if (bndIdx == 0 || bndIdx > prod.getArity())  {
          System.err.println("[error:] argument index out of bounds: " + bndIdx);
          System.exit(1);
        }

if (bndMap.containsKey(bndIndex)) {
            System.err.println("[error:] " + bndIdx );
            System.exit(1);
          }
*/
		}

		return node;
	}
}
