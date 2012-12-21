package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 11:40 PM
 */
public class AddSuperheatRules extends CopyOnWriteTransformer {
	java.util.List<ModuleItem> superHeats = new ArrayList<ModuleItem>();
	public AddSuperheatRules() {
		super("Add Superheat rules");
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		superHeats.clear();
		node = (Module) super.transform(node);
		if (!superHeats.isEmpty()) {
			node = node.shallowCopy();
			node.setItems(new ArrayList<ModuleItem>(node.getItems()));
			node.getItems().addAll(superHeats);
			node.getItems().add(new Import("K-STRICTNESS"));
		}
		return node;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (!node.containsAttribute(MetaK.Constants.heatingTag)) {
			return node;
		}
		boolean superheat = false;
		for (String heat : GlobalSettings.superheat) {
            if (node.containsAttribute(heat)) {
				superheat = true;
				break;
            }
        }
		if (!(node.getBody() instanceof Rewrite)) {
			GlobalSettings.kem.register(
					new KException(KException.ExceptionType.ERROR,
							KException.KExceptionGroup.CRITICAL,
							"Heating rules should have rewrite at the top.",
							getName(),
							node.getFilename(),
							node.getLocation())
			);
		}
		final Rewrite body = (Rewrite) node.getBody();
		if (!superheat) {
			// rule heat(redex((C[e] =>  e ~> C) ~> _:K),, _:List{K})
			KSequence kSequence = new KSequence();
			kSequence.getContents().add(body);
			kSequence.add(new Variable(MetaK.Constants.anyVarSymbol,"K"));
			Term redex = new KApp(Constant.REDEX_KLABEL,kSequence);
			ListOfK listOfK = new ListOfK();
			listOfK.add(redex);
			listOfK.add(new Variable(MetaK.Constants.anyVarSymbol, "List{K}"));
			Term heat = new KApp(Constant.HEAT_KLABEL, listOfK);
			Rule superHeat = node.shallowCopy();
			superHeat.setBody(heat);
			superHeats.add(superHeat);
			return node;
		}
		// add superheat rule
		// rule heat(redex(C[e] ~> RestHeat:K,,	LHeat:List{K},,
		//                 (.List{K} => redex(e ~> C ~> RestHeat:K))),,_:List{K})
		// when '_=/=K_('_inList`{K`}_(redex(e ~> C ~> RestHeat:K),,List{K}2KLabel LHeat:List{K}(.List{K})),# true(.List{K}))
		Rule superHeat = node.shallowCopy();
		Term left = body.getLeft(); // C[e]
		Term right = body.getRight(); // e ~> C
		Variable restHeat = MetaK.getFreshVar("K");
		Variable lHeat = MetaK.getFreshVar("List{K}");
		KSequence red1Seq = new KSequence();
		red1Seq.add(left); red1Seq.add(restHeat); //C[e] ~> RestHeat:K,
		ListOfK red1List = new ListOfK();
		red1List.add(red1Seq);red1List.add(lHeat); //C[e] ~> RestHeat:K,,	LHeat:List{K}
		KSequence red2Seq = new KSequence();
		red2Seq.getContents().addAll(((KSequence)right).getContents()); red2Seq.add(restHeat); // e ~> C ~> RestHeat:K
		Term red2 = new KApp(Constant.REDEX_KLABEL,red2Seq); // redex(e ~> C ~> RestHeat:K)
		Term red2rew = new Rewrite(new Empty("List{K}"), red2); // (.List{K} => redex(e ~> C ~> RestHeat:K))
		red1List.add(red2rew);
		Term red1 = new KApp(Constant.REDEX_KLABEL, red1List); // redex(C[e] ~> RestHeat:K,,	LHeat:List{K},,
															   //       (.List{K} => redex(e ~> C ~> RestHeat:K)))
		ListOfK heatList = new ListOfK();
		heatList.add(red1); heatList.add(new Variable(MetaK.Constants.anyVarSymbol, "List{K}"));
		Term heat = new KApp(Constant.HEAT_KLABEL, heatList);
		superHeat.setBody(heat);

		ListOfK inListList = new ListOfK();
		inListList.add(red2); inListList.add(new KApp(new KInjectedLabel(lHeat), new Empty("List{K}")));
		Term inList = new KApp(Constant.KLABEL("'_inList`{K`}_"), inListList);
		ListOfK condList = new ListOfK();
		condList.add(inList);
		condList.add(Constant.TRUE);
		Term cond = new KApp(Constant.KNEQ_KLABEL, condList);
		superHeat.setCondition(MetaK.incrementCondition(node.getCondition(),cond));
		superHeats.add(superHeat);

		// replace heating rule by
		// rule C[e] => heat(redex(C[e]),, heated(.List{K}))
		node = node.shallowCopy();
		Term red3 = new KApp(Constant.REDEX_KLABEL,left);
		ListOfK red3List = new ListOfK();
		red3List.add(red3);
		red3List.add(new KApp(Constant.HEATED_KLABEL, new Empty("List{K}")));
		Term heat2 = new KApp(Constant.HEAT_KLABEL, red3List);
		node.setBody(new Rewrite(left, heat2));


		return node;

	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
}
