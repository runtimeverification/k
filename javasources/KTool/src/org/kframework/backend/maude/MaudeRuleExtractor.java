package org.kframework.backend.maude;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/18/12
 * Time: 12:59 AM
 */
public class MaudeRuleExtractor extends CopyOnWriteTransformer {
	MaudeFilter maudeFilter;

	public MaudeRuleExtractor(Context context) {
		super("Maude Rules Extractor", context);
		maudeFilter = new MaudeFilter(context);
	}

	public String getResult() {
		return maudeFilter.getResult();
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		node.accept(maudeFilter);
		return null;
	}

	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;    //To change body of overridden methods use File | Settings | File Templates.
	}
}
