package org.kframework.backend.maude;

import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/18/12
 * Time: 12:59 AM
 */
public class MaudeContextExtractor extends CopyOnWriteTransformer {
	MaudeFilter maudeFilter = new MaudeFilter(definitionHelper);

	public MaudeContextExtractor(DefinitionHelper definitionHelper) {
		super("Maude Contexts Extractor", definitionHelper);
	}

	public String getResult() {
		return maudeFilter.getResult();
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		node.accept(maudeFilter);
		return null;
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
