package org.kframework.backend.hkcd;

import org.kframework.kil.loader.Context;

/**
 * Transform AST of program into set of Haskell constructors.
 *
 * AST must not be processed by KAppModifier.
 *
 * @see ProgramLoader.loadPgmAst
 */
public class HaskellPgmFilter extends HaskellFilter {

	public HaskellPgmFilter(Context context) {
		super(context);
	}
}
