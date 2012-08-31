package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;

/**
 * Transform AST of program into set of Haskell constructors.
 *
 * AST must not be processed by KAppModifier.
 *
 * @see ProgramLoader.loadPgmAst
 */
public class HaskellPgmFilter extends HaskellFilter {
}
