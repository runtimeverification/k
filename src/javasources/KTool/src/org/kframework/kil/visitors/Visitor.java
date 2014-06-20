// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.*;

public interface Visitor<P, R, E extends Throwable> {
    public R visit(ASTNode node, P p) throws E;
    public R visit(ParseError node, P p) throws E;
    public R visit(Definition node, P p) throws E;
    public R visit(DefinitionItem node, P p) throws E;
    // <DefinitionItems>
    public R visit(LiterateDefinitionComment node, P p) throws E;
    public R visit(Module node, P p) throws E;
    public R visit(Require require, P p) throws E;
    // </DefinitionItems>
    public R visit(ModuleItem node, P p) throws E;
    // <ModuleItems>
    public R visit(Import node, P p) throws E;
    public R visit(LiterateModuleComment node, P p) throws E;
    public R visit(Sentence node, P p) throws E;
    // <Sentences>
    public R visit(StringSentence node, P p) throws E;
    public R visit(Restrictions node, P p) throws E;
    public R visit(Configuration node, P p) throws E;
    public R visit(Context node, P p) throws E;
    public R visit(Rule node, P p) throws E;
    // </Sentences>
    public R visit(Syntax node, P p) throws E;
    public R visit(PriorityExtended node, P p) throws E;
    public R visit(PriorityExtendedAssoc node, P p) throws E;
    // <ModuleItems>
    public R visit(PriorityBlock node, P p) throws E;
    public R visit(PriorityBlockExtended node, P p) throws E;
    public R visit(Production node, P p) throws E;
    public R visit(ProductionItem node, P p) throws E;
    // <ProductionItems>
    public R visit(Sort node, P p) throws E;
    public R visit(Lexical node, P p) throws E;
    public R visit(Terminal node, P p) throws E;
    public R visit(UserList node, P p) throws E;
    // </ProductionItems>
    public R visit(Term node, P p) throws E;
    // <Terms>
    public R visit(Cell node, P p) throws E;
    public R visit(org.kframework.kil.Collection node, P p) throws E;
    // <Collections>
    public R visit(Ambiguity node, P p) throws E;
    public R visit(Bag node, P p) throws E;
    public R visit(KSequence node, P p) throws E;
    public R visit(KList node, P p) throws E;
    // </Collections>
    public R visit(CollectionItem node, P p) throws E;
    // <CollectionItems>
    public R visit(BagItem node, P p) throws E;
    // </CollectionItems>
    // <BuiltinDataStructure>
    public R visit(BuiltinLookup node, P p) throws E;
    public R visit(DataStructureBuiltin node, P p) throws E;
    public R visit(CollectionBuiltin node, P p) throws E;
    public R visit(ListBuiltin node, P p) throws E;
    public R visit(ListLookup node, P p) throws E;
    public R visit(ListUpdate node, P p) throws E;
    public R visit(SetBuiltin node, P p) throws E;
    public R visit(SetLookup node, P p) throws E;
    public R visit(SetUpdate node, P p) throws E;
    public R visit(MapBuiltin node, P p) throws E;
    public R visit(MapLookup node, P p) throws E;
    public R visit(MapUpdate node, P p) throws E;
    // </BuiltinDataStructure>
    // <Token>
    public R visit(Token node, P p) throws E;
    public R visit(BoolBuiltin node, P p) throws E;
    public R visit(IntBuiltin node, P p) throws E;
    public R visit(StringBuiltin node, P p) throws E;
    public R visit(FloatBuiltin node, P p) throws E;
    public R visit(GenericToken node, P p) throws E;
    // </Token>
    public R visit(ListTerminator node, P p) throws E;
    public R visit(Hole node, P p) throws E;
    public R visit(FreezerHole node, P p) throws E;
    public R visit(KApp node, P p) throws E;
    public R visit(KItemProjection node, P p) throws E;
    public R visit(KLabel node, P p) throws E;
    public R visit(KLabelConstant node, P p) throws E;
    public R visit(KLabelInjection node, P p) throws E;
    public R visit(Rewrite node, P p) throws E;
    public R visit(TermCons node, P p) throws E;
    public R visit(Bracket node, P p) throws E;
    public R visit(Cast node, P p) throws E;
    public R visit(Variable node, P p) throws E;
    // </Terms>
    public R visit(TermComment node, P p) throws E;
    // Others
    public R visit(Attributes node, P p) throws E;
    public R visit(Attribute node, P p) throws E;
    public R visit(KInjectedLabel kInjectedLabel, P p) throws E;
    public R visit(FreezerLabel freezerLabel, P p) throws E;
    public R visit(Freezer f, P p) throws E;
    public R visit(BackendTerm term, P p) throws E;
    
    /**
     * Visit an AST tree. This is the main entry point whenever you want to apply a visitor to an ASTNode.
     * 
     * @param node The node to visit.
     * @param p The optional parameter to pass to the visit methods.
     * @return The value returned from visiting the entire ASTNode tree.
     * @throws E if the visitor implementation raises an exception.
     */
    public R visitNode(ASTNode node, P p) throws E;
    
    /**
     * Visit an AST tree with {@code p} equal to null. Useful if {@code <P>} is {@link Void}. 
     * 
     * This method should be implemented by calling {@code visitNode(node, null)}.
     * 
     * @param node The node to visit.
     * @return The value returned from visiting the entire ASTNode tree.
     * @throws E if the visitor implementation raises an exception.
     */
    public R visitNode(ASTNode node) throws E;

    /**
     * This method must be called by {@link ASTNode#accept(Visitor, Object)} with the ASTNode
     * and the result of transforming the ASTNode. Its purpose is to factor out functionality
     * which must be performed by the visitor for correctness regardless of whether the visit
     * methods are overridden. For example, a visitor may override a method in such a way that 
     * children are not accepted, or so that the parent class's visit method is not called.
     * This method serves to guarantee that certain functionality will occur regardless of whether
     * this is the case.
     * @param node Should be the {@code this} of the ASTNode.
     * @param Should be the result of visiting the ASTNode.
     * @return Implementations should return {@code r}.
     */
    public R complete(ASTNode node, R r);
}
