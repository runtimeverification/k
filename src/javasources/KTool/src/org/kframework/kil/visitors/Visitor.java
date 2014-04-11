package org.kframework.kil.visitors;

import org.kframework.kil.*;

public interface Visitor<P, R> {
    public R visit(ASTNode node, P p);
    public R visit(Definition node, P p);
    public R visit(DefinitionItem node, P p);
    // <DefinitionItems>
    public R visit(LiterateDefinitionComment node, P p);
    public R visit(Module node, P p);
    public R visit(Require require, P p);
    // </DefinitionItems>
    public R visit(ModuleItem node, P p);
    // <ModuleItems>
    public R visit(Import node, P p);
    public R visit(LiterateModuleComment node, P p);
    public R visit(Sentence node, P p);
    // <Sentences>
    public R visit(StringSentence node, P p);
    public R visit(Restrictions node, P p);
    public R visit(Configuration node, P p);
    public R visit(Context node, P p);
    public R visit(Rule node, P p);
    // </Sentences>
    public R visit(Syntax node, P p);
    public R visit(PriorityExtended node, P p);
    public R visit(PriorityExtendedAssoc node, P p);
    // <ModuleItems>
    public R visit(PriorityBlock node, P p);
    public R visit(PriorityBlockExtended node, P p);
    public R visit(Production node, P p);
    public R visit(ProductionItem node, P p);
    // <ProductionItems>
    public R visit(Sort node, P p);
    public R visit(Lexical node, P p);
    public R visit(Terminal node, P p);
    public R visit(UserList node, P p);
    // </ProductionItems>
    public R visit(Term node, P p);
    // <Terms>
    public R visit(Cell node, P p);
    public R visit(org.kframework.kil.Collection node, P p);
    // <Collections>
    public R visit(Ambiguity node, P p);
    public R visit(Bag node, P p);
    public R visit(KSequence node, P p);
    public R visit(List node, P p);
    public R visit(KList node, P p);
    public R visit(org.kframework.kil.Map node, P p);
    public R visit(Set node, P p);
    // </Collections>
    public R visit(CollectionItem node, P p);
    // <CollectionItems>
    public R visit(BagItem node, P p);
    public R visit(ListItem node, P p);
    public R visit(MapItem node, P p);
    public R visit(SetItem node, P p);
    // </CollectionItems>
    // <BuiltinDataStructure>
    public R visit(DataStructureBuiltin node, P p);
    public R visit(CollectionBuiltin node, P p);
    public R visit(ListBuiltin node, P p);
    public R visit(ListLookup node, P p);
    public R visit(ListUpdate node, P p);
    public R visit(SetBuiltin node, P p);
    public R visit(SetLookup node, P p);
    public R visit(SetUpdate node, P p);
    public R visit(MapBuiltin node, P p);
    public R visit(MapLookup node, P p);
    public R visit(MapUpdate node, P p);
    // </BuiltinDataStructure>
    // <Token>
    public R visit(Token node, P p);
    public R visit(BoolBuiltin node, P p);
    public R visit(IntBuiltin node, P p);
    public R visit(StringBuiltin node, P p);
    public R visit(GenericToken node, P p);
    // </Token>
    public R visit(ListTerminator node, P p);
    public R visit(Hole node, P p);
    public R visit(FreezerHole node, P p);
    public R visit(KApp node, P p);
    public R visit(KItemProjection node, P p);
    public R visit(KLabel node, P p);
    public R visit(KLabelConstant node, P p);
    public R visit(KLabelInjection node, P p);
    public R visit(Rewrite node, P p);
    public R visit(TermCons node, P p);
    public R visit(Bracket node, P p);
    public R visit(Cast node, P p);
    public R visit(Variable node, P p);
    // </Terms>
    public R visit(TermComment node, P p);
    // Others
    public R visit(KInjectedLabel kInjectedLabel, P p);
    public R visit(FreezerLabel freezerLabel, P p);
    public R visit(Freezer f, P p);
    public R visit(BackendTerm term, P p);
}
