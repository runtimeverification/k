// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;


public class DesugarStreams extends CopyOnWriteTransformer {
    
    ArrayList<String> channels = new ArrayList<String>();

    public DesugarStreams(org.kframework.kil.loader.Context context) {
        super("Desugar streams", context);
        
        channels.add("stdin");
        channels.add("stdout");
    }
    
    @Override
    public ASTNode visit(Cell node, Void _)  {
        ASTNode result = super.visit(node, _);
        if (!(result instanceof Cell)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
                    KExceptionGroup.INTERNAL, 
                    "Expecting Cell, but got " + result.getClass() + " in Streams Desugarer.", 
                    getName(), result.getFilename(), result.getLocation()));
        }
        Cell cell = (Cell) result;
        String stream = cell.getCellAttributes().get("stream");
        if (null == stream) return cell;
        if (result == node) {
            node = node.shallowCopy();
        } else node = cell;
        node.setContents(makeStreamList(stream, node));
        return node;
    }
    
    private Term makeStreamList(String stream, Cell node) {
        Term contents = node.getContents();
        
        Term addAtBeginning = null;
        Term addAtEnd = null;
        java.util.List<Term> items = new ArrayList<Term>();
        if ("stdin".equals(stream)) {
//            eq evalCleanConf(T, "stdin") = mkCollection(List, (T, ioBuffer(stdinVariable), noIOVariable, stdinStream)) .
            addAtBeginning = contents;
//            syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
            TermCons buffer = new TermCons("Stream", "Stream1IOBufferSyn", context);
            java.util.List<Term> bufferTerms = new ArrayList<Term>();
            bufferTerms.add(new Variable("$stdin", "String")); // eq stdinVariable = mkVariable('$stdin,K) .
            buffer.setContents(bufferTerms);
            items.add(newListItem(buffer));
            
            items.add(new Variable("$noIO", ("List")));//          eq noIOVariable = mkVariable('$noIO,List) .
            
//            syntax List ::= "#istream" "(" Int ")"        [cons(List1InputStreamSyn)]
            TermCons stdinStream = new TermCons("Stream", "Stream1InputStreamSyn", context);
            java.util.List<Term> stdinStreamTerms = new ArrayList<Term>();
            stdinStreamTerms.add(IntBuiltin.ZERO);
            stdinStream.setContents(stdinStreamTerms);
            items.add(newListItem(stdinStream));
        }
        if ("stdout".equals(stream)) {
//            eq evalCleanConf(T, "stdout") = mkCollection(List, (stdoutStream, noIOVariable, ioBuffer(nilK),T)) .
//            | "#ostream" "(" Int ")"        [cons(List1OutputStreamSyn)]
            TermCons stdoutStream = new TermCons("Stream", "Stream1OutputStreamSyn", context);
            java.util.List<Term> stdinStreamTerms = new ArrayList<Term>();
            stdinStreamTerms.add(IntBuiltin.ONE);
            stdoutStream.setContents(stdinStreamTerms);
            items.add(newListItem(stdoutStream));
            
            items.add(new Variable("$noIO", ("List")));//          eq noIOVariable = mkVariable('$noIO,List) .

//            syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
            TermCons buffer = new TermCons("Stream", "Stream1IOBufferSyn", context);
            java.util.List<Term> bufferTerms = new ArrayList<Term>();
            bufferTerms.add(StringBuiltin.EMPTY);
            buffer.setContents(bufferTerms);
            items.add(newListItem(buffer));

            addAtEnd = contents;
        }
        if(channels.indexOf(stream) == -1){
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
                    KExceptionGroup.INTERNAL, 
                    "Make sure you give the correct stream names: " + channels.toString(), 
                    getName(), node.getFilename(), node.getLocation()));
        }
        DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
        Term newItems = DataStructureSort.listOf(context, items.toArray(new Term[] {}));
        if (addAtBeginning != null) {
            newItems = KApp.of(KLabelConstant.of(myList.constructorLabel(), context), addAtBeginning, newItems);
        }
        if (addAtEnd != null) {
            newItems = KApp.of(KLabelConstant.of(myList.constructorLabel(), context), newItems, addAtEnd);
        }
        return newItems;
    }

    private Term newListItem(Term element) {
        DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
        return KApp.of(KLabelConstant.of(myList.elementLabel(), context), element);
    }        

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _) {
        return node;
    }
    
    @Override
    public ASTNode visit(Rule node, Void _) {
        return node;
    }
    
    @Override
    public ASTNode visit(Syntax node, Void _) {
        return node;
    }
    
}
