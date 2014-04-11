package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;


public class DesugarStreams extends CopyOnWriteTransformer {
    
    ArrayList<String> channels = new ArrayList<String>();
    boolean newList;

    public DesugarStreams(org.kframework.kil.loader.Context context, boolean newList) {
        super("Desugar streams", context);
        
        channels.add("stdin");
        channels.add("stdout");
        this.newList = newList;
    }
    
    @Override
    public ASTNode transform(Cell node) throws TransformerException {
        ASTNode result = super.transform(node);
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
        
        List result;
        Term addAtBeginning = null;
        Term addAtEnd = null;
        if (newList) {
            result = null;
        } else if (contents instanceof List) {
            result = ((List)contents).shallowCopy();
        } else {
            result = new List();
            result.getContents().add(contents);
        }
        java.util.List<Term> items = new ArrayList<Term>();
        if ("stdin".equals(stream)) {
//            eq evalCleanConf(T, "stdin") = mkCollection(List, (T, ioBuffer(stdinVariable), noIOVariable, stdinStream)) .
            if (!newList) items.addAll(result.getContents());
            else addAtBeginning = contents;
//            syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
            TermCons buffer = new TermCons("Stream", "Stream1IOBufferSyn", context);
            java.util.List<Term> bufferTerms = new ArrayList<Term>();
            bufferTerms.add(new Variable("$stdin", "String")); // eq stdinVariable = mkVariable('$stdin,K) .
            buffer.setContents(bufferTerms);
            items.add(newListItem(buffer));
            
            items.add(new Variable("$noIO", (!newList ? "ListItem" : "List")));//          eq noIOVariable = mkVariable('$noIO,List) .
            
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
            
            items.add(new Variable("$noIO", (!newList ? "ListItem" : "List")));//          eq noIOVariable = mkVariable('$noIO,List) .

//            syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
            TermCons buffer = new TermCons("Stream", "Stream1IOBufferSyn", context);
            java.util.List<Term> bufferTerms = new ArrayList<Term>();
            bufferTerms.add(StringBuiltin.EMPTY);
            buffer.setContents(bufferTerms);
            items.add(newListItem(buffer));

            if (!newList) items.addAll(result.getContents());
            else addAtEnd = contents;
        }
        if(channels.indexOf(stream) == -1){
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
                    KExceptionGroup.INTERNAL, 
                    "Make sure you give the correct stream names: " + channels.toString(), 
                    getName(), node.getFilename(), node.getLocation()));
        }
        if (newList) {
            DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
            Term newItems = DataStructureSort.listOf(context, items.toArray(new Term[] {}));
            if (addAtBeginning != null) {
                newItems = KApp.of(KLabelConstant.of(myList.constructorLabel(), context), addAtBeginning, newItems);
            }
            if (addAtEnd != null) {
                newItems = KApp.of(KLabelConstant.of(myList.constructorLabel(), context), newItems, addAtEnd);
            }
            return newItems;
        } else {
            result.setContents(items);
            return result;
        }
    }

    private Term newListItem(Term element) {
        if (newList) {
            DataStructureSort myList = context.dataStructureListSortOf(DataStructureSort.DEFAULT_LIST_SORT);
            return KApp.of(KLabelConstant.of(myList.elementLabel(), context), element);
        } else {
            return new ListItem(element);
        }
    }        

    @Override
    public ASTNode transform(org.kframework.kil.Context node) {
        return node;
    }
    
    @Override
    public ASTNode transform(Rule node) {
        return node;
    }
    
    @Override
    public ASTNode transform(Syntax node) {
        return node;
    }
    
}
