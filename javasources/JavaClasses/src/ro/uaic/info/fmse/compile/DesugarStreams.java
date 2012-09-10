package ro.uaic.info.fmse.compile;

import java.util.ArrayList;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Context;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.List;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

public class DesugarStreams extends CopyOnWriteTransformer implements CompilerStep {

	@Override
	public Definition compile(Definition def) {
		ASTNode result = null;
		try {
			result = def.accept(this);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (result == def) return def;
		if (!(result instanceof Definition)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Configuration Cleaner failed.", 
					def.getFilename(), def.getLocation(), 0));
		}
		return (Definition) result;
	}

	@Override
	public String getName() {
		return "Streams Desugarer";
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		ASTNode result = super.transform(node);
		if (!(result instanceof Cell)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Cell, but got " + result.getClass() + " in Streams Desugarer.", 
					result.getFilename(), result.getLocation(), 0));
		}
		Cell cell = (Cell) result;
		String stream = cell.getAttributes().get("stream");
		if (null == stream) return cell;
		if (result == node) {
			node = node.shallowCopy();
		} else node = cell;
		node.setContents(makeStreamList(stream, node.getContents()));
		return node;
	}
	
	private Term makeStreamList(String stream, Term contents) {
		List result;
		if (contents instanceof List) {
			result = ((List)contents).shallowCopy();
		} else {
			result = new List();
			result.getContents().add(contents);
		}
		java.util.List<Term> items = new ArrayList<Term>();
		if ("stdin".equals(stream)) {
//			eq evalCleanConf(T, "stdin") = mkCollection(List, (T, ioBuffer(stdinVariable), noIOVariable, stdinStream)) .
			items.addAll(result.getContents());
			
//			syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
			TermCons buffer = new TermCons("List", "List1IOBufferSyn");
			java.util.List<Term> bufferTerms = new ArrayList<Term>();
			bufferTerms.add(new Variable("$stdin", "K")); // eq stdinVariable = mkVariable('$stdin,K) .
			buffer.setContents(bufferTerms);
			items.add(buffer);
			
			items.add(new Variable("$noIO", "List"));//		  eq noIOVariable = mkVariable('$noIO,List) .
			
//			syntax List ::= "#istream" "(" Int ")"        [cons(List1InputStreamSyn)]
			TermCons stdinStream = new TermCons("List", "List1InputStreamSyn");
			java.util.List<Term> stdinStreamTerms = new ArrayList<Term>();
			stdinStreamTerms.add(new Constant("Int", "0"));
			stdinStream.setContents(stdinStreamTerms);
			items.add(stdinStream);
		}
		if ("stdout".equals(stream)) {
//			eq evalCleanConf(T, "stdout") = mkCollection(List, (stdoutStream, noIOVariable, ioBuffer(nilK),T)) .
//            | "#ostream" "(" Int ")"        [cons(List1OutputStreamSyn)]
			TermCons stdoutStream = new TermCons("List", "List1OutputStreamSyn");
			java.util.List<Term> stdinStreamTerms = new ArrayList<Term>();
			stdinStreamTerms.add(new Constant("Int", "1"));
			stdoutStream.setContents(stdinStreamTerms);
			items.add(stdoutStream);
			
			items.add(new Variable("$noIO", "List"));//		  eq noIOVariable = mkVariable('$noIO,List) .

//			syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
			TermCons buffer = new TermCons("List", "List1IOBufferSyn");
			java.util.List<Term> bufferTerms = new ArrayList<Term>();
			bufferTerms.add(new Empty("K"));
			buffer.setContents(bufferTerms);
			items.add(buffer);

			items.addAll(result.getContents());
		}
		result.setContents(items);
		return result;
	}

	@Override
	public ASTNode transform(Context node) {
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
