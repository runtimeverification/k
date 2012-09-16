package ro.uaic.info.fmse.compile.transformers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import ro.uaic.info.fmse.compile.utils.GetLhsPattern;
import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Attributes;
import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Context;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.List;
import ro.uaic.info.fmse.k.ListItem;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class ResolveBlockingInput extends GetLhsPattern {
	
	Set<String> inputCells = new HashSet<String>();
	java.util.List<Rule> generated = new ArrayList<Rule>();
	boolean hasInputCell;
	
	public ResolveBlockingInput() {
		super("Resolve Blocking Input");
	}
	
	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		Configuration config = MetaK.getConfiguration(node);
		config.accept(new BasicVisitor() {
			@Override
			public void visit(Cell node) {
				String stream = node.getAttributes().get("stream");
				if ("stdin".equals(stream)) {
					inputCells.add(node.getLabel());
				}
				super.visit(node);
			}

		});
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		ASTNode result = super.transform(node);
		if (result != node) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Should have obtained the same module ", 
					node.getFilename(), node.getLocation(), 0));					
		}
		if (generated.isEmpty()) return node;
		node = node.shallowCopy();
		node.getItems().addAll(generated);
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
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		hasInputCell = false;
		ASTNode result = super.transform(node);
		if (hasInputCell) {
			generated.add((Rule)result);
		}
		return node;
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		if ((!inputCells.contains(node.getLabel()))) {
			return super.transform(node);
		}
		if (!(node.getElipses().equals("right"))) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"cell should have right ellipses but it doesn't." +
							System.getProperty("line.separator") + "Won't transform.", 
							node.getFilename(), node.getLocation(), 0));
			return node;
		}
		Term contents = node.getContents();
		if (!(contents instanceof Rewrite)) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a rewrite of a basic type variable into the empty list but got " + contents.getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							contents.getFilename(), contents.getLocation(), 0));
			return node;
		}
		Rewrite rewrite = (Rewrite) contents;
		if (!(rewrite.getLeft() instanceof ListItem)) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a list item but got " + rewrite.getLeft().getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							rewrite.getLeft().getFilename(), rewrite.getLeft().getLocation(), 0));
			return node;			
		}
		ListItem item = (ListItem) rewrite.getLeft();
		if (!(item.getItem() instanceof Variable &&
				MetaK.isBuiltinSort(item.getItem().getSort()))) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a basic type variable but got " + item.getItem().getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							item.getItem().getFilename(), item.getItem().getLocation(), 0));
			return node;
		}			
		if (!(rewrite.getRight() instanceof Empty && rewrite.getRight().getSort().equals("List"))) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting an empty list but got " + rewrite.getRight().getClass() + " of sort " + 
							rewrite.getRight().getSort() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							rewrite.getRight().getFilename(), rewrite.getRight().getLocation(), 0));
			return node;						
		}
		
		hasInputCell = true;
		
		
//		  syntax List ::= "#parse" "(" String "," K ")"   [cons(List1ParseSyn)]
		TermCons parseTerm = new TermCons("List", "List1ParseSyn");
		parseTerm.getContents().add(new Constant("String", "\"" + item.getItem().getSort() + "\""));
		parseTerm.getContents().add(new Empty("K"));
		
//		  syntax List ::= "#buffer" "(" K ")"           [cons(List1IOBufferSyn)]
		TermCons ioBuffer = new TermCons("List", "List1IOBufferSyn");
		ioBuffer.getContents().add(new Variable(MetaK.getFreshVar("K")));
		
//		ctor(List)[replaceS[emptyCt(List),parseTerm(string(Ty),nilK)],ioBuffer(mkVariable('BI,K))]
		List list = new List();
		list.getContents().add(new Rewrite(new Empty("List"), parseTerm));
		list.getContents().add(ioBuffer);
		
		node = node.shallowCopy();
		node.setContents(list);
		return node;
	}
}
