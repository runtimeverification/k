package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.kframework.compile.utils.GetLhsPattern;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.Module;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;


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
					node.getFilename(), node.getLocation()));					
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
							node.getFilename(), node.getLocation()));
			return node;
		}
		Term contents = node.getContents();
		if (!(contents instanceof Rewrite)) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a rewrite of a basic type variable into the empty list but got " + contents.getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							contents.getFilename(), contents.getLocation()));
			return node;
		}
		Rewrite rewrite = (Rewrite) contents;
		if (!(rewrite.getLeft() instanceof ListItem)) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a list item but got " + rewrite.getLeft().getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							rewrite.getLeft().getFilename(), rewrite.getLeft().getLocation()));
			return node;			
		}
		ListItem item = (ListItem) rewrite.getLeft();
		if (!(item.getItem() instanceof Variable &&
				MetaK.isBuiltinSort(item.getItem().getSort()))) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting a basic type variable but got " + item.getItem().getClass() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							item.getItem().getFilename(), item.getItem().getLocation()));
			return node;
		}			
		if (!(rewrite.getRight() instanceof Empty && rewrite.getRight().getSort().equals("List"))) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Expecting an empty list but got " + rewrite.getRight().getClass() + " of sort " + 
							rewrite.getRight().getSort() + "." +
							System.getProperty("line.separator") + "Won't transform.", 
							rewrite.getRight().getFilename(), rewrite.getRight().getLocation()));
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
