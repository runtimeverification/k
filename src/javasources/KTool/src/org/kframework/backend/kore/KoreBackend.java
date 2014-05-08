// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.unparser.Indenter;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.AddHeatingConditions;
import org.kframework.compile.transformers.AddK2SMTLib;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.transformers.AddSemanticEquality;
import org.kframework.compile.transformers.AddStreamCells;
import org.kframework.compile.transformers.AddSupercoolDefinition;
import org.kframework.compile.transformers.AddSuperheatRules;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.AddTopCellRules;
import org.kframework.compile.transformers.ContextsToHeating;
import org.kframework.compile.transformers.DesugarStreams;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.FreezeUserFreezers;
import org.kframework.compile.transformers.FreshCondToFreshVar;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveBinder;
import org.kframework.compile.transformers.ResolveBlockingInput;
import org.kframework.compile.transformers.ResolveBuiltins;
import org.kframework.compile.transformers.ResolveFreshVarMOS;
import org.kframework.compile.transformers.ResolveFunctions;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveSyntaxPredicates;
import org.kframework.compile.transformers.StrictnessToContexts;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ColorSetting;
import org.kframework.main.FirstStep;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.Stopwatch;

import java.awt.Color;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

public class KoreBackend extends BasicBackend {
  public KoreBackend(Stopwatch sw, Context context) {
    super(sw, context);
  }

  @Override
  public void run(Definition toKore) throws IOException {
      
      try {
        toKore = this.getCompilationSteps().compile(toKore, this.getDefaultStep());
    } catch (CompilerStepDone e) {
        // TODO Auto-generated catch block
        toKore = (Definition) e.getResult();
    }
      KilTransformer trans = new KilTransformer(context);
      HashMap<String,PrintWriter> fileTable = new HashMap<String,PrintWriter>();
      for(int i = 0; i < toKore.getItems().size(); ++i){
          
          if(!fileTable.containsKey(((toKore.getItems().get(i)).getFilename()))){
              
              fileTable.put((toKore.getItems().get(i)).getFilename(), 
                      new PrintWriter(((toKore.getItems().get(i)).getFilename().substring(0, 
                              (toKore.getItems().get(i)).getFilename().length()-2))+".kore"));
              }
      }
      
      for(int i = 0; i < toKore.getItems().size(); ++i){

          fileTable.get((toKore.getItems().get(i)).getFilename()).println(trans.kilToKore(((toKore.getItems().get(i)))));
      }
      
      ArrayList<PrintWriter> toClosedFiles = new ArrayList<PrintWriter>(fileTable.values());
      
      for(int i = 0; i < toClosedFiles.size(); ++i){
          
          toClosedFiles.get(i).close();
      }
  }

  @Override
  public String getDefaultStep() {
      return "LastStep";
  }
  
  @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        steps.add(new FirstStep(this, context));
        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        steps.add(new RemoveBrackets(context));
        steps.add(new AddEmptyLists(context));
        steps.add(new RemoveSyntacticCasts(context));
//        steps.add(new EnforceInferredSorts(context));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context), context));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));
        steps.add(new StrictnessToContexts(context));
        steps.add(new FreezeUserFreezers(context));
        steps.add(new ContextsToHeating(context));
        steps.add(new AddSupercoolDefinition(context));
        steps.add(new AddHeatingConditions(context));
        steps.add(new AddSuperheatRules(context));
        steps.add(new DesugarStreams(context));
        steps.add(new ResolveFunctions(context));
        steps.add(new AddKCell(context));
        steps.add(new AddStreamCells(context));
        steps.add(new AddSymbolicK(context));
        steps.add(new AddSemanticEquality(context));
        // steps.add(new ResolveFresh());
        steps.add(new FreshCondToFreshVar(context));
        steps.add(new ResolveFreshVarMOS(context));
        steps.add(new AddTopCellConfig(context));
        if (options.experimental.addTopCell) {
            steps.add(new AddTopCellRules(context));
        }
        steps.add(new ResolveBinder(context));
        steps.add(new ResolveAnonymousVariables(context));
        steps.add(new ResolveBlockingInput(context));
        steps.add(new AddK2SMTLib(context));
        steps.add(new AddPredicates(context));
        steps.add(new ResolveSyntaxPredicates(context));
        steps.add(new ResolveBuiltins(context));
        steps.add(new ResolveListOfK(context));
        steps.add(new FlattenSyntax(context));
        //steps.add(new LastStep(this, context));
        return steps;
    }
}

class KoreFilter extends BasicVisitor {
    
    protected Indenter indenter = new Indenter();
    private boolean inConfiguration = false;
    private int inTerm = 0;
    private ColorSetting color = ColorSetting.OFF;
    public static int TAB = 4;

    public KoreFilter(Context context) {
      this(false,ColorSetting.OFF,context);
    }

    public KoreFilter(boolean inConfiguration, ColorSetting color, org.kframework.kil.loader.Context context) {
        super(context);
        this.inConfiguration = inConfiguration;
        this.color = color;
        this.inTerm = 0;
        this.indenter.setWidth(500);
    }
    
    public String getResult() {
        String a = indenter.toString();
        this.clear();
        return a;
    }
    
    public void clear(){
        
        indenter=new Indenter();
        this.indenter.setWidth(500);
    }

    @Override
    public String getName() {
        return "KoreFilter";
    }
    
    @Override
    public Void visit(Ambiguity node, Void _) {

        indenter.write("amb(");
        for (int i = 0; i < node.getContents().size() ; ++i){
            Term term=node.getContents().get(i);
            if (term != null){
                this.visitNode(term);
                if(i!=node.getContents().size()-1){
                    indenter.write(",");
                }
            }
        }
        indenter.write(")");
        return null;
    }
    
    @Override
    public Void visit(Attribute node, Void _) {
        indenter.write(" "+node.getKey()+"("+node.getValue()+")");
        return null;
    }
    
    @Override
    public Void visit(Attributes node, Void _) {
        
        if(node.isEmpty()){
            return null;
        }
        indenter.write("[");
        for (int i = 0; i < node.getContents().size() ; ++i){
            Attribute term=node.getContents().get(i);
                this.visitNode(term);
                if(i!=node.getContents().size()-1){
                    indenter.write(", ");
            }
        }
        indenter.write("]");
        return null;
    }
    
    @Override
    public Void visit(BackendTerm node, Void _) {
        indenter.write(node.getValue());
        return null;
    }
    
    @Override
    public Void visit(Collection node, Void _) {
        
        if(node.getContents().size()==0){
            indenter.write("."+node.getSort());
            return null;
        }
        
        for(int i = 0;i < node.getContents().size(); ++i){
            Term term = node.getContents().get(i);
            this.visitNode(term);
        }
        return null;
    }
    
    @Override
    public Void visit(BagItem node, Void _) {
        this.visitNode(node.getItem());
        return null;
    }
    
    @Override
    public Void visit(Token node, Void _) {
        indenter.write("#token(\"" + node.tokenSort() + "\", \"" + node.value() + "\")");
        return null;
    }
    
    @Override
    public Void visit(Bracket node, Void _) {
        indenter.write("(");
        this.visitNode(node.getContent());
        indenter.write(")");
        return null;
    }
    
    @Override
    public Void visit(Cast node, Void _) {
        indenter.write("(");
        this.visitNode(node.getContent());
        indenter.write(" :");
        if (node.isSyntactic()) {
            indenter.write(":");
        }
        indenter.write(node.getSort());
        indenter.write(")");
        return null;
    }
    
    @Override
    public Void visit(Cell cell, Void _) {

        String attributes = "";
        for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
            if (entry.getKey() != "ellipses") {
                attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
            }
        }
        String colorCode = "";
        Cell declaredCell = context.cells.get(cell.getLabel());
        if (declaredCell != null) {
            String declaredColor = declaredCell.getCellAttributes().get("color");
            if (declaredColor != null) {
                colorCode = ColorUtil.RgbToAnsi(declaredColor, color, Color.black);
                indenter.write(colorCode);
            }
        }

        indenter.write("<" + cell.getLabel() + attributes + ">");
        if (inConfiguration && inTerm == 0) {
            indenter.endLine();
            indenter.indent(TAB);
        } else {
            if (cell.hasLeftEllipsis()) {
                indenter.write("... ");
            } else {
                indenter.write(" ");
            }
        }
        if (!colorCode.equals("")) {
            indenter.write(ColorUtil.ANSI_NORMAL);
        }
        this.visitNode(cell.getContents());
        indenter.write(colorCode);
        if (inConfiguration && inTerm == 0) {
            indenter.endLine();
            indenter.unindent();
        } else {
            if (cell.hasRightEllipsis()) {
                indenter.write(" ...");
            } else {
                indenter.write(" ");
            }
        }
        indenter.write("</" + cell.getLabel() + ">");
        if (!colorCode.equals("")) {
            indenter.write(ColorUtil.ANSI_NORMAL);
        }

        return null;
    }
    
    @Override
    public Void visit(Configuration node, Void _) {
        indenter.write("  configuration ");
        this.visitNode(node.getBody()) ;
        indenter.write(" ");
        indenter.endLine();
        return null;
    }
    
    @Override
    public Void visit(org.kframework.kil.Context node, Void _) {
        indenter.write("  context ");
        this.visitNode(node.getBody());
        indenter.write(" ");
        this.visitNode(node.getAttributes());
        return null;
    }
    
    public Void visit(DataStructureSort node, Void _) {
        indenter.write(node.name());
        return null;
    }
    
    @Override
    public Void visit(Definition node, Void _) {
        for (DefinitionItem di : node.getItems()) {
            this.visitNode(di);
        }
        return null;
    }
    
    @Override
    public Void visit(Freezer node, Void _) {
        indenter.write("#freezer");
        this.visitNode(node.getTerm());
        indenter.write("(.KList)");
        return null;
    }
    
    @Override
    public Void visit(FreezerHole hole, Void _) {
        indenter.write("HOLE(" + hole.getIndex() + ")");
        return null;
    }
    
    @Override
    public Void visit(Hole hole, Void _) {
        indenter.write("HOLE");
        return null;
    }

    @Override
    public Void visit(Import node, Void _) {
        indenter.write("  imports " +node.getName());
        indenter.endLine();
        return null;
    }
  
    private void visitList(List<? extends ASTNode> nodes, String sep, String empty) {
        if (nodes.size() == 0) { this.indenter.write(empty); }
        else {
          for (int i = 0; i < nodes.size(); i++) {
            this.visitNode(nodes.get(i));
            if (i != (nodes.size() - 1)) { indenter.write(sep); }
          }
        }
      }

          @Override
        public Void visit(KSequence node, Void _) { 
            visitList(node.getContents(), " ~> ", ".K");
            return null;
        }

          @Override
        public Void visit(KList node, Void _) {
              visitList(node.getContents(), ", ", ".KList");
              return null;
        }

          @Override
        public Void visit(BoolBuiltin node, Void _) {
              this.indenter.write(node.value()); // TODO: true() vs #"true"()
              return null;
        }

        @Override
        public Void visit(IntBuiltin node, Void _) {
            this.indenter.write(node.value()); // TODO: true() vs #"true"()
            return null;
        }

        @Override
        public Void visit(StringBuiltin node, Void _) {
            this.indenter.write(node.value());
            return null;
        }
        
        @Override
        public Void visit(KApp node, Void _) {
              this.visitNode(node.getLabel());
              this.indenter.write("(");
              this.visitNode(node.getChild());
              this.indenter.write(")");
              return null;
        }

        @Override
        public Void visit(KLabelConstant node, Void _) {
            this.indenter.write(node.getLabel().replaceAll("\\(", "`(").replaceAll("\\)", "`)")); // TODO: escape the label
            return null;
        }
        
        @Override
        public Void visit(KInjectedLabel kInjectedLabel, Void _) {
            Term term = kInjectedLabel.getTerm();
            if (MetaK.isKSort(term.getSort())) {
                indenter.write(KInjectedLabel.getInjectedSort(term.getSort()));
                indenter.write("2KLabel ");
            } else {
                indenter.write("# ");
            }
            this.visitNode(term);
            return null;
        }
        
        @Override
        public Void visit(Lexical node, Void _) {
            this.indenter.write("Lexical{"+node.getLexicalRule()+"}");
            return null;
        }
  
        @Override
        public Void visit(ListTerminator node, Void _) {
            this.indenter.write(node.toString());
            return null;
        }
        
        @Override
        public Void visit(LiterateModuleComment node, Void _) {
            indenter.write(node.toString());
            return null;
        }
        
        @Override
        public Void visit(LiterateDefinitionComment node, Void _) {
            indenter.write(node.toString());
            return null;
        }
          
        @Override
        public Void visit(Module mod, Void _) {
            indenter.write("module " + mod.getName() + "\n");
            for (ModuleItem i : mod.getItems()){
                
                this.visitNode(i);
            }
            indenter.write("\nendmodule");
            return null;
        }

        @Override
        public Void visit(ParseError node, Void _) {
            indenter.write("Parse error: " + node.getMessage());
            return null;
        }
        
        @Override
        public Void visit(Production node, Void _) {
            for (ProductionItem i : node.getItems()){
                
                this.visitNode(i);
                indenter.write(" ");
            }
            return null;
        }
        
        @Override
        public Void visit(PriorityBlock node, Void _) {
            
            if (node.getAssoc() != null && !node.getAssoc().equals("")){
                indenter.write(node.getAssoc()+": ");
            }
            
            for (int i = 0; i < node.getProductions().size(); ++i){
                Production production = node.getProductions().get(i);
                this.visitNode(production);
                if(i!=node.getProductions().size()-1){
                    indenter.write("\n     | ");
                }
            }
            return null;
        }
        
        @Override
        public Void visit(PriorityBlockExtended node, Void _) {
            
            for (int i = 0; i < node.getProductions().size(); ++i){
                KLabelConstant production = node.getProductions().get(i);
                this.visitNode(production);
                if(i!=node.getProductions().size()-1){
                    indenter.write(" ");
                }
            }
            return null;
        }
        
        @Override
        public Void visit(PriorityExtended node, Void _) {
            
            indenter.write("  syntax priorities" );
            for (int i = 0; i < node.getPriorityBlocks().size(); ++i){
                PriorityBlockExtended production = node.getPriorityBlocks().get(i);
                this.visitNode(production);
                if(i!=node.getPriorityBlocks().size()-1){
                    indenter.write("\n     > ");
                }
            }
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(PriorityExtendedAssoc node, Void _) {
            
            indenter.write("  syntax "+node.getAssoc() );
            for (int i = 0; i < node.getTags().size(); ++i){
                KLabelConstant production = node.getTags().get(i);
                this.visitNode(production);
                if(i!=node.getTags().size()-1){
                    indenter.write(" ");
                }
            }
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Require node, Void _) {
            
            indenter.write(node.toString());
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Restrictions node, Void _) {
            indenter.write("  syntax ");
            if(node.getSort()!=null){
                this.visitNode(node.getSort());
            } else {
                this.visitNode(node.getTerminal());
            }
            indenter.write(" -/- " + node.getPattern());
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Rewrite rewrite, Void _) {
            this.visitNode(rewrite.getLeft());
            indenter.write(" => ");
            this.visitNode(rewrite.getRight());
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Rule node, Void _) {
            indenter.write("  rule ");

            if (node.getLabel() != null && !node.getLabel().equals(""))
                indenter.write("[" + node.getLabel() + "]: ");

            this.visitNode(node.getBody());
            indenter.write(" ");
            
            if (node.getRequires() != null) {
                indenter.write("requires ");
                this.visitNode(node.getRequires());
                indenter.write(" ");
            }
            if (node.getEnsures() != null) {
                indenter.write("requires ");
                this.visitNode(node.getEnsures());
                indenter.write(" ");
            }
            this.visitNode(node.getAttributes());
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Sentence node, Void _) {

            if (node.getLabel() != null && !node.getLabel().equals(""))
                indenter.write("[" + node.getLabel() + "]: ");

            this.visitNode(node.getBody());
            indenter.write(" ");
            
            if (node.getRequires() != null) {
                indenter.write("requires ");
                this.visitNode(node.getRequires());
                indenter.write(" ");
            }
            if (node.getEnsures() != null) {
                indenter.write("requires ");
                this.visitNode(node.getEnsures());
                indenter.write(" ");
            }
            this.visitNode(node.getAttributes());
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(Sort node, Void _) {
            indenter.write(node.toString());
            return null;
        }

        @Override
        public Void visit(StringSentence node, Void _) {
            indenter.write(node.toString());
            return null;
        }
        
        @Override
        public Void visit(Syntax node, Void _) {
            
            indenter.write("  syntax ");
            this.visitNode(node.getSort());
            indenter.write(" ::=");
            for (int i = 0; i < node.getPriorityBlocks().size(); ++i){
                PriorityBlock production = node.getPriorityBlocks().get(i);
                this.visitNode(production);
                if(i!=node.getPriorityBlocks().size()-1){
                    indenter.write("\n     > ");
                }
            }
            indenter.endLine();
            return null;
        }
        
        @Override
        public Void visit(TermComment node, Void _) {
            indenter.write(node.toString());
            return null;
        }
  
        @Override
        public Void visit(Terminal node, Void _) {
            indenter.write(node.toString());
            return null;
        }
        
        @Override
        public Void visit(UserList node, Void _) {
            indenter.write(node.toString());
            return null;
        }

        @Override
        public Void visit(Variable node, Void _) {
            this.indenter.write(node.getName() + ":" + node.getSort());
            return null;
        }
        
        @Override
        public Void visit(TermCons node, Void _){
            this.visitNode(new KApp(new KLabelConstant(node.getProduction().getKLabel()),new KList(node.getContents())));
            return null;
        }
}
