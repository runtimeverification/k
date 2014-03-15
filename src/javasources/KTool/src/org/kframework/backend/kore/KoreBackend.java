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
        steps.add(new DesugarStreams(context, false));
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
        steps.add(new ResolveBlockingInput(context, false));
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
    public void visit(Ambiguity node) {

        indenter.write("amb(");
        for (int i = 0; i < node.getContents().size() ; ++i){
            Term term=node.getContents().get(i);
            if (term != null){
                term.accept(this);
                if(i!=node.getContents().size()-1){
                    indenter.write(",");
                }
            }
        }
        indenter.write(")");
    }
    
    @Override
    public void visit(Attribute node) {
        indenter.write(" "+node.getKey()+"("+node.getValue()+")");
    }
    
    @Override
    public void visit(Attributes node) {
        
        if(node.isEmpty()){
            return;
        }
        indenter.write("[");
        for (int i = 0; i < node.getContents().size() ; ++i){
            Attribute term=node.getContents().get(i);
                term.accept(this);
                if(i!=node.getContents().size()-1){
                    indenter.write(", ");
            }
        }
        indenter.write("]");
    }
    
    @Override
    public void visit(BackendTerm node) {
        indenter.write(node.getValue());
    }
    
    @Override
    public void visit(Collection node) {
        
        if(node.getContents().size()==0){
            indenter.write("."+node.getSort());
            return;
        }
        
        for(int i = 0;i < node.getContents().size(); ++i){
            Term term = node.getContents().get(i);
            term.accept(this);
        }
    }
    
    @Override
    public void visit(BagItem node) {
        node.getItem().accept(this);
    }
    
    @Override
    public void visit(Token node) {
        indenter.write("#token(\"" + node.tokenSort() + "\", \"" + node.value() + "\")");
    }
    
    @Override
    public void visit(Bracket node) {
        indenter.write("(");
        node.getContent().accept(this);
        indenter.write(")");
    }
    
    @Override
    public void visit(Cast node) {
        indenter.write("(");
        node.getContent().accept(this);
        indenter.write(" :");
        if (node.isSyntactic()) {
            indenter.write(":");
        }
        indenter.write(node.getSort());
        indenter.write(")");
    }
    
    @Override
    public void visit(Cell cell) {

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
                colorCode = ColorUtil.RgbToAnsi(ColorUtil.colors.get(declaredColor), color);
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
        cell.getContents().accept(this);
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

    }
    
    @Override
    public void visit(Configuration node) {
        indenter.write("  configuration ");
        node.getBody().accept(this) ;
        indenter.write(" ");
        indenter.endLine();
    }
    
    @Override
    public void visit(org.kframework.kil.Context node) {
        indenter.write("  context ");
        node.getBody().accept(this);
        indenter.write(" ");
        node.getAttributes().accept(this);
    }
    
    public void visit(DataStructureSort node) {
        indenter.write(node.name());
    }
    
    @Override
    public void visit(Definition node) {
        for (DefinitionItem di : node.getItems()) {
            di.accept(this);
        }
    }
    
    @Override
    public void visit(Freezer node) {
        indenter.write("#freezer");
        node.getTerm().accept(this);
        indenter.write("(.KList)");
    }
    
    @Override
    public void visit(FreezerHole hole) {
        indenter.write("HOLE(" + hole.getIndex() + ")");
    }
    
    @Override
    public void visit(Hole hole) {
        indenter.write("HOLE");
    }

    @Override
    public void visit(Import node) {
        indenter.write("  imports " +node.getName());
        indenter.endLine();
    }
  
    private void visitList(List<? extends ASTNode> nodes, String sep, String empty) {
        if (nodes.size() == 0) { this.indenter.write(empty); }
        else {
          for (int i = 0; i < nodes.size(); i++) {
            nodes.get(i).accept(this);
            if (i != (nodes.size() - 1)) { indenter.write(sep); }
          }
        }
      }

          @Override
        public void visit(KSequence node) { 
            visitList(node.getContents(), " ~> ", ".K");
        }

          @Override
        public void visit(KList node) {
              visitList(node.getContents(), ", ", ".KList");
        }

          @Override
        public void visit(BoolBuiltin node) {
              this.indenter.write(node.value()); // TODO: true() vs #"true"()
        }

        @Override
        public void visit(IntBuiltin node) {
            this.indenter.write(node.value()); // TODO: true() vs #"true"()
        }

        @Override
        public void visit(StringBuiltin node) {
            this.indenter.write(node.value());
        }
        
        @Override
        public void visit(KApp node) {
              node.getLabel().accept(this);
              this.indenter.write("(");
              node.getChild().accept(this);
              this.indenter.write(")");
        }

        @Override
        public void visit(KLabelConstant node) {
            this.indenter.write(node.getLabel().replaceAll("\\(", "`(").replaceAll("\\)", "`)")); // TODO: escape the label
        }
        
        @Override
        public void visit(KInjectedLabel kInjectedLabel) {
            Term term = kInjectedLabel.getTerm();
            if (MetaK.isKSort(term.getSort())) {
                indenter.write(KInjectedLabel.getInjectedSort(term.getSort()));
                indenter.write("2KLabel ");
            } else {
                indenter.write("# ");
            }
            term.accept(this);
        }
        
        @Override
        public void visit(Lexical node) {
            this.indenter.write("Lexical{"+node.getLexicalRule()+"}");
        }
  
        @Override
        public void visit(ListTerminator node) {
            this.indenter.write(node.toString());
        }
        
        @Override
        public void visit(LiterateModuleComment node) {
            indenter.write(node.toString());
        }
        
        @Override
        public void visit(LiterateDefinitionComment node) {
            indenter.write(node.toString());
        }
          
        @Override
        public void visit(Module mod) {
            indenter.write("module " + mod.getName() + "\n");
            for (ModuleItem i : mod.getItems()){
                
                i.accept(this);
            }
            indenter.write("\nendmodule");
        }

        @Override
        public void visit(ParseError node) {
            indenter.write("Parse error: " + node.getMessage());
        }
        
        @Override
        public void visit(Production node) {
            for (ProductionItem i : node.getItems()){
                
                i.accept(this);
                indenter.write(" ");
            }
        }
        
        @Override
        public void visit(PriorityBlock node) {
            
            if (node.getAssoc() != null && !node.getAssoc().equals("")){
                indenter.write(node.getAssoc()+": ");
            }
            
            for (int i = 0; i < node.getProductions().size(); ++i){
                Production production = node.getProductions().get(i);
                production.accept(this);
                if(i!=node.getProductions().size()-1){
                    indenter.write("\n     | ");
                }
            }
        }
        
        @Override
        public void visit(PriorityBlockExtended node) {
            
            for (int i = 0; i < node.getProductions().size(); ++i){
                KLabelConstant production = node.getProductions().get(i);
                production.accept(this);
                if(i!=node.getProductions().size()-1){
                    indenter.write(" ");
                }
            }
        }
        
        @Override
        public void visit(PriorityExtended node) {
            
            indenter.write("  syntax priorities" );
            for (int i = 0; i < node.getPriorityBlocks().size(); ++i){
                PriorityBlockExtended production = node.getPriorityBlocks().get(i);
                production.accept(this);
                if(i!=node.getPriorityBlocks().size()-1){
                    indenter.write("\n     > ");
                }
            }
            indenter.endLine();
        }
        
        @Override
        public void visit(PriorityExtendedAssoc node) {
            
            indenter.write("  syntax "+node.getAssoc() );
            for (int i = 0; i < node.getTags().size(); ++i){
                KLabelConstant production = node.getTags().get(i);
                production.accept(this);
                if(i!=node.getTags().size()-1){
                    indenter.write(" ");
                }
            }
            indenter.endLine();
        }
        
        @Override
        public void visit(Require node) {
            
            indenter.write(node.toString());
            indenter.endLine();
        }
        
        @Override
        public void visit(Restrictions node) {
            indenter.write("  syntax ");
            if(node.getSort()!=null){
                node.getSort().accept(this);
            } else {
                node.getTerminal().accept(this);
            }
            indenter.write(" -/- " + node.getPattern());
            indenter.endLine();
        }
        
        @Override
        public void visit(Rewrite rewrite) {
            rewrite.getLeft().accept(this);
            indenter.write(" => ");
            rewrite.getRight().accept(this);
            indenter.endLine();
        }
        
        @Override
        public void visit(Rule node) {
            indenter.write("  rule ");

            if (node.getLabel() != null && !node.getLabel().equals(""))
                indenter.write("[" + node.getLabel() + "]: ");

            node.getBody().accept(this);
            indenter.write(" ");
            
            if (node.getRequires() != null) {
                indenter.write("requires ");
                node.getRequires().accept(this);
                indenter.write(" ");
            }
            if (node.getEnsures() != null) {
                indenter.write("requires ");
                node.getEnsures().accept(this);
                indenter.write(" ");
            }
            node.getAttributes().accept(this);
            indenter.endLine();
        }
        
        @Override
        public void visit(Sentence node) {

            if (node.getLabel() != null && !node.getLabel().equals(""))
                indenter.write("[" + node.getLabel() + "]: ");

            node.getBody().accept(this);
            indenter.write(" ");
            
            if (node.getRequires() != null) {
                indenter.write("requires ");
                node.getRequires().accept(this);
                indenter.write(" ");
            }
            if (node.getEnsures() != null) {
                indenter.write("requires ");
                node.getEnsures().accept(this);
                indenter.write(" ");
            }
            node.getAttributes().accept(this);
            indenter.endLine();
        }
        
        @Override
        public void visit(Sort node) {
            indenter.write(node.toString());
        }

        @Override
        public void visit(StringSentence node) {
            indenter.write(node.toString());
        }
        
        @Override
        public void visit(Syntax node) {
            
            indenter.write("  syntax ");
            node.getSort().accept(this);
            indenter.write(" ::=");
            for (int i = 0; i < node.getPriorityBlocks().size(); ++i){
                PriorityBlock production = node.getPriorityBlocks().get(i);
                production.accept(this);
                if(i!=node.getPriorityBlocks().size()-1){
                    indenter.write("\n     > ");
                }
            }
            indenter.endLine();
        }
        
        @Override
        public void visit(TermComment node) {
            indenter.write(node.toString());
        }
  
        @Override
        public void visit(Terminal node) {
            indenter.write(node.toString());
        }
        
        @Override
        public void visit(UserList node) {
            indenter.write(node.toString());
        }

        @Override
        public void visit(Variable node) {
            this.indenter.write(node.getName() + ":" + node.getSort());
        }
        
        @Override
        public void visit(TermCons node){
            (new KApp(new KLabelConstant(node.getProduction().getKLabel()),new KList(node.getContents()))).accept(this);

        }
}
