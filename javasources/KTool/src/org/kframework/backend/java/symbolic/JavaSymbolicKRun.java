package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.TopIndex;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.MapToLookupUpdate;
import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.*;
//import org.kframework.kil.KList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.*;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.utils.BinaryLoader;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;


import edu.uci.ics.jung.graph.DirectedGraph;


/**
 *
 *
 * @author AndreiS
 */
public class JavaSymbolicKRun implements KRun {

    private final Definition definition;
	private final Context context;
    private final KILtoBackendJavaKILTransformer transformer;

    public JavaSymbolicKRun(Context context) throws KRunExecutionException {
		this.context = context;
        transformer = new KILtoBackendJavaKILTransformer(context);

        try {
            /* load the definition from a binary file */
            InputStream inputStream = new BufferedInputStream(new FileInputStream(new File(
                    context.kompiled,
                    JavaSymbolicBackend.DEFINITION_FILENAME)));
            org.kframework.kil.Definition kilDefinition
                    = (org.kframework.kil.Definition) BinaryLoader.fromBinary(inputStream);
            definition = transformer.transformDefinition(kilDefinition);
            inputStream.close();

            if (definition == null) {
                throw new KRunExecutionException("cannot load definition");
            }

            /* initialize the builtin function table */
            BuiltinFunction.init(definition);
        } catch (FileNotFoundException e) {
            throw new KRunExecutionException(e);
        } catch (IOException e) {
            throw new KRunExecutionException(e);
        }
	}
	
    public static Cell wrap(Term t, String label) {
        Cell cell = new Cell(label,t);
        System.out.println("Content Kind: "+t.kind());
        return cell;
    }

    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(Term.of(cfg, definition), new TermContext(definition, new PortableFileSystem()));
//        try {
//            generate(definition, symbolicRewriter);
//        } catch (TransformerException e) {
//            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
//        }       java_symbolic_definition.bin
        ConstrainedTerm result = symbolicRewriter.rewrite(constrainedTerm);
        org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                new BackendJavaKILtoKILTranslation(context));
        return new KRunResult<KRunState>(new KRunState(kilTerm, context));
    }

    public void generate(Definition def, SymbolicRewriter sr) throws TransformerException{
        //make a copy of the definition
        Definition d = def;

        // fetch the rules from the definition
        Collection<Rule> rules = d.rules();
        Term rule1, rule2;
        for (int i = 0; i < rules.size(); i++) {

        }
        /*filter out rules whose RHS has KResults - they can't
          be used as the basis of test generation
          */
        Collection<Rule> nonResultRules = filterResults(rules);

        /*filter out heating and cooling rules - they also cannot be
        used as basis of test generation
         */

        Collection<Rule> nonResultOrHCRules = filterHeatersAndCoolers(nonResultRules);

//        org.kframework.kil.Term term;
//        List<org.kframework.kil.Term> list1 = new ArrayList<org.kframework.kil.Term>();
//        list1.add(new org.kframework.kil.Variable("B", "Bool"));
//        list1.add(new org.kframework.kil.Variable("S1", "Stmt"));
//        list1.add(new org.kframework.kil.Variable("S2", "Stmt"));
//        org.kframework.kil.Term kTerm = new KApp(org.kframework.kil.KLabelConstant.of("'if(_)_else_", context), new org.kframework.kil.KList(list1));
//        List<org.kframework.kil.Term> list2 = new ArrayList<org.kframework.kil.Term>();
//        list2.add(kTerm);
//        org.kframework.kil.Term kSequence = new org.kframework.kil.KSequence(list2);
//        // Term stateTerm = new Empty("Map");
//
//        org.kframework.kil.Bag bag = new org.kframework.kil.Bag();
//        bag.getContents().add(MetaK.wrap(kSequence, "k", org.kframework.kil.Cell.Ellipses.NONE));
//        // bag.getContents().add(MetaK.wrap(stateTerm, "state", Cell.Ellipses.NONE));
//        org.kframework.kil.Bag topBag = new org.kframework.kil.Bag();
//        topBag.getContents().add(MetaK.wrap(bag, "T", org.kframework.kil.Cell.Ellipses.NONE));
//        term = MetaK.wrap(topBag, MetaK.Constants.generatedTopCellLabel, org.kframework.kil.Cell.Ellipses.NONE);
//        System.out.println("Term: "+ term);
//
//        try {
//            term = (org.kframework.kil.Term) term.accept(new FlattenSyntax(context));
//            System.out.println("Term again: "+term);
//        } catch (org.kframework.kil.visitors.exceptions.TransformerException e) {
//            e.printStackTrace();
//        }
//
//        org.kframework.backend.java.kil.Term javaTerm = (org.kframework.backend.java.kil.Term) term.accept(
//                new KILtoBackendJavaKILTransformer(context));
//
//        System.out.println("Java term: "+javaTerm);
//        System.out.println("Java term variable set: "+javaTerm.variableSet());
//        System.out.println("Evaluated: "+javaTerm.evaluate(d));
//
//        KLabel label = KLabelConstant.of("'if(_)_else_", context);
////        KLabel iLabel = KLabelConstant.of(term, context);
//        ImmutableList
//        KList list = new KList(list1);
//
//        KItem item = new KItem("label", )

        /*Term term;
        List<Term> list1 = new ArrayList<Term>();
        list1.add(new Variable("B", "Bool"));
        list1.add(new Variable("S1", "Stmt"));
        list1.add(new Variable("S2", "Stmt"));
        ImmutableList<Term> imList = ImmutableList.copyOf(list1);
        KList kList = new KList(imList);

        Term kTerm = new KItem(KLabelConstant.of("'if(_)_else_", context), kList, context);
        System.out.println("KTerm: "+ kTerm.toString());
        List<Term> list2 = new ArrayList<Term>();
        list2.add(kTerm);
        Term kSequence = new KSequence(ImmutableList.copyOf(list2));
        System.out.println("KSequence: "+kSequence.toString());
//        // Term stateTerm = new Empty("Map");

        Cell kCell = wrap(kSequence, "k");

        CellCollection cellCollection1 = new CellCollection();
        cellCollection1.cellMap().put("k", kCell);

        // bag.getContents().add(MetaK.wrap(stateTerm, "state", Cell.Ellipses.NONE));
        Cell topCell = wrap(cellCollection1, "T");

        CellCollection cellCollection2 = new CellCollection();
        cellCollection2.cellMap().put("T", topCell);

        term = wrap(cellCollection2, "generatedTop");
        System.out.println("Term: "+term.toString()); */

//        Set<Variable> varSet = new HashSet<Variable>();
//        varSet.add(new Variable("B", "Bool"));
//        varSet.add(new Variable("S1", "Stmt"));
//        varSet.add(new Variable("S2", "Stmt"));
//
//
//
//        Map<Variable,Variable> varMap = Variable.getFreshSubstitution(varSet);
//
//        Variable boolVar = new Variable("B", "Bool");
//        ASTNode newBool = boolVar.accept(new SubstitutionTransformer(varMap,definition));
//        System.out.println("NewBool: "+ newBool.toString());
//
//        System.out.println("Var Map: "+ varMap);

//        try {
//            term = (Term) term.accept(new FlattenSyntax(context));
//            System.out.println("Term again: "+ term.toString());
//        } catch (TransformerException e) {
//            e.printStackTrace();
//        }

        /*SymbolicConstraint constraint = new SymbolicConstraint(definition);
        SymbolicUnifier unifier = new SymbolicUnifier(constraint,definition);*/

//        Object[] ruleArray = d.rules().toArray();
//        Rule firstRule = (Rule) ruleArray[0];
//        System.out.println("First Rule: "+ firstRule);

        /*for (Rule rule: d.rules()){
            System.out.println("LHS Rule 2: ");
            System.out.println(rule.leftHandSide());
            try{
                unifier.unify(term, rule.leftHandSide());
                System.out.println("Match: "+ rule);
                System.out.println("LHS Rule 2: ");
                System.out.println(rule.leftHandSide());
                System.out.println("");
            } catch(MatcherException e){
                System.out.println("Not a Match");
            }
        } */



//        try {
//            KRun kRun = new JavaSymbolicKRun(context);
//            kRun.run(term);
//        } catch (Exception e) {
//            e.printStackTrace();
//        }

    }

    private Collection<Rule> filterResults(Collection<Rule> rules){
        Collection<Rule> filtered = new ArrayList<Rule>();
        for (Rule rule: rules){
           Set<Variable> vars = rule.variableSet();

           if (!ruleHasKResult(vars)){
               filtered.add(rule);
           }
        }
        return filtered;
    }

    private Collection<Rule> filterHeatersAndCoolers(Collection<Rule> rules){
        Collection<Rule> filtered = new ArrayList<Rule>();
        for (Rule rule: rules){
            Collection<Term> conditions = rule.condition();
            if (!conditionHasKResult(conditions)){
                filtered.add(rule);
            }
        }
        return filtered;
    }

    private boolean ruleHasKResult(Set<Variable> vars){
        boolean hasKResult = false;
        for (Variable var: vars){
            if(var.sort().equals("KResult")){
                hasKResult = true;
                break;
            }
        }
        return hasKResult;
    }

    private boolean conditionHasKResult(Collection<Term> conditions){
        boolean hasKResult = false;
        for (Term term: conditions){
            if(term.toString().contains("isKResult")){
                hasKResult = true;
                break;
            }
        }
        return hasKResult;
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(org.kframework.kil.Module module) {
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();

        MapToLookupUpdate mapTransformer = new MapToLookupUpdate(context);

        try {
            List<Rule> rules = new ArrayList<Rule>();
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
                assert moduleItem instanceof org.kframework.kil.Rule;

                rules.add(transformer.transformRule(
                        (org.kframework.kil.Rule) moduleItem.accept(mapTransformer),
                        definition));
            }

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
                org.kframework.kil.Rule kilRule = (org.kframework.kil.Rule) moduleItem;
                org.kframework.kil.Term kilLeftHandSide
                        = ((org.kframework.kil.Rewrite) kilRule.getBody()).getLeft();
                org.kframework.kil.Term kilRightHandSide =
                        ((org.kframework.kil.Rewrite) kilRule.getBody()).getRight();
                org.kframework.kil.Term kilRequires = kilRule.getRequires();

                //TODO: Deal with Ensures
                
                /* rename rule variables */
                Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(
                        transformer.transformRule(
                                (org.kframework.kil.Rule) moduleItem.accept(mapTransformer),
                                definition).variableSet());

                TermContext termContext = new TermContext(definition, new PortableFileSystem());
                SymbolicConstraint initialConstraint = new SymbolicConstraint(termContext);
                //initialConstraint.addAll(rule.condition());
                initialConstraint.add(
                        transformer.transformTerm(kilRequires, definition),
                        BoolToken.TRUE);
                ConstrainedTerm initialTerm = new ConstrainedTerm(
                        transformer.transformTerm(kilLeftHandSide, definition).substitute(
                                freshSubstitution,
                                termContext),
                        initialConstraint.substitute(freshSubstitution, termContext),
                        termContext);

                org.kframework.kil.Rule kilDummyRule = new org.kframework.kil.Rule(
                        kilRightHandSide,
                        MetaK.kWrap(org.kframework.kil.KSequence.EMPTY, "k"),
                        context);
                Rule dummyRule = transformer.transformRule(
                        (org.kframework.kil.Rule) kilDummyRule.accept(mapTransformer),
                        definition);
                ConstrainedTerm targetTerm = new ConstrainedTerm(
                        dummyRule.leftHandSide().substitute(freshSubstitution, termContext),
                        dummyRule.lookups().substitute(freshSubstitution, termContext),
                        new SymbolicConstraint(termContext),
                        termContext);

                proofResults.addAll(symbolicRewriter.proveRule(initialTerm, targetTerm, rules));
            }

            return null;
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
    }

	@Override
	public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        FileSystem fs = new PortableFileSystem();
        TermContext termContext = new TermContext(definition, fs);
        ConstrainedTerm initialTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);
        ConstrainedTerm targetTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);


        List<Rule> claims = Collections.emptyList();

        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<ConstrainedTerm> hits = symbolicRewriter.search(initialTerm, targetTerm, claims, bound, depth);


        for (ConstrainedTerm result :hits ) {

            org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                    new BackendJavaKILtoKILTranslation(context));

            searchResults.add(new SearchResult(
                    new KRunState(kilTerm, context),
                    Collections.singletonMap("B:Bag", kilTerm),
                    compilationInfo,
                    context));
        }

        return new KRunResult<SearchResults>(new SearchResults(
                searchResults,
                null,
                true,
                context));
    }

    public KRunResult<GeneratorResults> generate(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        TermContext termContext = new TermContext(definition, new PortableFileSystem());
        ConstrainedTerm initialTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);
        ConstrainedTerm targetTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);


        List<Rule> claims = Collections.emptyList();
        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<GeneratorResult> generatedPrograms = new ArrayList<GeneratorResult>();

        List<ConstrainedTerm> hits = symbolicRewriter.search(initialTerm, targetTerm, claims, bound, depth, true);

        for (ConstrainedTerm result :hits ) {
            //reconstruct the generated program
            Term pgm = constructProgram(result,Term.of(cfg,definition));

            org.kframework.kil.Term pgmTerm =  (org.kframework.kil.Term)  pgm.accept(
                    new BackendJavaKILtoKILTranslation(context));

            org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                    new BackendJavaKILtoKILTranslation(context));

            generatedPrograms.add(new GeneratorResult(
                    new KRunState(kilTerm, context),
                    Collections.singletonMap("B:Bag", kilTerm),
                    compilationInfo,
                    context,
                    pgmTerm));
        }

        return new KRunResult<GeneratorResults>(new GeneratorResults(
                generatedPrograms,
                null,
                true,
                context));
    }

    private Term constructProgram(ConstrainedTerm term, Term config){
//        Term pgm = new ConstrainedTerm(term,definition);
        SymbolicConstraint constraint = term.constraint();
        Term pgm = config.substitute(constraint.substitution(),term.termContext());
        return pgm;
    }

    @Override
    public KRunProofResult<DirectedGraph<KRunState, Transition>> modelCheck(
            org.kframework.kil.Term formula,
            org.kframework.kil.Term cfg) throws KRunExecutionException {
        throw new UnsupportedOperationException("--ltlmc");
    }

    @Override
    public KRunResult<KRunState> step(org.kframework.kil.Term cfg, int steps)
            throws KRunExecutionException {
        throw new UnsupportedOperationException("--debug");
    }

    @Override
    public KRunDebugger debug(org.kframework.kil.Term cfg) {
        throw new UnsupportedOperationException("--debug");
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        throw new UnsupportedOperationException("--debug");
    }

	@Override
	public void setBackendOption(String key, Object value) {
	}

}
