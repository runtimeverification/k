// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import org.apache.commons.codec.binary.Base64InputStream;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenTerms;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.ResolveVariableAttribute;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.MakeConsList;
import org.kframework.parser.concrete2.Parser;
import org.kframework.parser.concrete2.Parser.ParseError;
import org.kframework.parser.concrete2.TreeCleanerVisitor;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.google.inject.Inject;

public class ProgramLoader {

    private final BinaryLoader loader;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final GlobalOptions globalOptions;
    private final TermLoader termLoader;

    @Inject
    ProgramLoader(
            BinaryLoader loader,
            Stopwatch sw,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            TermLoader termLoader) {
        this.loader = loader;
        this.sw = sw;
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.termLoader = termLoader;
    }

    /**
     * Load program file to ASTNode.
     *
     * @param kappize
     *            If true, then apply KAppModifier to AST.
     */
    public ASTNode loadPgmAst(String content, Source source, Boolean kappize, Sort startSymbol, Context context)
            throws ParseFailedException {
        // ------------------------------------- import files in Stratego
        ASTNode out;

        String parsed = org.kframework.parser.concrete.DefinitionLocalKParser.ParseProgramString(content, startSymbol.toString(), context.files.resolveKompiled("."));
        Document doc = XmlLoader.getXMLDoc(parsed);

        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);
        out = new  JavaClassesFactory(context).getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

        out = new PriorityFilter(context).visitNode(out);
        out = new PreferAvoidFilter(context).visitNode(out);
        out = new NormalizeASTTransformer(context, kem).visitNode(out);
        out = new AmbFilter(context, kem).visitNode(out);
        out = new RemoveBrackets(context).visitNode(out);

        if (kappize)
            out = new FlattenTerms(context).visitNode(out);

        return out;
    }

    public ASTNode loadPgmAst(String content, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        return loadPgmAst(content, source, true, startSymbol, context);
    }

    /**
     * Print maudified program to standard output.
     *
     * Save it in kompiled cache under pgm.maude.
     */
    public Term processPgm(String content, Source source, Sort startSymbol,
            Context context, ParserType whatParser) throws ParseFailedException {
        sw.printIntermediate("Importing Files");
        if (!context.getAllSorts().contains(startSymbol)) {
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    "The start symbol must be declared in the definition. Found: " + startSymbol));
        }

        ASTNode out;
        if (whatParser == ParserType.GROUND) {
            out = termLoader.parseCmdString(content, source, startSymbol, context);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context, kem).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
        } else if (whatParser == ParserType.RULES) {
            out = termLoader.parsePattern(content, source, startSymbol, context);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context, kem).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            out = new ResolveAnonymousVariables(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
            out = ((Sentence) out).getBody();
        } else if (whatParser == ParserType.BINARY) {
            try (InputStream in = new Base64InputStream(new ByteArrayInputStream(content.getBytes()))) {
                out = loader.loadOrDie(Term.class, in);
            } catch (IOException e) {
                throw KExceptionManager.internalError("Error reading from binary file", e);
            }
        } else if (whatParser == ParserType.NEWPROGRAM) {
            // load the new parser
            // TODO(Radu): after the parser is in a good enough shape, replace the program parser
            // TODO(Radu): (the default one) with this branch of the 'if'
            Grammar grammar = loader.loadOrDie(Grammar.class, context.files.resolveKompiled("newParser.bin"));

            out = newParserParse(content, grammar.get(startSymbol.toString()), source, context);
            out = new AmbFilter(context, kem).visitNode(out);
            out = new RemoveBrackets(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
            out = new ResolveVariableAttribute(context).visitNode(out);
        } else {
            out = loadPgmAst(content, source, startSymbol, context);
            out = new ResolveVariableAttribute(context).visitNode(out);
        }
        sw.printIntermediate("Parsing Program");

        return (Term) out;
    }

    public Term parseInModule(String content, Source source, Sort startSymbol,
                                  String moduleName, Context context) throws ParseFailedException {
        @SuppressWarnings("unchecked")
        Map<String, Grammar> grammars = loader.loadOrDie(Map.class, context.files.resolveKompiled("newModuleParsers.bin"));

        ASTNode out;
        Grammar grammar = grammars.get(moduleName);
        if (grammar == null) {
            String msg = "Could not find module: " + moduleName + " when trying to parseInModule.";
            throw new ParseFailedException(new KException(
                    ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, source, null));
        }
        NonTerminal nt = grammar.get(startSymbol.toString());
        if (nt == null) {
            String msg = "Could not find start symbol: " + startSymbol + " when trying to parseInModule " + moduleName;
            throw new ParseFailedException(new KException(
                    ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, source, null));
        }
        out = newParserParse(content, nt, source, context);
        out = new AmbFilter(context, kem).visitNode(out);
        out = new RemoveBrackets(context).visitNode(out);
        out = new FlattenTerms(context).visitNode(out);
        out = new ResolveVariableAttribute(context).visitNode(out);
        return (Term) out;
    }

    /**
     *
     * @param content String to be parsed.
     * @param nt      Start symbol.
     * @param source  Source information for error reporting and term annotation.
     * @param context The context in which to disambiguate the AST.
     * @return AST representation of the input.
     * @throws ParseFailedException In case the parse failed.
     */
    public static ASTNode newParserParse(String content,
                                         NonTerminal nt,
                                         Source source,
                                         Context context) throws ParseFailedException {
        Parser parser = new Parser(content);
        ASTNode out;
        out = parser.parse(nt, 0);
        if (context.globalOptions.debug)
            System.err.println("Raw: " + out + "\n");
        try {
            // only the unexpected character type of errors should be checked in this block
            out = new TreeCleanerVisitor().visitNode(out);
        } catch (ParseFailedException te) {
            ParseError perror = parser.getErrors();

            String msg = content.length() == perror.position ?
                    "Parse error: unexpected end of file." :
                    "Parse error: unexpected character '" + content.charAt(perror.position) + "'.";
            Location loc = new Location(perror.line, perror.column,
                    perror.line, perror.column + 1);
            throw new ParseFailedException(new KException(
                    ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, source, loc));
        }
        out = new MakeConsList().visitNode(out);
        if (context.globalOptions.debug)
            System.err.println("Clean: " + out + "\n");
        out = new PriorityFilter(context).visitNode(out);
        out = new PreferAvoidFilter(context).visitNode(out);
        if (context.globalOptions.debug)
            System.err.println("Filtered: " + out + "\n");
        return out;
    }
}
