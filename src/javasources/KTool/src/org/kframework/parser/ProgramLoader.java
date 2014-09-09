// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenTerms;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.ResolveVariableAttribute;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete2.MakeConsList;
import org.kframework.parser.concrete2.Parser;
import org.kframework.parser.concrete2.Parser.ParseError;
import org.kframework.parser.concrete2.TreeCleanerVisitor;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class ProgramLoader {

    /**
     * Load program file to ASTNode.
     *
     * @param kappize
     *            If true, then apply KAppModifier to AST.
     */
    public static ASTNode loadPgmAst(String content, Source source, Boolean kappize, Sort startSymbol, Context context)
            throws ParseFailedException {
        // ------------------------------------- import files in Stratego
        ASTNode out;

        org.kframework.parser.concrete.KParser.ImportTblPgm(context.kompiled);
        String parsed = org.kframework.parser.concrete.KParser.ParseProgramString(content, startSymbol.toString());
        Document doc = XmlLoader.getXMLDoc(parsed);

        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);
        JavaClassesFactory.startConstruction(context);
        out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        out = new PriorityFilter(context).visitNode(out);
        out = new PreferAvoidFilter(context).visitNode(out);
        out = new NormalizeASTTransformer(context).visitNode(out);
        out = new AmbFilter(context).visitNode(out);
        out = new RemoveBrackets(context).visitNode(out);

        if (kappize)
            out = new FlattenTerms(context).visitNode(out);

        return out;
    }

    public static ASTNode loadPgmAst(String content, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        return loadPgmAst(content, source, true, startSymbol, context);
    }

    /**
     * Print maudified program to standard output.
     *
     * Save it in kompiled cache under pgm.maude.
     */
    public static Term processPgm(byte[] content, Source source, Sort startSymbol,
            Context context, ParserType whatParser) throws ParseFailedException {
        Stopwatch.instance().printIntermediate("Importing Files");
        if (!context.definedSorts.contains(startSymbol)) {
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    "The start symbol must be declared in the definition. Found: " + startSymbol));
        }

        ASTNode out;
        if (whatParser == ParserType.GROUND) {
            org.kframework.parser.concrete.KParser.ImportTblGround(context.kompiled);
            out = DefinitionLoader.parseCmdString(new String(content), source, startSymbol, context);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
        } else if (whatParser == ParserType.RULES) {
            org.kframework.parser.concrete.KParser.ImportTblRule(context.kompiled);
            out = DefinitionLoader.parsePattern(new String(content), source, startSymbol, context);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            try {
                out = new RuleCompilerSteps(context).compile(
                        new Rule((Sentence) out),
                        null);
            } catch (CompilerStepDone e) {
                out = (ASTNode) e.getResult();
            }
            out = ((Rule) out).getBody();
        } else if (whatParser == ParserType.BINARY) {
            try (ByteArrayInputStream in = new ByteArrayInputStream(content)) {
                out = BinaryLoader.instance().loadOrDie(Term.class, in);
            } catch (IOException e) {
                GlobalSettings.kem.registerInternalError("Error reading from binary file", e);
                throw new AssertionError("unreachable");
            }
        } else if (whatParser == ParserType.NEWPROGRAM) {
            // load the new parser
            // TODO(Radu): after the parser is in a good enough shape, replace the program parser
            // TODO(Radu): (the default one) with this branch of the 'if'
            Grammar grammar = BinaryLoader.instance().loadOrDie(Grammar.class, context.kompiled.getAbsolutePath() + "/pgm/newParser.bin");

            String contentString = new String(content);
            Parser parser = new Parser(contentString);
            out = parser.parse(grammar.get(startSymbol.toString()), 0);
            if (context.globalOptions.debug)
                System.err.println("Raw: " + out + "\n");
            try {
                out = new TreeCleanerVisitor(context).visitNode(out);
                out = new MakeConsList(context).visitNode(out);
                if (context.globalOptions.debug)
                    System.err.println("Clean: " + out + "\n");
                out = new PriorityFilter(context).visitNode(out);
                out = new PreferAvoidFilter(context).visitNode(out);
                if (context.globalOptions.debug)
                    System.err.println("Filtered: " + out + "\n");
                out = new AmbFilter(context).visitNode(out);
                out = new RemoveBrackets(context).visitNode(out);
                out = new FlattenTerms(context).visitNode(out);
            } catch (ParseFailedException te) {
                ParseError perror = parser.getErrors();

                String msg = contentString.length() == perror.position ?
                    "Parse error: unexpected end of file." :
                    "Parse error: unexpected character '" + contentString.charAt(perror.position) + "'.";
                Location loc = new Location(perror.line, perror.column,
                                            perror.line, perror.column + 1);
                throw new ParseFailedException(new KException(
                        ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, msg, source, loc));
            }
            out = new ResolveVariableAttribute(context).visitNode(out);
        } else {
            out = loadPgmAst(new String(content), source, startSymbol, context);
            out = new ResolveVariableAttribute(context).visitNode(out);
        }
        Stopwatch.instance().printIntermediate("Parsing Program");

        return (Term) out;
    }
}
