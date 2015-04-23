// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser;

import com.google.inject.Inject;
import org.apache.commons.codec.binary.Base64InputStream;
import org.apache.commons.io.input.ReaderInputStream;
import org.kframework.attributes.Source;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenTerms;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.definition.Module;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.ResolveVariableAttribute;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.kore.convertors.KOREtoKIL;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import scala.Tuple2;
import scala.util.Either;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import java.util.Set;

public class ProgramLoader {

    private final BinaryLoader loader;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final TermLoader termLoader;
    private final FileUtil files;

    @Inject
    ProgramLoader(
            BinaryLoader loader,
            Stopwatch sw,
            KExceptionManager kem,
            TermLoader termLoader,
            FileUtil files) {
        this.loader = loader;
        this.sw = sw;
        this.kem = kem;
        this.termLoader = termLoader;
        this.files = files;
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

        String parsed = org.kframework.parser.concrete.DefinitionLocalKParser.ParseProgramString(content, startSymbol.toString(), files.resolveKompiled("."));
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
    public Term processPgm(Reader content, Source source, Sort startSymbol,
            Context context, ParserType whatParser) throws ParseFailedException {
        sw.printIntermediate("Importing Files");
        if (!context.getAllSorts().contains(startSymbol)) {
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    "The start symbol must be declared in the definition. Found: " + startSymbol));
        }

        ASTNode out;
        if (whatParser == ParserType.GROUND) {
            out = termLoader.parseCmdString(FileUtil.read(content), source, startSymbol);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context, kem).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
        } else if (whatParser == ParserType.RULES) {
            out = termLoader.parsePattern(FileUtil.read(content), source, startSymbol);
            out = new RemoveBrackets(context).visitNode(out);
            out = new AddEmptyLists(context, kem).visitNode(out);
            out = new RemoveSyntacticCasts(context).visitNode(out);
            out = new ResolveAnonymousVariables(context).visitNode(out);
            out = new FlattenTerms(context).visitNode(out);
            out = ((Sentence) out).getBody();
        } else if (whatParser == ParserType.BINARY) {
            try (InputStream in = new Base64InputStream(new ReaderInputStream(content))) {
                out = loader.loadOrDie(Term.class, in, source.toString());
            } catch (IOException e) {
                throw KEMException.internalError("Error reading from binary file", e);
            }
        } else if (whatParser == ParserType.NEWPROGRAM) {
            Definition def = loader.loadOrDie(Definition.class, files.resolveKompiled("definition-concrete.bin"));
            org.kframework.definition.Definition koreDef = new KILtoKORE(context, true, false).apply(def);
            Module synMod = koreDef.getModule(def.getMainSyntaxModule()).get();
            ParseInModule parser = new ParseInModule(new RuleGrammarGenerator(koreDef).getProgramsGrammar(synMod));
            Tuple2<Either<Set<ParseFailedException>, org.kframework.parser.Term>, Set<ParseFailedException>> parsed
                    = parser.parseString(FileUtil.read(content), startSymbol.getName(), source);
            for (ParseFailedException warn : parsed._2()) {
                kem.addKException(warn.getKException());
            }
            if (parsed._1().isLeft()) {
                for (ParseFailedException k : parsed._1().left().get())
                    kem.addKException(k.getKException());
                throw parsed._1().left().get().iterator().next();
            }

            out = new KOREtoKIL().convertK(TreeNodesToKORE.apply(parsed._1().right().get()));
        } else {
            out = loadPgmAst(FileUtil.read(content), source, startSymbol, context);
            out = new ResolveVariableAttribute(context).visitNode(out);
        }
        sw.printIntermediate("Parsing Program");

        return (Term) out;
    }

}
