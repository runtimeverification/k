package org.kframework.parser.generator;

import org.kframework.compile.checks.CheckListOfKDeprecation;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.CollectStartSymbolPgmVisitor;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.InclusionFilter;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseConfigsFilter extends BasicTransformer {
	public ParseConfigsFilter(DefinitionHelper definitionHelper) {
		super("Parse Configurations", definitionHelper);
	}

	String localModule = null;

	@Override
	public ASTNode transform(Module m) throws TransformerException {
		localModule = m.getName();
		ASTNode rez = super.transform(m);
		rez.accept(new CollectStartSymbolPgmVisitor(definitionHelper));
		return rez;
	}

	public ASTNode transform(StringSentence ss) throws TransformerException {
		if (ss.getType().equals(Constants.CONFIG)) {
			try {
				ASTNode config = null;
				String parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(ss.getContent());
				Document doc = XmlLoader.getXMLDoc(parsed);

				// replace the old xml node with the newly parsed sentence
				Node xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
				XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(ss.getLocation(), 0), XmlLoader.getLocNumber(ss.getLocation(), 1));
				XmlLoader.addFilename(xmlTerm, ss.getFilename());
				XmlLoader.reportErrors(doc, "configuration");

				config = JavaClassesFactory.getTerm((Element) xmlTerm);
				if (GlobalSettings.fastKast) {
					// TODO: load directly from ATerms
					System.out.println("Not implemented yet: org.kframework.parser.generator.ParseConfigsFilter");
					System.exit(0);
					config = null;
					// ATerm parsed = org.kframework.parser.concrete.KParser.ParseKConfigStringAst(ss.getContent());
					// config = JavaClassesFactory.getTerm((IStrategoAppl) parsed);
				}

				new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(definitionHelper), definitionHelper).check(config);
				// disambiguate configs
				config = config.accept(new SentenceVariablesFilter(definitionHelper));
				config = config.accept(new CellEndLabelFilter(definitionHelper));
				config = config.accept(new InclusionFilter(localModule, definitionHelper));
				// config = config.accept(new CellTypesFilter()); not the case on configs
				// config = config.accept(new CorrectRewritePriorityFilter());
				config = config.accept(new CorrectKSeqFilter(definitionHelper));
				config = config.accept(new CorrectCastPriorityFilter(definitionHelper));
				// config = config.accept(new CheckBinaryPrecedenceFilter());
				config = config.accept(new VariableTypeInferenceFilter(definitionHelper));
				config = config.accept(new AmbDuplicateFilter(definitionHelper));
				config = config.accept(new TypeSystemFilter(definitionHelper));
				config = config.accept(new PriorityFilter(definitionHelper));
				config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(definitionHelper), definitionHelper));
				config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(definitionHelper), definitionHelper));
				config = config.accept(new TypeInferenceSupremumFilter(definitionHelper));
				config = config.accept(new PreferAvoidFilter(definitionHelper));
				config = config.accept(new FlattenListsFilter(definitionHelper));
				config = config.accept(new AmbDuplicateFilter(definitionHelper));
				// last resort disambiguation
				config = config.accept(new AmbFilter(definitionHelper));

				return config;
			} catch (TransformerException te) {
				te.printStackTrace();
			} catch (Exception e) {
				String msg = "Cannot parse configuration: " + e.getLocalizedMessage();
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ss.getFilename(), ss.getLocation()));
			}
		}
		return ss;
	}
}
