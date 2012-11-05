package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewriteSortFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitFileCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
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

public class ParseRulesFilter extends BasicTransformer {
	public ParseRulesFilter() {
		super("Parse Configurations");
	}

	public ASTNode transform(StringSentence ss) throws TransformerException {
		if (ss.getType().equals(Constants.RULE) || ss.getType().equals(Constants.CONTEXT)) {
			try {
				String parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(ss.getContent());
				Document doc = XmlLoader.getXMLDoc(parsed);

				// replace the old xml node with the newly parsed sentence
				Node xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
				XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(ss.getLocation(), 0), XmlLoader.getLocNumber(ss.getLocation(), 1));
				XmlLoader.addFilename(xmlTerm, ss.getFilename());
				XmlLoader.reportErrors(doc, ss.getType());

				ASTNode config = JavaClassesFactory.getTerm((Element) xmlTerm);

				// disambiguate configs

				config = config.accept(new SentenceVariablesFilter());
				config = config.accept(new CellTypesFilter());
				config = config.accept(new CorrectRewritePriorityFilter());
				config = config.accept(new CorrectKSeqFilter());
				config = config.accept(new BestFitFilter(new GetFitnessUnitFileCheckVisitor()));
				config = config.accept(new VariableTypeInferenceFilter());
				config = config.accept(new AmbDuplicateFilter());
				config = config.accept(new TypeSystemFilter());
				config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
				config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
				config = config.accept(new TypeInferenceSupremumFilter());
				config = config.accept(new FlattenListsFilter());
				config = config.accept(new CorrectRewriteSortFilter());
				// last resort disambiguation
				config = config.accept(new AmbFilter());

				return config;
			} catch (Exception e) {
				e.printStackTrace();
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse configuration: " + e.getLocalizedMessage(), ss.getFilename(), ss.getLocation()));
			}
		}
		return ss;
	}
}
