package org.kframework.krun;

import java.io.File;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CheckBinaryPrecedenceFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewriteSortFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
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

import com.thoughtworks.xstream.XStream;

public class PatternParser {
	private static boolean initialized = false;

	public static void initParser() {
		File tbl = new File(K.kdir + "/def/Concrete.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTbl(tbl.getAbsolutePath());

		if (!DefinitionHelper.initialized) {
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			org.kframework.kil.Definition javaDef = (org.kframework.kil.Definition) xstream.fromXML(new File(K.kdir + "/defx.xml"));
			// This is essential for generating maude
			javaDef.preprocess();
		}

		initialized = true;
		// TODO: save outDef somewhere - maybe you will need it later
	}

	public static ASTNode getKastTerm(String pattern) {
		if (!initialized)
			initParser();

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString("rule " + pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), "Command line pattern");
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, K.kdir + "/pattern.xml");

		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		try {
			config = config.accept(new SentenceVariablesFilter());
			config = config.accept(new CellEndLabelFilter());
			config = config.accept(new CellTypesFilter());
			config = config.accept(new CorrectRewritePriorityFilter());
			config = config.accept(new CorrectKSeqFilter());
			config = config.accept(new CheckBinaryPrecedenceFilter());
			// config = config.accept(new InclusionFilter(localModule));
			config = config.accept(new VariableTypeInferenceFilter());
			config = config.accept(new AmbDuplicateFilter());
			config = config.accept(new TypeSystemFilter());
			config = config.accept(new PriorityFilter());
			config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
			config = config.accept(new TypeInferenceSupremumFilter());
			config = config.accept(new PreferAvoidFilter());
			config = config.accept(new FlattenListsFilter());
			config = config.accept(new CorrectRewriteSortFilter());
			// last resort disambiguation
			config = config.accept(new AmbFilter());
		} catch (TransformerException e) {
			String msg = "Cannot parse pattern: " + e.getLocalizedMessage();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, config.getFilename(), config.getLocation()));
		}
		return config;
	}
}
