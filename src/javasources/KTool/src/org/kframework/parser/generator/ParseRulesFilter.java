package org.kframework.parser.generator;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Formatter;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectConstantsTransformer;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.InclusionFilter;
import org.kframework.parser.concrete.disambiguate.MergeAmbFilter;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.utils.ReportErrorsVisitor;
import org.kframework.parser.utils.Sglr;
import org.kframework.utils.StringUtil;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseRulesFilter extends BasicTransformer {
    Formatter f;
    boolean checkInclusion = true;

    public ParseRulesFilter(Context context, boolean checkInclusion) {
        super("Parse Configurations", context);
        this.checkInclusion = checkInclusion;
        if (globalOptions.verbose)
            try {
                f = new Formatter(new File(context.dotk.getAbsolutePath() + "/timing.log"));
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
    }

    public ParseRulesFilter(Context context) {
        super("Parse Configurations", context);
        if (globalOptions.verbose)
            try {
                f = new Formatter(new File(context.dotk.getAbsolutePath() + "/timing.log"));
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
    }

    String localModule = null;

    @Override
    public ASTNode transform(Module m) throws TransformerException {
        localModule = m.getName();
        return super.transform(m);
    }

    public ASTNode transform(StringSentence ss) throws TransformerException {
        if (ss.getType().equals(Constants.RULE) || ss.getType().equals(Constants.CONTEXT)) {
            long startTime = System.currentTimeMillis();
            try {
                ASTNode config;

                if (experimentalParserOptions.fastKast) {
                    // TODO(RaduM): load directly from ATerms
                    ASTNode anode = Sglr.run_sglri(context.dotk.getAbsolutePath() + "/def/Concrete.tbl", "CondSentence", ss.getContent(), ss.getFilename());

                    int startLine = StringUtil.getStartLineFromLocation(ss.getContentLocation());
                    int startCol = StringUtil.getStartColFromLocation(ss.getContentLocation());
                    anode.accept(new UpdateLocationVisitor(context, startLine, startCol));
                    anode.accept(new ReportErrorsVisitor(context, "rule"));

                    Sentence st = (Sentence) anode;
                    if (ss.getType().equals(Constants.CONTEXT))
                        config = new org.kframework.kil.Context(st);
                    else if (ss.getType().equals(Constants.RULE))
                        config = new Rule(st);
                    else { // should not reach here
                        config = null;
                        assert false : "Only context and rules have been implemented.";
                    }

                    ((Sentence) config).setLabel(ss.getLabel());
                    //assert st.getAttributes() == null || st.getAttributes().isEmpty(); // attributes should have been parsed in Basic Parsing
                    ((Sentence) config).setAttributes(ss.getAttributes());
                } else {
                    String parsed = null;
                    if (ss.containsAttribute("kore")) {

                        long koreStartTime = System.currentTimeMillis();
                        parsed = org.kframework.parser.concrete.KParser.ParseKoreString(ss.getContent());
                        if (globalOptions.verbose)
                            System.out.println("Parsing with Kore: " + ss.getFilename() + ":" + ss.getLocation() + " - " + (System.currentTimeMillis() - koreStartTime));
                    } else
                        parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(ss.getContent());
                    Document doc = XmlLoader.getXMLDoc(parsed);

                    // replace the old xml node with the newly parsed sentence
                    Node xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
                    XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(ss.getContentLocation(), 0), XmlLoader.getLocNumber(ss.getContentLocation(), 1));
                    XmlLoader.addFilename(xmlTerm, ss.getFilename());
                    XmlLoader.reportErrors(doc, ss.getType());

                    if (ss.getType().equals(Constants.CONTEXT))
                        config = new org.kframework.kil.Context((Sentence) JavaClassesFactory.getTerm((Element) xmlTerm));
                    else if (ss.getType().equals(Constants.RULE))
                        config = new Rule((Sentence) JavaClassesFactory.getTerm((Element) xmlTerm));
                    else { // should not reach here
                        config = null;
                        assert false : "Only context and rules have been implemented.";
                    }
                    Sentence st = (Sentence) config;
                    assert st.getLabel().equals(""); // labels should have been parsed in Basic Parsing
                    st.setLabel(ss.getLabel());
                    //assert st.getAttributes() == null || st.getAttributes().isEmpty(); // attributes should have been parsed in Basic Parsing
                    st.setAttributes(ss.getAttributes());
                }
                // disambiguate rules
                if (config.getFilename().endsWith("test.k")) {
                    // this is just for testing. I put a breakpoint on the next line so I can get faster to the rule that I'm interested in
                    int a = 1;
                    a = a + 1;
                }

                config = config.accept(new SentenceVariablesFilter(context));
                config = config.accept(new CellEndLabelFilter(context));
                if (checkInclusion)
                    config = config.accept(new InclusionFilter(localModule, context));
                config = config.accept(new CellTypesFilter(context));
                config = config.accept(new CorrectRewritePriorityFilter(context));
                config = config.accept(new CorrectKSeqFilter(context));
                config = config.accept(new CorrectCastPriorityFilter(context));
                // config = config.accept(new CheckBinaryPrecedenceFilter());
                config = config.accept(new PriorityFilter(context));
                if (experimentalParserOptions.fastKast)
                    config = config.accept(new MergeAmbFilter(context));
                config = config.accept(new VariableTypeInferenceFilter(context));
                // config = config.accept(new AmbDuplicateFilter(context));
                // config = config.accept(new TypeSystemFilter(context));
                // config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context));
                // config = config.accept(new TypeInferenceSupremumFilter(context));
                config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context));
                config = config.accept(new PreferAvoidFilter(context));
                config = config.accept(new FlattenListsFilter(context));
                config = config.accept(new AmbDuplicateFilter(context));
                // last resort disambiguation
                config = config.accept(new AmbFilter(context));

                if (globalOptions.verbose) {
                    f.format("Parsing rule: Time: %6d Location: %s:%s\n", (System.currentTimeMillis() - startTime), ss.getFilename(), ss.getLocation());
                    f.flush();
                }
                return config;
            } catch (TransformerException te) {
                te.printStackTrace();
            } catch (Exception | Error e) {
                e.printStackTrace();
                String msg = "Cannot parse sentence: " + e.getLocalizedMessage();
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ss.getFilename(), ss.getLocation()));
            }
        }
        return ss;
    }

    public boolean isCheckInclusion() {
        return checkInclusion;
    }

    public void setCheckInclusion(boolean checkInclusion) {
        this.checkInclusion = checkInclusion;
    }
}
