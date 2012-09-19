package org.kframework.parser.generator.preprocessor;

import org.kframework.parser.generator.preprocessor.labels.LabelGenerator;
import org.w3c.dom.Document;


public class Preprocessor {

	public Document run(Document kil)
	{
		LabelGenerator lg = new LabelGenerator();
		kil = lg.generateKLabels(kil);
		
		return kil;
	}
}
