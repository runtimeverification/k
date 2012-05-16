package ro.uaic.info.fmse.pp;

import org.w3c.dom.Document;

import ro.uaic.info.fmse.pp.labels.LabelGenerator;

public class Preprocessor {

	public Document run(Document kil)
	{
		LabelGenerator lg = new LabelGenerator();
		kil = lg.generateKLabels(kil);
		
		return kil;
	}
}
