package ro.uaic.info.fmse.main;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;

public class CAManager {

	private ConfigurationInferencer ci;
	
	public CAManager(Element config) {
		ci = new ConfigurationInferencer(createConfiguration(config));
	}

	public Element transform(Element erule)
	{
		Rule rule = createRule(erule);
		
		rule = ci.inferConfigurationForRule(rule);
		
		return erule;
//		return xmlify(rule);
	}
	
	public Element xmlify(Rule rule) {
		return null;
	}

	private Rule createRule(Element rule)
	{
		return new Rule(rule);
	}
	
	private Configuration createConfiguration(Element config)
	{
		return new Configuration(config);
	}
	
}
