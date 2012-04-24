package ro.uaic.info.fmse.k2m.utils;

import generated.Constants;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class ParsingError
{
	public static void check(Document doc)
	{
		checkError(doc);
		
		checkAmb(doc);
	}
	
	private static void checkAmb(Document doc) {
		NodeList ambs = doc.getElementsByTagName("amb");
		
		
		for(int i = 0; i < ambs.getLength(); i++)
		{
			Element amb = (Element)ambs.item(i);
			
			System.out.println("Ambiguity at " + amb.getAttribute(Constants.LOC_loc_ATTR) + " file: " + amb.getAttribute("filename"));
			
		}
		
		if (ambs.getLength() > 0)
			System.exit(1);
	}

	public static void checkError(Document doc)
	{
		NodeList errors = doc.getElementsByTagName("error");
		
		for(int i = 0; i < errors.getLength(); i++)
		{
			Element error = (Element)errors.item(i);
			
			String type = error.getAttribute("value");
			
			NodeList localized = error.getElementsByTagName("localized");
			for(int j = 0; j < localized.getLength(); j++)
			{
				Element local = (Element)localized.item(j);
				String file = local.getAttribute("filename");
				String location = local.getAttribute("loc");
				String message = local.getAttribute("message");
				
				System.out.println(type + ": " + message + " in file " + file + " at " + location);
			}
		}
		
		if (errors.getLength() > 0)
			System.exit(1);
	}

}
