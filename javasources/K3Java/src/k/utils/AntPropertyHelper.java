package k.utils;

import java.io.*;
import javax.xml.parsers.*;
import org.w3c.dom.*;

public class AntPropertyHelper {

	public static void main(String[] args) {
		if (args.length < 2)
			System.exit(2);

		try {
			// parse the xml returned by the parser.
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			Document doc = db.parse(new File(args[0]));

			NodeList nl = doc.getElementsByTagName("artifact");
			for (int i = 0; i < nl.getLength(); i++) {
				Node n = nl.item(i);

				Element el = (Element) n;
				if (el.getAttribute("id").equals(args[1])) {
					System.out.println(el.getAttribute("version"));
					return;
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		System.exit(1);
	}
}
