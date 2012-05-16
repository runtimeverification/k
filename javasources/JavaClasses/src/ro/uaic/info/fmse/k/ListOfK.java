package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

public class ListOfK extends Collection {
	public ListOfK(String location, String filename) {
		super(location, filename);
	}

	public ListOfK(Element element) {
		super(element);
	}

	@Override
	public String toString() {
		String content = "";
		for (int i = 0; i < contents.size(); i++) {
			if (i == contents.size() - 1)
				content += contents.get(i);
			else
				content += contents.get(i) + ",, ";
		}
		return content;
	}

	@Override
	public String toMaude() {
		String content = "";

		for (Term term : contents)
			if (term != null)
				content += term.toMaude() + ",";

		if (content.length() > 1)
			content = content.substring(0, content.length() - 1);

		return "_`,`,_(" + content + ")";
	}
}
