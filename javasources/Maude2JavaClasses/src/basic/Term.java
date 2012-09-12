package basic;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.utils.file.FileUtil;

public class Term {
	private String op;
	private String sort;
	private String number;
	private List<Term> children;

	public static Term loadTermFromFile(String file) {
		String fileContent = FileUtil.getFileContent(file);

		try {
			// parse the xml returned by the parser.
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			InputStream is = new ByteArrayInputStream(
					fileContent.getBytes("UTF-8"));
			Document doc = db.parse(is);

			NodeList nl = doc.getElementsByTagName("result");

			return new Term((Element) nl.item(0).getFirstChild()
					.getNextSibling());

		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public Term() {
		setOp("");
		setSort("");
		setNumber("");
		setChildren(new ArrayList<Term>());
	}

	public Term(Element elm) {
		if (elm.getNodeName() != "term")
			System.out.println("Tag is not term: " + elm.getNodeName());
		setOp(elm.getAttribute("op"));
		setSort(elm.getAttribute("sort"));
		if (elm.hasAttribute("number")) {
			setNumber(elm.getAttribute("number"));
		} else {
			setNumber("");
		}

		setChildren(new ArrayList<Term>());
		NodeList nl = elm.getChildNodes();
		for (int i = 0; i < nl.getLength(); i++) {
			if (nl.item(i).getNodeType() == Node.ELEMENT_NODE) {
				getChildren().add(new Term((Element) nl.item(i)));
			}
		}
	}

	public String getOp() {
		return op;
	}

	public void setOp(String op) {
		this.op = op;
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public String getNumber() {
		return number;
	}

	public void setNumber(String number) {
		this.number = number;
	}

	public List<Term> getChildren() {
		return children;
	}

	public void setChildren(List<Term> children) {
		this.children = children;
	}

	public boolean hasChildren() {
		return this.children.size() > 0;
	}

	@Override
	public String toString() {
		String str = this.op;

		if (children.size() > 0) {
			str += "(";
			for (Term t : this.children)
				str += t.toString() + ", ";
			str = str.substring(0, str.length() - 2);
			str += ")";
		}
		return str;
	}
}
