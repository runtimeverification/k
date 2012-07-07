package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.visitors.BasicVisitor;

import com.thoughtworks.xstream.XStream;

public class HaskellDumpFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	XStream xstream = new XStream();
	private String result = "";

	@Override
	public void visit(Rewrite r) {
		result += xstream.toXML(r);
	}

	public String getResult() {
		return result;
	}
}
