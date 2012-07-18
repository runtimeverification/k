package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Sort extends ProductionItem {

	private String sort;

	public Sort(Element element) {
		super(element);

		sort = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public static boolean isBasesort(String sort) {
		return sort.equals("VARID") || sort.equals("Map") || sort.equals("K") || sort.equals("List") || sort.equals("Bag") || sort.equals("Set") || sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("BagItem") || sort.equals("SetItem")
				|| sort.equals("List{K}") || sort.equals("KLabel") || sort.equals("CellLabel");
	}
	
	public boolean isBaseSort() {
		return Sort.isBasesort(sort);
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public String getSort() {
		return sort;
	}

	public ProductionType getType() {
		return ProductionType.SORT;
	}

	@Override
	public String toString() {
		return sort;
	}

	@Override
	public String toMaude() {
		return sort;
	}

	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		Element sort = doc.createElement(Constants.SORT);
		sort.setTextContent(this.sort);

		return sort;
	}

	public void accept(Modifier visitor) {
		visitor.modify(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (obj == this)
			return true;
		if (!(obj instanceof Sort))
			return false;

		Sort srt = (Sort) obj;

		if (!sort.equals(srt.getSort()))
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		return this.sort.hashCode();
	}
}
