package ro.uaic.info.fmse.k;

public interface ProductionItem {
	public enum ProductionType { TERMINAL, SORT, USERLIST } ;
	
	public ProductionType getType();
}
