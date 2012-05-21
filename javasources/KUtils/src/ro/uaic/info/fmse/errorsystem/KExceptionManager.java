package ro.uaic.info.fmse.errorsystem;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
	private static List<KException> exceptions = new ArrayList<KException>();
	
	public static void register(KException exception)
	{
		exceptions.add(exception);
	}
	
	
}
