package ro.uaic.info.fmse.utils;

public class Generator {
	private static int id = 0;
	
	public static int getNewId()
	{
		return id ++;
	}
}
