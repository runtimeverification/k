package resources;

public class ResourceException extends Exception {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	ResourceException() {
		super();
	}
	
	ResourceException(String message){
		super(message);
	}
	
	ResourceException(String message, Throwable t){
		super(message, t);
	}
	
	ResourceException(Throwable t){
		super(t);
	}
}
