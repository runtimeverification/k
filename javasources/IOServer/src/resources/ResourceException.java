package resources;

public class ResourceException extends Exception {
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
