package ro.uaic.info.fmse.jkrun;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.Serializable;

public class ProcessBean implements PropertyChangeListener, Serializable {

	private static final long serialVersionUID = 1L;
	public static final int defaultValue = Integer.MAX_VALUE;
	private int exitCode;

	private PropertyChangeSupport pcs = new PropertyChangeSupport(this);

	public ProcessBean() {
		pcs.addPropertyChangeListener(this);
		this.exitCode = defaultValue;
	}
	
	public void propertyChange(PropertyChangeEvent evt) {
		int newValue;
	    if (evt.getPropertyName().equals("exitCode")) {
	    	newValue = (Integer)evt.getNewValue();
	    	if (newValue != defaultValue) {
	    		//the default exit code has changed, the program is about to terminate and the krun temp directory should be renamed
	    		
	    		//test if the krun directory is empty and if is not empty delete its content
				File f = new File(K.krunDir);
				boolean empty = true;
				if (f.exists()) {
					empty = FileUtil.isEmptyDir(K.krunDir);
				}
				if (!empty) {
					FileUtil.deleteDirectoryContent(f);
				}
				//rename krun temp directory into "krun" 
				boolean success = FileUtil.renameDirectory(K.krunTempDir, K.krunDir);
				if (!success) {
					Error.externalReport("Directory does not rename successfully.");
				}
	    	}
	    }
	    
	}

	public int getExitCode() {
		return exitCode;
	}

	public void setExitCode(int exitCode) {
		int oldValue = this.exitCode;
		this.exitCode = exitCode;
	    pcs.firePropertyChange("exitCode", oldValue, exitCode);
	}

}
