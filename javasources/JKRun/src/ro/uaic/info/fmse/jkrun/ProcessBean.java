package ro.uaic.info.fmse.jkrun;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.IOException;
import java.io.Serializable;

public class ProcessBean implements PropertyChangeListener, Serializable {

	private static final long serialVersionUID = 1L;
	private static final int defaultValue = Integer.MAX_VALUE;
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
				try {
					FileUtil.renameFolder(K.krunTempDir, K.krunDir);
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
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
