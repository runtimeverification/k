package org.kframework.krun.gui.UIDesign;

import java.awt.Dimension;
import java.awt.Toolkit;

import javax.swing.JFrame;

import org.kframework.kil.loader.Context;
import org.kframework.krun.gui.Controller.RunKRunCommand;

public class MainWindow extends JFrame {

	private static final long serialVersionUID = 1L;

	public MainWindow(RunKRunCommand command, Context context){
			Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
			this.setPreferredSize(screenSize);
			this.setExtendedState(MAXIMIZED_BOTH);
			this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);			
		    try {
				this.getContentPane().add(new GraphRepresentation(command, context));
			} catch (Exception e) {
				e.printStackTrace();
			}		   
		    this.pack();
		    this.setVisible(true);
   }
}