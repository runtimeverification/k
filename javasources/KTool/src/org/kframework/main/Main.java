package org.kframework.main;

import org.kframework.utils.Error;

public class Main {

	/**
	 * @param args
	 *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
	 */
	public static void main(String[] args) {
		if (args.length >= 1) {
			String[] args2 = new String[args.length - 1];
			for (int i = 0; i < args.length - 1; i++)
				args2[i] = args[i + 1];
			if (args[0].equals("-kompile")) {
				KompileFrontEnd.kompile(args2);
			} else if (args[0].equals("-kast")) {
				KastFrontEnd.kast(args2);
			} else if (args[0].equals("-hkcd")) {
				HKCDFrontEnd.hkcd(args2);
			} else if (args[0].equals("-krun")) {
				org.kframework.krun.Main.execute_Krun(args2);
			} else {
				Error.report("The first argument of K3 not recognized. Try -kompile or -kast or -krun.");
			}
		}
		Error.report("There must be a first argument to K3: try -kompile or -kast or -krun.");
	}
}
