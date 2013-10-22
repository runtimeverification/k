package org.kframework.utils.errorsystem;

import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
	private List<KException> exceptions = new ArrayList<KException>();

	public void register(KException exception) {
		exceptions.add(exception);
		if (exception.type == ExceptionType.ERROR)
			print();
	}

	public void print() {
		boolean errors = false;
		for (KException e : exceptions) {
			if (!GlobalSettings.warnings.equals("all") && e.type == ExceptionType.HIDDENWARNING)
				continue;
            if (GlobalSettings.warnings.equals("none") && e.type == ExceptionType.WARNING)
                continue;

			if (e.type == ExceptionType.ERROR)
				errors = true;
			System.err.println(e);
		}
		if (errors)
			System.exit(1);
	}

	public void print(KExceptionGroup keg) {
		boolean errors = false;
		for (KException e : exceptions)
			if (e.exceptionGroup == keg) {
				if (!GlobalSettings.warnings.equals("all") && e.type == ExceptionType.HIDDENWARNING)
					continue;
                if (GlobalSettings.warnings.equals("none") && e.type == ExceptionType.WARNING)
                    continue;

				if (e.type == ExceptionType.ERROR)
					errors = true;
				System.err.println(e);
			}
		if (errors)
			System.exit(1);
	}
}
