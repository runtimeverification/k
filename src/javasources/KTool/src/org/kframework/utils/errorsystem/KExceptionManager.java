package org.kframework.utils.errorsystem;

import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
	private final List<KException> exceptions = new ArrayList<KException>();

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
            System.err.println(StringUtil.splitLines(e.toString()));
		}
		if (errors)
			System.exit(1);
	}
}
