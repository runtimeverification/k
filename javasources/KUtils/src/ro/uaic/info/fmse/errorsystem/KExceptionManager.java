package ro.uaic.info.fmse.errorsystem;

import java.util.ArrayList;
import java.util.List;

import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class KExceptionManager {
	private List<KException> exceptions = new ArrayList<KException>();

	public void register(KException exception) {
		exceptions.add(exception);
		if (exception.exceptionGroup.equals(KExceptionGroup.CRITICAL)) {
			print(GlobalSettings.level);
		}
	}

	public void print(int level) {
		boolean errors = false;
		for (KException e : exceptions)
			if (e.level <= level) {
				if (e.type == ExceptionType.WARNING && e.level <= GlobalSettings.warnings) {
					System.err.println(e);
				} else
					System.err.println(e);
				if (e.type == ExceptionType.ERROR)
					errors = true;
			}
		if (errors)
			System.exit(1);
	}

	public void print(int level, KExceptionGroup keg) {
		boolean errors = false;
		for (KException e : exceptions)
			if (e.level <= level)
				if (e.exceptionGroup == keg) {
					if (e.type == ExceptionType.WARNING && !GlobalSettings.warnings) {
						// ignore warnings
					} else
						System.out.println(e);
					if (e.type == ExceptionType.ERROR)
						errors = true;
				}
		if (errors)
			System.exit(1);
	}
}
