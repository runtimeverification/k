package org.kframework.backend;

import org.kframework.kil.Definition;
import org.kframework.utils.Stopwatch;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12
 * Time: 11:18 PM
 */
public abstract class BasicBackend implements Backend {
	protected Stopwatch sw;

	public BasicBackend(Stopwatch sw) {
		this.sw = sw;
	}

	@Override
	public Definition lastStep(Definition def) {
		return def;
	}

	@Override
	public Definition firstStep(Definition def) {
		return def;
	}
}
