package org.kframework.krun;

import org.kframework.kil.*;

import java.util.Set;

public interface KRun {
	public KRunResult run(Term cfg) throws Exception;
	public KRunResult search(String bound, String depth, String searchType, Rule pattern, Term cfg, Set<String> varNames) throws Exception;
	public KRunResult modelCheck(Term formula, Term cfg) throws Exception;
}
