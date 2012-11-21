package org.kframework.compile.utils;

import org.kframework.kil.Definition;

public interface CheckStep {
	boolean check(Definition def);
	String getName(); 
}
