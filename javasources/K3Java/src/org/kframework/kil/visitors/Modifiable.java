package org.kframework.kil.visitors;

public interface Modifiable {
	public void applyToAll(Modifier visitor);
}
