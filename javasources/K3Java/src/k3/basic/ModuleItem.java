package k3.basic;

import org.w3c.dom.Node;

public abstract class ModuleItem extends Term {
	public enum ModuleType {
		MODULE, COMMENT, REQUIRE;
	}

	public ModuleItem() {
	}

	public ModuleItem(ModuleItem s) {
		super(s);
	}

	public ModuleItem(Node node) {
		super(node);
	}

	public abstract ModuleType getType();

	@Override
	public abstract ModuleItem clone();
}
