package org.kframework.kore;

import org.junit.Test;
import static org.kframework.kore.Interface.*;

public class InterfaceTest {

	@Test
	public void example() {
		// Creating "A + 0 => A" programmatically

		KRewrite k = KRewrite(
				KApply(KLabel("_+_"),
						KList(KVariable("A"), KToken(Sort("Int"), KString("0")))),
				KVariable("A"));

		// Navigating it
		KLabel theLabel = ((KApply) k.left()).klabel();
	}
}
