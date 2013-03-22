package org.kframework.krun.gui.UIDesign;

import java.awt.Color;
import java.util.Map.Entry;

import org.kframework.kil.Cell;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.krun.gui.UIDesign.xmlEditor.ColorTagMap;
import org.kframework.utils.ColorUtil;

public class ColorVisitor extends BasicVisitor{
	@Override
	public void visit(Cell cell) {
		Cell declaredCell = DefinitionHelper.cells.get(cell.getLabel());
		if (declaredCell != null) {
			String declaredColor = declaredCell.getCellAttributes().get("color");
			if (declaredColor != null) {
				Color c = ColorUtil.colors.get(declaredColor);
				ColorTagMap.addColorToTag(cell.getLabel(), c);
			}
		}
		cell.getContents().accept(this);
	}
}
