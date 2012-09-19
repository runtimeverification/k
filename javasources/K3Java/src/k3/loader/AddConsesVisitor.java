package k3.loader;

import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.visitors.BasicVisitor;

import k.utils.StringUtil;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class AddConsesVisitor extends BasicVisitor {

	public void visit(Production p) {
		// add cons to productions that don't have it already
		if (p.getAttributes().containsKey("bracket")) {
			// don't add cons to bracket production
			String cons = p.getAttributes().get("cons");
			if (cons != null)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "'bracket' productions are not allowed to have cons: '" + cons + "'", p.getFilename(), p.getLocation(), 0));
		} else if (p.getItems().size() == 1 && p.getItems().get(0).getType() == ProductionType.TERMINAL && (p.getSort().startsWith("#") || p.getSort().equals("KLabel"))) {
			// don't add any cons, if it is a constant
			// a constant is a single terminal for a builtin sort
			String cons = p.getAttributes().get("cons");
			if (cons != null)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Constants are not allowed to have cons: '" + cons + "'", p.getFilename(), p.getLocation(), 0));
		} else if (p.isSubsort()) {
			// cons are not allowed for subsortings
			String cons = p.getAttributes().get("cons");
			if (cons != null)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Subsortings are not allowed to have cons: '" + cons + "'", p.getFilename(), p.getLocation(), 0));
		} else {
			if (!p.getAttributes().containsKey("cons")) {
				String cons;
				if (p.isListDecl())
					cons = StringUtil.escapeSortName(p.getSort()) + "1" + "ListSyn";
				else
					cons = StringUtil.escapeSortName(p.getSort()) + "1" + StringUtil.getUniqueId() + "Syn";
				p.getAttributes().getContents().add(new Attribute("cons", "\"" + cons + "\""));
			} else {
				// check if the provided cons is correct
				String cons = p.getAttributes().get("cons");
				String escSort = StringUtil.escapeSortName(p.getSort());
				if (!cons.startsWith(escSort))
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "The cons attribute must start with '" + escSort + "' and not with " + cons, p.getFilename(), p.getLocation(), 0));
				if (!cons.endsWith("Syn")) // a normal cons must end with 'Syn'
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "The cons attribute must end with 'Syn' and not with " + cons, p.getFilename(), p.getLocation(), 0));
				if (p.isListDecl() && !cons.endsWith("ListSyn")) // if this is a list, it must end with 'ListSyn'
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "The cons attribute must end with 'ListSyn' and not with " + cons, p.getFilename(), p.getLocation(), 0));
			}
		}
	}
}
