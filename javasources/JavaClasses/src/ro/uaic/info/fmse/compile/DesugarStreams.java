package ro.uaic.info.fmse.compile;

import java.util.Set;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class DesugarStreams implements CompilerStep {

	@Override
	public Definition compile(Definition def) {
		Configuration cfg = MetaK.getConfiguration(def);
		
		ASTNode cfgDesugaredNode = new StreamDesugarer().transform(cfg);
		if (!(cfgDesugaredNode instanceof Configuration)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Configuration Cleaner failed.", 
					cfg.getFilename(), cfg.getLocation(), 0));
		}
		Configuration cfgDesugared = (Configuration)cfgDesugaredNode;

		return null;
	}

	public class StreamDesugarer extends BasicTransformer {

	}

	@Override
	public String getName() {
		return "Desugar streams";
	}
	
}
