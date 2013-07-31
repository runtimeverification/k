package org.kframework.krun.ioserver.main;

import org.kframework.compile.FlattenModules;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.utils.BinaryLoader;

import java.io.File;
import java.io.FileInputStream;
import java.util.logging.Logger;

public class MainServer implements Runnable {
	public int _port;
	public boolean _started;
	private Logger _logger;
	protected Context context;
    protected FileSystem fs;

	public MainServer(int port, Logger logger, Context context) {
		this.context = context;
		_port = port;
		_logger = logger;
        fs = new PortableFileSystem();
	}
	public void run() {
		IOServer server = new IOServer(_port, _logger, context, fs);
		_port = server.port; // in case server changes port
		_started = true;
		try {
			server.acceptConnections();
		} catch (java.io.IOException e) {
			_logger.severe("Error accepting connection:" + e);
		}
	}

	public static void main(String[] args) throws Exception {
		Context context = new Context();
		context.kompiled = new File(args[1]);
		Definition javaDef = (Definition) BinaryLoader.fromBinary(
			new FileInputStream(context.kompiled.getCanonicalPath() + "/defx-maude.bin"));
		javaDef = new FlattenModules(context).compile(javaDef, null);
		javaDef = (Definition) javaDef.accept(new AddTopCellConfig(context));
		// This is essential for generating maude
		javaDef.preprocess(context);
        K.parser = args[2];
		Logger logger = java.util.logging.Logger.getLogger("KRunner");
		logger.setUseParentHandlers(false);
		MainServer ms = new MainServer(Integer.parseInt(args[0]), logger, context);
		
		ms.run();
		//start(Integer.parseInt(args[0]));
	}
}
