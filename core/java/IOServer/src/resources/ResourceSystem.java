package resources;

import java.io.FileNotFoundException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;

import main.Fresh;

public class ResourceSystem {

	static ConcurrentHashMap<Long, Resource> files = new ConcurrentHashMap<Long, Resource>();
	static ConcurrentHashMap<Long, Long> time = new ConcurrentHashMap<Long, Long>();
	private static Long lastCleanup;
	private static final Long TIME = (long) (120 * 60 * 1000);

	public static Resource getResource(Long ID) {
		return files.get(ID);
	}

	public static void appendResource(Long ID, Resource fs) throws Exception {
		files.put(ID, fs);
		time.put(ID, System.currentTimeMillis());

		// initialize lastCleanup
		if (lastCleanup == null) {
			lastCleanup = System.currentTimeMillis();
		}

		// lazyCleanup if neccessary
		lazyCleanup();
	}

	private static void lazyCleanup() throws Exception {
		Long now = System.currentTimeMillis();

		if (now - lastCleanup > TIME) {
			List<Long> toRemove = new LinkedList<Long>();

			for (Entry<Long, Resource> entry : files.entrySet()) {
				if (now - time.get(entry.getKey()) > TIME) {
					toRemove.add(entry.getKey());
				}
			}

			for (Long l : toRemove) {
				remove(l);
			}
		}
	}

	public static Long getNewResource(String uri_, String[] args)
			throws Exception {
		return getNewResource(Fresh.getFreshId(), uri_, args);
	}

	public static Long getNewResource(Long ID, String uri_, String[] args)
			throws Exception {
		try {
			// parse uri
			URI uri = new URI(uri_);

			// remove ID if any
			remove(ID);

			// create proper resources depending on URI schema
			Resource resource = createResource(uri, args);

			// return null to command in order to trigger exception
			if (resource == null)
				return null;

			// append resource in map
			appendResource(ID, resource);

			// return the resource ID
			return ID;

		} catch (URISyntaxException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return null;
	}

	private static Resource createResource(URI uri, String[] args) {

		try {
			if (uri.getScheme().equals("file")) {
				if (args[2].startsWith("r"))
					return new ResourceRandFile(uri, args[2]);
				else
					return new ResourceOutFile(uri, args[2]);
			} else if (uri.getScheme().equals("stdin")) {
				return new ResourceInFile();
			} else if (uri.getScheme().equals("stdout")) {
				return new ResourceOutFile(System.out);
			} else if (uri.getScheme().equals("stderr")) {
				return new ResourceOutFile(System.err);
			}
		} catch (FileNotFoundException e) {
			return null;
		}

		return null;
	}

	public static void remove(Long iD) throws Exception {
		// clean
		Resource resource = getResource(iD);

		if (resource != null)
			resource.close();

		files.remove(iD);
		time.remove(iD);
	}

}
