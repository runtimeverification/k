package resources;

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

	private static Resource createResource(URI uri, String[] args) throws ResourceException {
		if (uri.toString().equals("smt")){
			return new ResourceSmt("z3"); }
		else if (uri.getScheme().equals("file")) {
			return createNormalFile(uri, args);
		} else if (uri.getScheme().equals("stdin")) {
			return new ResourceInFile();
		} else if (uri.getScheme().equals("stdout")) {
			return new ResourceOutFile(System.out);
		} else if (uri.getScheme().equals("stderr")) {
			return new ResourceOutFile(System.err);
		} 
		
		return null;
	}
	
	private static FileResource createNormalFile(URI uri, String[] args) throws ResourceException {
		if (uri.getPath() == null) { // relative path
			String requestPath = uri.getSchemeSpecificPart();
			try {
				String localPath = new java.io.File(".").getCanonicalPath();
				uri = new java.io.File(localPath, requestPath).toURI();
			} catch (java.io.IOException e) {
				throw new ResourceException(e);
			}
		}
		// URI u = uri;
		// System.out.println(uri);
		// System.out.println(u.getSchemeSpecificPart());
		// System.out.println(u.getHost());
		// System.out.println(u.getPort());
		// System.out.println(u.getScheme());
		// System.out.println(u.getUserInfo());
		// System.out.println(u.getAuthority());
		// System.out.println(u.getPath());
		// System.out.println(u.getQuery());
		// System.out.println(u.getFragment());
		
		// String requestPath = uri.getPath();
		// System.out.println(requestPath);
		// String path = new java.io.File(".").getCanonicalPath();
		// System.out.println(path);
		// URI myURI = new URI("file", null, path, null);
		// System.out.println(myURI);
		// System.out.println("Before: " + uri);
		// uri = myURI.resolve(uri);
		// System.out.println("After: " + uri);
		try {
			if (args[2].startsWith("r")) {
				return new ResourceRandFile(uri, args[2]);
			} else {
				return new ResourceOutFile(uri, args[2]);
			}
		} catch (java.io.FileNotFoundException e) {
			throw new ResourceException(e);
		}
		// } catch (FileNotFoundException e) {
			// return null;
		// } catch (java.io.IOException e) {
			// return null;
		// }
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
