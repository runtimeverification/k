package org.kframework.krun.ioserver.commands;

import java.io.IOException;
import java.net.Socket;
import java.nio.file.AccessDeniedException;
import java.nio.file.Files;
import java.nio.file.FileSystemException;
import java.nio.file.NoSuchFileException;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.file.attribute.PosixFileAttributes;
import java.util.Set;
import java.util.logging.Logger;

public class CommandStat extends Command {

	private String path;

	public CommandStat(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);

		path = args[1];
	}

	public void run() {
		try {
			PosixFileAttributes attrs = Files.readAttributes(Paths.get(path), PosixFileAttributes.class);
			//some notes on where we get these values: we call hashCode on the principals because I don't know a better way to get the integer associated with the principal. We also rely on the implementation of the toString method on file keys in order to get back the device id and inode number.
			succeed(new String[] {
				Long.toString(attrs.lastModifiedTime().toMillis()),
				Long.toString(attrs.lastAccessTime().toMillis()),
				Long.toString(attrs.creationTime().toMillis()),
				Boolean.toString(attrs.isRegularFile()),
				Boolean.toString(attrs.isDirectory()),
				Boolean.toString(attrs.isSymbolicLink()),
				Long.toString(attrs.size()),
				getDevice(attrs.fileKey()),
				getInode(attrs.fileKey()),
				Integer.toString(attrs.group().hashCode()),
				Integer.toString(attrs.owner().hashCode()),
				getPermissions(attrs.permissions())
			});
		} catch (NoSuchFileException e) {
			fail("ENOENT");
		} catch (AccessDeniedException e) {
			fail("EACCES");
		} catch (FileSystemException e) {
			if (e.getReason() != null && e.getReason().equals("Not a directory")) {
				fail("ENOTDIR");
			} else if (e.getReason() != null && e.getReason().equals("Too many levels of symbolic links")) {
				fail("ELOOP");
			} else if (e.getReason() != null && e.getReason().equals("File name too long")) {
				fail("ENAMETOOLONG");
			} else {
				e.printStackTrace();
				fail(e.getLocalizedMessage());
			}
		} catch (IOException e) {
			e.printStackTrace();
			fail(e.getLocalizedMessage());
		}
	}

	public String getPermissions(Set<PosixFilePermission> permissions) {
		int bits = 0;
		for (PosixFilePermission permission : permissions) {
			bits |= permission.ordinal();
		}
		return Integer.toString(bits);
	}

	public String getDevice(Object fileKey) {
		String s = fileKey.toString();
		String dev = s.substring(5, s.indexOf(","));
		return Integer.toString(Integer.parseInt(dev, 16));
	}

	public String getInode(Object fileKey) {
		String s = fileKey.toString();
		String ino = s.substring(s.indexOf("ino=") + 4, s.indexOf(")"));
		return ino;
	}
}
