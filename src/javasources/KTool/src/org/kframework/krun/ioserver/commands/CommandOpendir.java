// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.nio.file.AccessDeniedException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.NotDirectoryException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class CommandOpendir extends Command {

    private String path;

    public CommandOpendir(String[] args, Socket socket, Logger logger, FileSystem fs) {
        super(args, socket, logger, fs);

        path = args[1];
    }

    public void run() {
        try {
            Path dir = Paths.get(path);
            DirectoryStream<Path> files = Files.newDirectoryStream(dir);
            List<String> paths = new ArrayList<String>();
            for (Path file : files) {
                Path relative = dir.relativize(file);
                paths.add(relative.toString());
            }
            String[] result = paths.toArray(new String[] {});
            succeed(result);
        } catch (NoSuchFileException e) {
            fail("ENOENT");
        } catch (AccessDeniedException e) {
            fail("EACCES");
        } catch (NotDirectoryException e) {
            fail("ENOTDIR");
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }
}

