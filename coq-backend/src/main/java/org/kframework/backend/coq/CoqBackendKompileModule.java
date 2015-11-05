// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.coq;

import com.google.inject.AbstractModule;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;

/**
 * Created by brandon on 1/21/15.
 */
public class CoqBackendKompileModule extends AbstractModule {
    @Override
    protected void configure() {
        bind(FileSystem.class).to(PortableFileSystem.class);
    }
}
