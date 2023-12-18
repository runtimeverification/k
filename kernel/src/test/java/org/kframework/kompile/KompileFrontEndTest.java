// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kompile;

import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import com.google.inject.util.Providers;
import java.io.IOException;
import org.junit.Test;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.IOTestCase;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.mockito.Mock;

public class KompileFrontEndTest extends IOTestCase {

  @Mock org.kframework.compile.Backend koreBackend;

  @Mock JarInfo jarInfo;

  @Mock FileUtil files;

  KompileOptions options = new KompileOptions();
  OuterParsingOptions outerOptions = new OuterParsingOptions();
  InnerParsingOptions innerOptions = new InnerParsingOptions();
  GlobalOptions globalOptions = new GlobalOptions();

  @Test
  public void testHelp() throws IOException {
    globalOptions.help = true;
    new KompileFrontEnd(
            options,
            outerOptions,
            innerOptions,
            globalOptions,
            "foo",
            Providers.of(koreBackend),
            sw,
            kem,
            loader,
            jarInfo,
            Providers.of(files))
        .main();
    assertEquals("foo", stdout.toString());
  }

  @Test
  public void testVersion() {
    globalOptions.version = true;
    new KompileFrontEnd(
            options,
            outerOptions,
            innerOptions,
            globalOptions,
            "",
            Providers.of(koreBackend),
            sw,
            kem,
            loader,
            jarInfo,
            Providers.of(files))
        .main();
    verify(jarInfo).printVersionMessage();
  }
}
