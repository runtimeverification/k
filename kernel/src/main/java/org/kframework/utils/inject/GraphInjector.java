// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.grapher.graphviz.GraphvizGrapher;
import com.google.inject.grapher.graphviz.GraphvizModule;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import org.kframework.main.Main;

public class GraphInjector {

  public static void main(String[] args) throws IOException {
    String[] args2 = Arrays.copyOfRange(args, 1, args.length);
    Injector injector = Main.getInjector(args[0]);
    graph("injector.dot", injector);
  }

  private static void graph(String filename, Injector demoInjector) throws IOException {
    PrintWriter out = new PrintWriter(new File(filename), StandardCharsets.UTF_8);

    Injector injector = Guice.createInjector(new GraphvizModule());
    GraphvizGrapher grapher = injector.getInstance(GraphvizGrapher.class);
    grapher.setOut(out);
    grapher.setRankdir("TB");
    grapher.graph(demoInjector);
  }
}
