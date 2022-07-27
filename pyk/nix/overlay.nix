self: super: {
  graphviz = self.callPackage ./packages/graphviz { };

  pyk = self.callPackage ./packages/pyk { };

}
