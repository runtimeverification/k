self: super: {
  types-tabulate = self.callPackage ./packages/types-tabulate { };

  tabulate = self.callPackage ./packages/tabulate { };

  graphviz = self.callPackage ./packages/graphviz { };

  pyk = self.callPackage ./packages/pyk { };

}
