let
  sources = import ../sources.nix;
in

self: super: {
  z3 = super.z3.overrideAttrs (old: {
    src = sources.z3;
    version = builtins.replaceStrings ["z3-"] [""] sources.z3.branch;
  });
}
