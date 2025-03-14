{ poetry2nix, projectDir }:
(final: prev:
  let
    mkPyk = python:
      let
        p2n = poetry2nix.lib.mkPoetry2Nix { pkgs = prev; };
      in p2n.mkPoetryApplication {
        inherit projectDir;
        python = python;
        groups = [ ];
        # We remove `"dev"` from `checkGroups`, so that poetry2nix does not try to resolve dev dependencies.
        checkGroups = [ ];
        overrides = p2n.defaultPoetryOverrides.extend
          (self: super: {
            click = super.urllib3.overridePythonAttrs
            (
              old: {
                buildInputs = (old.buildInputs or [ ]) ++ [ super.flit-core ];
              }
            );
          });
      };
  in rec {
    pyk = pyk-python310;
    pyk-python310 = mkPyk prev.python310;
    pyk-python311 = mkPyk prev.python311;
  })
