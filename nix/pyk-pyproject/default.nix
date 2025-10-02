{
  lib,
  callPackage,
  nix-gitignore,

  uv2nix,
}:
let
  # load a uv workspace from a workspace root
  workspace = uv2nix.lib.workspace.loadWorkspace {
    workspaceRoot = lib.cleanSource (nix-gitignore.gitignoreSourcePure [
        ../../.gitignore
        ".github/"
        "result*"
        "/deps/"
        # do not include submodule directories that might be initilized empty or non-existent
      ] ../../pyk/.
    );
  };

  # create overlay
  lockFileOverlay = workspace.mkPyprojectOverlay {
    # prefer "wheel" over "sdist" due to maintance overhead
    # there is no bundled set of overlays for "sdist" in uv2nix, in contrast to poetry2nix
    sourcePreference = "wheel";
  };
in {
  inherit lockFileOverlay workspace;
}
