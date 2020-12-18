#!/usr/bin/env nix-shell
#!nix-shell ./shell.maven.nix -i bash

# Run this script (from the top level of the repository) when the maven
# project's dependencies change.

# Ensure the source is loaded into the Nix store.
# This command will fail, but only after loading the source.
# mavenix will not do this automatically because we it uses restrict-eval,
# and we are using filterSource, which is disabled under restrict-eval.
nix-build --no-out-link -E '(import ./. {}).k.src' || echo "^~~~ expected error"

mvnix-update -E '(import ./. {}).k'
