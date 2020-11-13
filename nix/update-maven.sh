#!/usr/bin/env nix-shell
#!nix-shell ../shell.nix -i bash

# Run this script (from the top level of the repository) when the maven
# project's dependencies change.

# Ensure the source is loaded into the Nix store.
# mavenix will not do this automatically because we are using nix-gitignore.
nix-instantiate --eval -E '(import ./. {}).k.src'

mvnix-update -E '(import ./. {}).k'
