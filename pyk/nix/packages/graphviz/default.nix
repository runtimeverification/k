# WARNING: This file was automatically generated. You should avoid editing it.
# If you run pynixify again, the file will be either overwritten or
# deleted, and you will lose the changes you made to it.

{ buildPythonPackage, fetchPypi, lib }:

buildPythonPackage rec {
  pname = "graphviz";
  version = "0.19.1";

  src = fetchPypi {
    inherit pname version;
    extension = "zip";
    sha256 = "0y4hyjw8r04p9c6jbg7m8p92hbv4xc8a4ia8gkkmy09d8pg0rv89";
  };

  # TODO FIXME
  doCheck = false;

  meta = with lib; {
    description = "Simple Python interface for Graphviz";
    homepage = "https://github.com/xflr6/graphviz";
  };
}
