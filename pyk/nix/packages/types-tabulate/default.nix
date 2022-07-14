# WARNING: This file was automatically generated. You should avoid editing it.
# If you run pynixify again, the file will be either overwritten or
# deleted, and you will lose the changes you made to it.

{ buildPythonPackage, fetchPypi, lib }:

buildPythonPackage rec {
  pname = "types-tabulate";
  version = "0.8.6";

  src = fetchPypi {
    inherit pname version;
    sha256 = "02kiv04hyrxw0c80mbbivppb2i602i8yq562sn71ghj9aiwznk9z";
  };

  # TODO FIXME
  doCheck = false;

  meta = with lib; {
    description = "Typing stubs for tabulate";
    homepage = "https://github.com/python/typeshed";
  };
}
