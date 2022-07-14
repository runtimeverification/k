# WARNING: This file was automatically generated. You should avoid editing it.
# If you run pynixify again, the file will be either overwritten or
# deleted, and you will lose the changes you made to it.

{ buildPythonPackage, fetchPypi, lib }:

buildPythonPackage rec {
  pname = "tabulate";
  version = "0.8.6";

  src = fetchPypi {
    inherit pname version;
    sha256 = "1j1pcwwbziramsj97ha9dngzwdcjdnab52gf5h2cg4d0hxkcqw2l";
  };

  # TODO FIXME
  doCheck = false;

  meta = with lib; {
    description = "Pretty-print tabular data";
    homepage = "https://github.com/astanin/python-tabulate";
  };
}
