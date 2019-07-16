Installation
============

These instructions explain both (1) how to build the packages for K, and (2) how to install them.

Packaging
---------

Update `stack` with `sudo stack upgrade` or `curl -sSL https://get.haskellstack.org/ | sh` to make sure you have the newest version (> 2.0).

### Debian

```
dpkg-buildpackage --no-sign
```

It will throw an error for any build dependencies you're missing, install them with `sudo apt install ...`.

### Arch

The `PKGBUILD` has enough already.

Installing
----------

### Debian

The above step places `kframework_X.Y.Z_amd64.deb` in the directory above the K repo.
Call:

```
sudo dpkg -i kframework_X.Y.Z_amd64.deb
```

It will fail with some errors because of missing runtime dependencies, do:

```
sudo apt install -f
```

which will install the extra runtime dependencies.

### Arch

Run:

```
makepkg -si
```
