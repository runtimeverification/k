# The build environment

`package/debian/` holds the *recipes* for K's Debian packages. This directory holds the
*environment* they are built in, and the entry points that drive it.

```
package/build-env/Dockerfile               the build environment
package/build-env/Dockerfile.stack-deps    prerequisite: stack + a warm ~/.stack
package/build-env/Dockerfile.maven-cache   prerequisite: maven + a warm ~/.m2
package/build-env/build-deb                build one deb for one Ubuntu release
package/build-env/test-deb                 install that deb into a clean image, as root
package/build-env/common.sh                the distro and package tables both scripts read
```

```
package/build-env/build-deb noble
package/build-env/test-deb  noble

package/build-env/build-deb jammy kframework-frontend
package/build-env/test-deb  jammy kframework-frontend
```

The second argument selects the package — `kframework` (default) or `kframework-frontend`.
A third names the `.deb`; the default is `<package>_amd64_ubuntu_<distro>.deb`, left at the
root of the checkout. Both scripts can be run from any directory — they `cd` to the checkout
root themselves, because `package/debian/build-package` assumes it. They use `podman` if it is
installed and `docker` otherwise; `CONTAINER_ENGINE` overrides that.

`build-package` *moves* files out of `package/debian/` into a top-level `debian/`, so a second
`build-deb` run needs a clean tree. That is pre-existing behaviour, noted here because it is
surprising the first time.

## Why it lives here

It used to be three Dockerfiles under `.github/workflows/`, invoked by a composite action.
That made the environment reachable only from a GitHub workflow, and the knowledge of *how to
invoke it* was not written down as anything executable — it was one shell block inside an
action definition, and then copied, imperfectly, into whatever else needed to build a deb.

That knowledge is not small, which is the point:

- the main image `FROM`s two others that must be built **first**, tagged exactly
  `stack:<distro>-<version>` and `maven:<distro>-<version>`. Skip them and the build tries to
  pull `docker.io/library/stack:…` off the internet.
- `Z3_VERSION` comes from `deps/z3` and `K_VERSION` from `package/version` — read from the
  tree, so the image cannot be built against a different z3 than the source declares.
- `JDK_VERSION` is declared with **no default**, so a caller that forgets it installs the
  package `openjdk--jdk` and fails several minutes in, on an apt error that never mentions a
  build arg. noble wants 21, jammy 17.

Moving CI to the internal forge deletes `.github/` entirely. Rather than move the same
arrangement sideways, the environment moved next to the recipes it builds, behind two scripts
that a forge workflow, the release repository, and a developer's shell can all call the same
way.

## Two things that are easy to get wrong

**The checkout mounts at `/opt/workspace/source`, not at `/opt/workspace`.**
`dpkg-buildpackage` writes the `.deb` to the *parent* of the directory it builds in, and
`build-package` globs `../<package>_*_amd64.deb` to find it. Mount the checkout at
`/opt/workspace` and that parent is `/`, which the non-root build user cannot write — the
build then fails from inside `dpkg-buildpackage`, naming neither the mount nor the reason. The
`Dockerfile` creates `/opt/workspace` owned by the build user so the parent is writable.

**The package must be tested somewhere other than the build environment.** That image has
every build dependency already installed, so a missing or wrong entry in `debian/control`
would install cleanly there and fail only for a user. `test-deb` uses a bare `ubuntu:<distro>`
for that reason, and needs root, which the build environment does not have. It also picks the
test script from the package name, so the frontend deb cannot be checked with the full K test.

## The account inside the image

The build runs as an account whose uid/gid match the caller's, so files written to the
bind-mounted checkout come back owned by whoever ran the build. Only the *ids* matter for
that, so the Dockerfiles name the account themselves (`builder`) and callers pass ids alone.

Here that is load-bearing rather than tidy: the main image does
`COPY --from=STACK /home/$USER/.stack` and `COPY --from=MAVEN /home/$USER/.m2`, so all three
images must agree on the name. Taking it from the caller meant every one of the three builds
had to be passed the same value, and a mismatch produces an image that is merely missing its
caches — a slow build, not an error.

Passing the caller's name through also collides with the base image: `ubuntu:noble` has an
`ubuntu` account at uid/gid 1000, and `users` (gid 100) is the primary group of many developer
accounts; either makes `useradd` fail minutes into the build. `-o` lets the ids be shared
rather than deleting a system account that something else uses.
