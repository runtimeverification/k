# Maintainer: Dwight Guth <dwight.guth@runtimeverification.com>
pkgname=kframwork
pkgver=5.0.0
pkgrel=1
epoch=
pkgdesc="K framework toolchain. Includes K Framework compiler for K language definitions, and K interpreter and prover for programs written in languages defined in K."
arch=('x86_64')
url="https://github.com/kframework/k"
license=('custom')
groups=()
depends=('java-runtime' 'flex' 'gcc' 'gmp' 'mpfr' 'z3' 'clang' 'yaml-cpp' 'jemalloc' 'opam')
makedepends=('maven' 'jdk-openjdk' 'cmake' 'boost' 'zlib')
checkdepends=()
optdepends=()
provides=()
conflicts=()
replaces=()
backup=()
options=()
install=kframework.install
changelog=
source=()
noextract=()
md5sums=()
validpgpkeys=()

prepare() {
}

build() {
	mvn package -DskipTests
}

check() {
}

package() {
	export DESTDIR="$pkgname-$pkgver/$pkgdir" 
	src/main/scripts/package
	install -Dm644 LICENSE.md "$DESTDIR/usr/share/licenses/$pkgname/LICENSE"
}
