<!-- Copyright (c) 2010-2015 K Team. All Rights Reserved. -->
K tool, version 3.6
-------------------

K is a rewrite-based executable semantic framework in which programming 
languages, type systems, and formal analysis tools can be defined using
_configurations_, _computations_, and _rules_. Configurations organize
the state in units called _cells_, which are labeled and can be nested.
Computations carry _computational meaning_ as special nested list
structures sequentializing computational tasks, such as fragments of
program. Computations extend the original language abstract syntax. K
(rewrite) rules make it explicit which parts of the term they read-only,
write-only, read-write, or do not care about. This makes K suitable for
defining truly concurrent languages even in the presence of sharing.
Computations are like any other term in a rewriting environment:
they can be matched, moved from one place to another, modified, or deleted.
This makes K suitable for defining control-intensive features such as 
abrupt termination, exceptions, or call/cc.

This distribution contains a tool prototype which implements many of K's
features.  For more on the K framework and how to use the current tool,
go to k/tutorial (start with the README file there), or refer to the
website, which contains video tutorials, at http://www.kframework.org/.

**NOTE**: This README file contains information regarding the stable release of
the K tool indicated in the title above, regardless of whether it came with
the release itself or with subsequent nightly/latest builds.  This file is
updated only when new stable versions are officially released.

**WARNING**: The command line options for kompile, krun, kast and ktest have
recently changed!
Type `--help` with any of these to see the new options, or see CHANGELOG.md
for more details.

New features
------------

For a list of high-level changes since the previous release, please refer to
the file CHANGELOG.md in the current directory.

Developers
----------

See README.md in the root directory of a source distribution or checkout.
