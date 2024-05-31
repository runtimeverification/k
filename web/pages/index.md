---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

<b style="font-size: 36px; line-height: 1;">K</b> is a rewrite-based
executable semantic framework in which programming languages, type
systems and formal analysis tools can be defined using configurations
and rules.  Configurations organize the state in units called cells,
which are labeled and can be nested.  K rewrite rules make it explicit
which parts of the term are read-only, write-only, read-write, or
unused.  This makes K suitable for defining truly concurrent languages
even in the presence of sharing.  Computations are represented as
syntactic extensions of the original language abstract syntax, using a
nested list structure which sequentializes computational tasks, such
as program fragments.  Computations are like any other terms in a
rewriting environment: they can be matched, moved from one place to
another, modified, or deleted.  This makes K suitable for defining
control-intensive features such as abrupt termination, exceptions, or
call/cc.

## K Tool Download

- Install from the latest [K GitHub Release](https://github.com/runtimeverification/k/releases/latest).
- Install [pyk](https://github.com/runtimeverification/k/tree/master/pyk), K's scripting interface for Python. Check the [API documentation](https://kframework.org/pyk/) for a complete reference of supported features.
- Try our [Editor Support](./editor_support.md) page for links to K syntax highlighting definitions for various popular editors/IDEs. Please feel free to contribute.
- Build or browse the code [on GitHub](https://github.com/runtimeverification/k), where you can also [report bugs](http://github.com/runtimeverification/k/issues).

## Learn K

- <a href="/k-distribution/k-tutorial/README.md">Do the K Tutorial!</a>
- <a href="/docs/user_manual.md">Reference Documentation</a>
- <a href="/docs/cheat_sheet.md">K Cheat Sheet</a>
- <a href="/docs/ktools.md">K Tool Reference</a>
- <a href="/k-distribution/include/kframework/builtin/README.md">K Builtins</a>

## Support

- [Discord Server](https://discord.com/invite/CurfmXNtbN): Most direct way to get support.
- [Matrix Room](https://matrix.to/#/#k:matrix.org): Another way to get support.
- [Telegram](https://t.me/rv_inc): for newsletters and general announcements.

## Resources

- K Approach and Vision (2020): [slide presentation](https://drive.google.com/file/d/1iXda2NyGzKVWxkd02IlXj5Tq5cOM_gNd/view)
- A set of <a href="/k-distribution/pl-tutorial/README.md">reference implementations and tutorials</a> for common programming language features and paradigms is available, although parts of these implementations may not be fully up to date with modern K features.
- Read some papers about K on the [Formal Systems Laboratory (FSL)](https://fsl.cs.illinois.edu/publications/).
- [Matching logic](http://matching-logic.org/) webpage at UIUC (USA).
- A ten-minute overview video [slide presentation](./overview.md).
- A ninety-minute [tutorial video](https://youtu.be/3ovulLNCEQc?list=PLQMvp5V6ZQjOm4JZK15s-WJtQHxOmb2h7), given at ETAPS'16.
- [Optional] A high-level [interview](http://channel9.msdn.com/posts/ICSE-2011-Grigore-Rosu-The-Art-and-Science-of-Program-Verification) about rewrite-based semantics (Wolfram Schulte interviews Grigore Rosu at [ICSE'11](http://2011.icse-conferences.org/).
- [FAQ](./faq.md)
