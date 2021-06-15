K Framework 5.2.0
=================

**TODO**: Current as of 61eec9a398

```k
Feature Additions
-----------------

* 3eebe42d24 - Search in llvm backend (#1978)                                                   - Dwight Guth
* c4c5582232 - Fix constant folding PR quadratic behavior (#1958)                               - Dwight Guth
* 2403a5c09a - Revert "Constant folding of Int, Float, String, and Bool" (#1946)                - Radu Mereuta (tag: v5.1.7)
* 42dbd6af22 - Constant folding of Int, Float, String, and Bool (#1896)                         - Dwight Guth (tag: v5.1.6)

Feature Removals
----------------

* 3dfdd085d0 - Remove `imports syntax` to clean out the code (#1927)                            - Radu Mereuta

Kore Encoding
-------------

* e6161cb9d9 - Exclude simplification rules in concrete backend (#1983)                         - Radu Mereuta

Documentation
-------------

* 2b5da87ca7 - optimize array extensions (#1952)                                                - Dwight Guth
* 61eec9a398 - Lesson 12: syntactic lists (#2023)                                               - Dwight Guth (tag: v5.1.62, upstream/master)
* c017a74a88 - Lesson 11: Casts (#2018)                                                         - Dwight Guth (tag: v5.1.61)
* 2f589a36ba - Lesson 10: Strings (#2011)                                                       - Dwight Guth
* c4151b2d75 - Declare encoding/decoding between Bytes and String in domains.md (#2002)         - Andrei Burdușa
* ef39d1f0fb - Lesson 9: unparsing and formatting (#2005)                                       - Dwight Guth (tag: v5.1.51)
* 6e1da47009 - Misc tutorial improvements (#2006)                                               - Dwight Guth
* 58ea05e4ee - Lesson 8: Literate Programming (#1994)                                           - Dwight Guth
* 1c46185602 - Update pending-documentation.md: side conditions are supported for smt-lemma rules (#1995) - Andrei Burdușa (tag: v5.1.42)
* 85d5664732 - fix typos in tutorial lessons (#2000)                                            - Dwight Guth (tag: v5.1.41)
* 561e0f6e8c - kast.md: Document what each #Layout production does (#1997)                      - Nishant Rodrigues (tag: v5.1.40)
* 732519f55d - Lesson 7: Side conditions and rule priority (#1993)                              - Dwight Guth
* 7a4cb62fa8 - Lesson 6: integers and booleans (#1992)                                          - Dwight Guth
* 58cc924ba8 - Lesson 5: modules, imports, and requires (#1973)                                 - Dwight Guth
* 398356f4d2 - lessons 3/4: parsing and disambiguation (#1847)                                  - Dwight Guth (tag: v5.1.21)
* a7f37e4a45 - add an exercise to lesson 2 (#1970)                                              - Dwight Guth (tag: v5.1.19)
* 35a7b6d37d - Documentation update for symbol, klabel, simplification, and Z3 version (#1930)  - Everett Hildenbrandt (tag: v5.1.3)

Dependency Updates
------------------

* cbce3c86b1 - Update dependency: llvm-backend/src/main/native/llvm-backend (#2021)             - rv-jenkins
* c206850a7e - Update dependency: haskell-backend/src/main/native/haskell-backend (#2009)       - rv-jenkins
* 68a1a25b64 - Update dependency: haskell-backend/src/main/native/haskell-backend (#2008)       - rv-jenkins
* 94148f87ee - Update dependency: haskell-backend/src/main/native/haskell-backend (#2003)       - rv-jenkins
* a64e023e39 - Update dependency: haskell-backend/src/main/native/haskell-backend (#1980)       - rv-jenkins (tag: v5.1.39)
* f15c91057d - Update dependency: haskell-backend/src/main/native/haskell-backend (#1976)       - rv-jenkins (tag: v5.1.25)
* 29e1e20d1f - Update dependency: haskell-backend/src/main/native/haskell-backend (#1971)       - rv-jenkins (tag: v5.1.23)
* 051c46a3e1 - Update dependency: web/k-web-theme (#1974)                                       - rv-jenkins (tag: v5.1.22)
* 6dff3c2663 - Update dependency: haskell-backend/src/main/native/haskell-backend (#1939)       - rv-jenkins (tag: v5.1.20)
* 6ac93bc91e - Update dependency: llvm-backend/src/main/native/llvm-backend (#1959)             - rv-jenkins (tag: v5.1.14)
* de29b8fcff - Bump commons-io from 2.4 to 2.7 in /kernel (#1941)                               - dependabot[bot] (tag: v5.1.13)
* 925136722e - Update dependency: llvm-backend/src/main/native/llvm-backend (#1954)             - rv-jenkins
* c7c2dac7e0 - Update dependency: haskell-backend/src/main/native/haskell-backend (#1932)       - rv-jenkins

Parsing Performance
-------------------

* c747292f23 - Parse record productions in linear time (#2012)                                  - Radu Mereuta
* 787add05a4 - Update Location of cached Bubbles (#2001)                                        - Radu Mereuta (tag: v5.1.45)
* e655bcc108 - Parse configs in parallel (#1996)                                                - Radu Mereuta
* b9581a3bd4 - Refactor rule and config caching (#1962)                                         - Radu Mereuta
* 9f8a111e34 - Optimize POSet performance (#1944)                                               - Radu Mereuta (tag: v5.1.8)

Website Improvements
--------------------

* 0186735835 - Fixed bunch of broken links (#2013)                                              - Yiyi Wang (tag: v5.1.58)

Packaging/Deployment
--------------------

* 0ebf654633 - Revert "when building brew, update from llvm 8 to llvm 12 (#2014)"               - Dwight Guth
* bae0b77226 - when building brew, update from llvm 8 to llvm 12 (#2014)                        - Dwight Guth
* 800cd8cf2c - test.nix: Find the package version file (#2004)                                  - Thomas Tuegel
* 312e54d183 - Nix: Fix kserver (#1884)                                                         - Thomas Tuegel (tag: v5.1.47)
* 506d2019e1 - Remove platform independent K binary (#1975)                                     - Everett Hildenbrandt (tag: v5.1.24)
* cf17ed5497 - Pass flag to build Nix package with LTO through to the LLVM backend (#1964)      - Andrei Burdușa (tag: v5.1.17)
* 2225e0ef3a - Add flag to build Nix package with LTO (#1960)                                   - Andrei Burdușa (tag: v5.1.16, master)
* 04c747e243 - fix arch packaging (#1951)                                                       - Dwight Guth (tag: v5.1.11)
* cb7dadd046 - Add bison to hostInputs in k.nix (#1948)                                         - Andrei Burdușa
* 4c363a4ceb - Fix and simplify release trigger (#1935)                                         - Everett Hildenbrandt

Misc
----

* ff680bd9d8 - Attributes have restricted value type (#2010)                                    - Dwight Guth
* c294c372b9 - automatically remove `not-lr1` modules from Bison grammars (#1999)               - Dwight Guth (tag: v5.1.46)
* 7a482220be - Don't wrap exception messages to 80 chars in integration tests (#1987)           - Andrei Burdușa
* f244e528a1 - Add --no-exc-wrap to krun (#1991)                                                - Radu Mereuta (tag: v5.1.34)
* cf8d4265a8 - Remove experimental help menu (#1929)                                            - Everett Hildenbrandt (tag: v5.1.33)
* 04cf28cea4 - Normalize paths instead of canonicalize (#1984)                                  - Radu Mereuta (tag: v5.1.29)
* d939ea3a4e - Keep indentation for long lines (#1981)                                          - Radu Mereuta
* b93192ee41 - Update JavaCC library in Maven (#1985)                                           - Radu Mereuta
* f4526b0322 - Force mvn to use en_US locale for tests (#1982)                                  - Radu Mereuta (tag: v5.1.26)
* b3ee477caa - Add MAP import to all modules containing configs (#1965)                         - Radu Mereuta
* 31a97a54b8 - kast tool should respect --output-file (#1931)                                   - Everett Hildenbrandt
```

K Framework 5.1.0
=================

Features
--------

-   Use the `claim` keyword instead of `rule` for proof obligations.
-   Bison parser is full-featured and supports external ahead-of-time `macro` and `macro-rec` expansion.
-   The new `krun` pipeline is written in `bash`, and can often skip running the Java frontend altogether.
    In particular, if `kompile` is called using the Bison parser (`--gen-bison-parser` or `--gen-glr-bison-parser`), you get this benefit.
-   K semantic version numbers are re-introduced, and can be expected to increment (rather than relying on git commit IDs).

K Framework 5.0.0
=================

Major changes since version 3.6, not all are documented here.
In particular:

-   No longer user Maude backend for K.
-   OCaml backend was developed, but now is being deprecated in favor of LLVM backend for concrete execution.
-   Java backend was developed, but now is being deprecated in favor of Haskell backend for symbolic execution.
