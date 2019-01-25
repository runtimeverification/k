<!-- Copyright (c) 2014-2019 K Team. All Rights Reserved. -->

*Dear reader: these `NOTES.md` documents are mostly for myself (Grigore), to
keep track of changes and updates that need to be made as things evolve
in the K framework.  You can safely ignore them.  However, if you are curious
how things will change and decide to read them, I would be grateful if you
let me know whenever you find inconsistencies or things that I forgot to
mention here.  Or even better, feel free to make pull requests with suggested
changes or updates.*

Global changes that need to be made:

* Replace `when` in rules with `requires`

Things to revise each time the structure of the tutorial changes:

* `1_k\2_imp\lesson_1\README.md` refers to Tutorial 1
* `1_k\2_imp\lesson_4\README.md` refers to Lesson 1
* `1_k\2_imp\lesson_4\README.md` refers to Tutorial 1, Lesson 2.5
* `1_k\3_lambda++\lesson_1\README.md` refers to Lesson 8, Tutorial 1
* `1_k\3_lambda++\lesson_1\exercises refers to Lesson 1, tests/config.xml
* `1_k\3_lambda++\lesson_2\README.md` Lesson 1, Tutorial 1; Tutorial 6; Part 1, 2
* `1_k\3_lambda++\lesson_3\README.md` refers to Lesson 7, Tutorial 1
* `1_k\3_lambda++\lesson_4\README.md` refers to Lesson 1
* `1_k\3_lambda++\lesson_5\README.md` refers to Lesson 4, Lesson 8 and Lesson 7 of Tutorial 1
* `1_k\3_lambda++\lesson_6\README.md` refers to Parts 3 and 4 of the tutorial
* `1_k\4_imp++\lesson_1\README.md` refers to Lesson 4, Tutorial 2; also Tutorial 3 (at the end)
* `1_k\4_imp++\lesson_2\README.md` refers to Tutorial 3; Tutorial 2
* `1_k\4_imp++\lesson_3\README.md` refers to Lesson 1, Lesson 6
* `1_k\4_imp++\lesson_4\README.md` refers to Tutorial 6
* `1_k\4_imp++\lesson_5\README.md` refers to Lesson 4; Tutorial 3
* `1_k\4_imp++\lesson_6\README.md` refers to Lesson 3
* `1_k\4_imp++\lesson_7\README.md` refers to Lesson 1, 6
* `1_k\5_types\lesson_1\README.md` refers to Part 4; SIMPLE
* `1_k\5_types\lesson_2\NOTES/README.md` refer to Tutorial 1
* `1_k\5_types\lesson_3\README.md` refers to Part 1; Lesson 1,2
* `1_k\5_types\lesson_4\README.md` refers to Part 1, and to Lessons 2 and 3
* `1_k\5_types\lesson_5\README.md` refers to Lessons 4, 3, 2
* `1_k\5_types\lesson_6\README.md` refers to Lesson 5; SIMPLE, KOOL, IMP++
* `1_k\5_types\lesson_7\README.md` refers to Lesson 4, 8, 9
* `1_k\5_types\lesson_8\README.md` refers to Lessons 5, 7
* `1_k\5_types\lesson_9\README.md` refers to Lessons 8, 5, 7, 4
* 

`1_k\4_imp++\lesson_2\README.md` states "generates a term of the form
`symNat(n)` of sort `Nat`", but the representation of symbolic numbers may
have changed

Describe/use/explain/justify the terminology "the `<k/>` cell" as opposed to "the `k` cell".

Would it be a good idea to make the README files self contained, that is,
to include the entire `lang.k` code in them, spread over the entire README, as things
are discussed?  In case we decide not to, make sure that the code snippets mentioned
in the READMEs are in perfect correspondence to the code in the actual .k definitions.
Maybe add a tag before each code snippet saying what file and what lines in that
file comes from, then we can use a script to check them to be identical.

`1_k\5_types\lesson_4\README.md` refers to *polymorphism*, but some may say that is not precisely 
polymorphism, because the types are not universally quantified.  Explain that better.

Modify the entire tutorial to use `.` or, if needed, `.::Map`, etc.,
instead of `.Map`, etc..  Check for each instance specifically, because
the surrounding text may also need to be modified.

We are still using the `--pdf` option to `kompile` at many places in the
tutorial, although in some places at the beginning we replaced it with the
new approach, `kdoc`.  It is actually not clear that we should switch to
`kdoc`, because after all the Latex generation is still a backend.  So it
makes sense to implement it as such, instead of as a different tool.

We sometimes use "Kompile", or "kompile", as a verb instead of "Compile",
or "compile", to indicate that we mean compilation with K.  Similarly for
"Krun", or "krun", instead of "Run" or "run".

Add citations to:

* chemical abstract machine
* logics, where the distinction between side condition and premise is explained
* reduction semantics with evaluation contexts

Replace `I1 +Int I2`, `notBool B`, etc., with `(I1 + I2)@INT`, `(not B)@Bool`,
etc., when we have module qualification in place and working.

Explain `isSort(T)` for all sorts `Sort`, in one place, when it is first used.
Explain also that `T:Sort` yields a side condition `isSort(T)`.

Currently all the K collections are "untyped", that is, over the sort `K`.
In the future we want to have parametric collections.  Make sure the tutorial
is systematically changed when this happens.

See issue #2023 and modify tutorial/1_k/2_imp/lesson_4 accordingly, if needed.

All definitions, and corresponding READMEs, should be changed to take advantage
of modules and module operations.  Ideally, we'd like to have no code repetition
in any examples, except for demonstration purposes.

In the PL semantics book, define print(AExps) to have the same semantics as in
IMP++: evaluates and prints each of its arguments in order (as opposed to
first evaluate all of them and then print them---for example, if the second
argument performs a division by zero, I still want to print the first argument.)

Windows user currently need to replace "kast" with "kast.bat" everywhere in their
config.xml files.  Hopefully this will be fixed soon.
