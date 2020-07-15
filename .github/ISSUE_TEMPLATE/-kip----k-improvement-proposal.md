---
name: "[KIP] - K Improvement Proposal"
about: Suggest a new feature for the K Language
title: "[KIP] - DESCRIBE KIP HERE"
labels: kip
assignees: ''

---

**Motivation**

-   Is there a semantics which you are developing which this feature would simplify?
-   Is this feature similar to a feature offered by another programming language?

**Example K Code**

Provide a small K-psuedocode example of what you would like to be able to say.

Example:

I would like to be able to use `foo` instead of `syntax` for declaring AST nodes:

```
foo Bar ::= "newBar" [function]
```

**Documentation**

Provide (initial) documentation for this new feature.

Example:

A user may choose to use `foo` instead of `syntax` when declaring new production in K.
The meaning is exactly identical to `syntax`, but it requires 3 fewer characters to type, which saves on average 17s/month of semantics development.

**Any alternative approaches**

If there is an obvious alternative way to implement this, please briefly describe it here.

Example:

-   Users could also type `fo`, because it's even shorter. But because they are already pressing the `o` key, pressing `o` a second time has been shown to only increase the time per month by 2s (compared to the 17s overall), which means that the added benefit of programmers being familiar with the word `foo` outweighs the performance gains.
-   The keyword `bar` was also considered, but because `foo` has double-`o`, it's faster to type.

**Testing approach**

If the feature is directly testable using the existing K test harness, provide an example test input/output here.
Otherwise, describe the testing approach you would use for this feature.

Example:

We could:

-   Modify `IMP` in the tutorial to use `foo` instead of `syntax` in a few places, or
-   Add the following definition to `tests/regression-new/foo-syntax.k`:

    ```
    module TEST
      imports BOOL
      configuration <k> $PGM:A </k>

      syntax A ::= "blah"
      foo A ::= "halb"

      rule <k> blah => halb ... </k>
    endmodule
    ```

    with the following input file:

    ```
    blah
    ```

    and expected output:

    ```
    halb
    ```
