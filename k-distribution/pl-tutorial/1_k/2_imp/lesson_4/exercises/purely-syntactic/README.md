---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

Modify IMP so that the K *followed by* arrow, `~>`, does not explicitly
occur in the definition (it currently occurs in the semantics of
sequential composition).

Hint: make sequential composition `strict(1)` or `seqstrict`, and have
statements reduce to `{}` instead of `.`; and don't forget to make
`{}` a `KResult` (you may need a new syntactic category for that, which
only includes `{}` and is included in `KResult`).
