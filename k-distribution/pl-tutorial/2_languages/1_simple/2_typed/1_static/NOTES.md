---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

While we disallow global variables with the same name, and that includes
vector variables, we currently do not check that function names are distinct
from each other and from other global variables.  Since we can pass functions
around through their names, this can be problematic.  May want to make this
into an exercise in the future.
