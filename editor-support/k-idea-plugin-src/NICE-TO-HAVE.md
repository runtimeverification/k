## Features nice to have

- References support for sorts, labels.
- Interoperability between labels and their syntactic definitions. If usages of a syntactic definition are searched, labels should be displayed as well.
- Quick documentation support for Sorts and Labels.
- Support for predicates isSort(), like isKResult(). whenever we search for usages for a Sort, these predicates should also be listed and the opposite.
- Treating builtin functions like regular functions, navigation support. Just like JDK classes are threated like regular classes by Java IDE.
- Highlighting of rule LHS/RHS when the arrow => is selected. LHS could have a reddish background color and RHS a blueish. Inspired from the highlighting of parentheses.
- Better rendering of documentation. Eventually support for javadoc tags @param, @return, @see.
- Code formatting. This is the only major feature from the tutorial that was not implemented. Both the format adopted in the tutorial and the one from java semantics should be supported. Should be highly configurable.
- Native integration with kompile/krun. Here we can also have navigation from error messages to the target code line.
- Autocomplete in various contexts
- Coloring the cells according to their color attribute.
