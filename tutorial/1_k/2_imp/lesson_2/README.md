<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Defining a Configuration

Here we learn how to define a configuration in K.  We also learn how to
initialize and how to display it.

As explained in the overview presentation on K, configurations are quite
important, because all semantic rules match and apply on them.
Moreover, they are the backbone of *configuration abstraction*, which allows
you to only mention the relevant cells in each semantic rule, the rest of
the configuration context being inferred automatically.  The importance of
configuration abstraction will become clear when we define more complex
languages (even in IMP++).  IMP does not really need it.  K configurations
are constructed making use of cells, which are labeled and can be arbitrarily
nested.

Configurations are defined with the keyword `configuration`.  Cells are
defined using an XML-ish notation stating clearly where the cell starts
and where it ends.

While not enforced by the tool, we typically like to put the entire
configuration in a top-level cell, called T.  So let's define it:

    configuration <T>...</T>

Cells can have other cells inside.  In our case of IMP, we need a cell to
hold the remaining program, which we typically call k, and a cell to hold
the program state.  Let us add them:

    configuration <T> <k>...</k> <state>...</state> </T>

K allows us to also specify how to initialize a configuration at the same
time with declaring the configuration.  All we have to do is to fill in
the contents of the cells with some terms.  The syntactic categories of
those terms will also indirectly define the types of the corresponding
cells.

For example, we want the k cell to initially hold the program that is passed
to krun.  K provides a builtin configuration variable, called $PGM, which is
specifically designed for this purpose: krun will place its program there
(after it parses it, or course).  The K tool allows users to define their own
configuration variables, too, which can be used to develop custom
initializations of program configurations with the help of krun; this can be
quite useful when defining complex languages, but we do not discuss it in
this tutorial.

    configuration <T> <k> $PGM </k> <state>...</state>  </T>

Moreover, we want the program to be a proper Pgm term (because we do not
want to allow krun to take fragments of programs, for example, statements).
Therefore, we tag $PGM with the desired syntactic category, pgm:

    configuration <T> <k> $PGM:Pgm </k> <state>...</state>  </T>

Like for other variable tags in K, a run-time check will be performed and the
semantics will get stuck if the passed term is not a well-formed program.

We next tell K that the state cell should be initialized with the empty map:

    configuration <T> <k> $PGM:Pgm </k> <state> .Map </state>  </T>

Recall that in K `.` stands for *nothing*.  However, since there are various
types of nothing, to avoid confusion we can suffix the `.` with its desired
type.  K has several builtin data-types, including lists, sets, bags, and
maps.  `.Map` is the empty map.

Compile imp.k and run several programs to see how the configuration is
initialized as desired.

Also, compile with the option `--pdf`, to see how configurations are displayed
in the documentation: like nested labeled bubbles, where each bubble is a cell.

When configurations get large, and they do when defining large programming
languages, you may want to color the cells in order to more easily distinguish
them.  This can be easily achieved using the `color` cell attribute, following
again an XML-ish style:

    configuration <T color="yellow">
                    <k color="green"> $PGM:Pgm </k>
                    <state color="red"> .Map </state>
                  </T>

Compile again with the `--pdf` option and take a look at the new configuration.
The cells should be now colored as indicated.

In the next lesson we will learn how to write rules that involve cells.
