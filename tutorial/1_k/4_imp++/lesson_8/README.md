<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

### Wrapping up Larger Languages

In this lesson we wrap up IMP++'s semantics and also generate its poster.
While doing so, we also learn how to display larger configurations in order
to make them easier to read and print.

Note that we rearrange a bit the semantics, to group the semantics of old
IMP's constructs together, and separate it from the new IMP++'s semantics.

Once we are done adding all the comments, we `kompile` with the documentation
option `--pdf`, and then visualize the generated PDF document.

Everything looks good, except the configuration.  We can move the store, in
and out cells on the next line.  The html-ish tag `<br/>` inserts a line break
in the configuration layout, as you can see in the generated document.

There is a detailed discussion at the end of the document about the
`--superheat`, `--supercool` and `--transition` options of `kompile`.
You may want to check it out.

You can go even further and manually edit the generated Latex document.
You typically want to do that when you want to publish your language
definition, or parts of it, and you need to finely tune it to fit the
editing requirements.  For example, you may want to insert some negative
spaces, etc.

Part 4 of the tutorial is now complete.  At this moment you should know most
of K framework's features and how to use the K tool.  You can now define or
design your own programming languages, and then execute and analyze programs.
