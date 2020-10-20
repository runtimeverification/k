requires "test.k"

module A-SPEC
  imports TEST

  claim
    <k> start(I) => end ...</k>
    <set>... (.Set => SetItem(I +Int 1) ?_:Set) ...</set>

  claim
    <k> mid(I) => end ...</k>
    <set>... SetItem(I) (.Set => SetItem(I +Int 1) ?_:Set) ...</set>
    [trusted]
endmodule
