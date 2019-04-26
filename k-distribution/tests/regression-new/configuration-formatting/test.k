module TEST
  imports INT

  configuration
    <t>
      <k> $PGM </k>
      <foo format="foo(%2)"> $PGM:Int </foo>
      <ms>
        <m multiplicity="*" type="Map">
          <id> 2:Int </id>
          <val> 2:Int </val>
        </m>
      </ms>
      <ls> <l multiplicity="*" type="List"> 2:Int </l> </ls>
      <ss> <x multiplicity="*" type="Set"> 2:Int </x> </ss>
      <bs> <b multiplicity="*"> 2:Int </b> </bs>
    </t>

  rule <ms> ( .Bag
           => <m> <id> 1 </id> <val> 1 </val> </m>
              <m> <id> 2 </id> <val> 1 </val> </m>
              )
       </ms>
  rule <ls> ( .Bag
            => <l> 1 </l>
               <l> 1 </l>
               )
       </ls>
  rule <ss> ( .Bag
             => <x> 1 </x>
                <x> 1 </x>
              )
       </ss>
  rule <bs> ( .Bag
           => <b> 1 </b>
              <b> 1 </b>
              )
       </bs>
endmodule
