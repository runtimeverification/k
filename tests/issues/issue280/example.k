
module ISSUE is 

  syntax ListId ::= List{#Id,","}

  syntax List{K} ::= `List`{K`} ( ListId )

end module

