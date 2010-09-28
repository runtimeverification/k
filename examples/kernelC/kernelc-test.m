---(
rew run('pSum) .
rew run('pCollatz) .
rew run('pAllocatePrintFree) .
rew run('pAllocatePrintReversePrintFree) .
rew run('pStrTest) .
rew run('pStrErr) .
rew run('pAllocateBadPrint) .
rew run('pBufferOverflow) .
rew run('pSimpTest) .
rew run('pSeqQuickSort, (Int 7(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) .
rew run('pConcQuickSort, (Int 7(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) .

search[1] run('pConcQuickSort, (Int 3(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) =>*  < race > B:Bag </ race > .
rew run('pRace1) .

rew run('pAccount1) .
rew run('pAccount2) .
search[1] run('pAccount2) =>* < race > B:Bag </ race > .

---)
frew run('pAccount3) .
search[1] run('pAccount3) =>* < race > B:Bag </ race > .
search[1] run('pAccount3) =>! < T > B:Bag </ T > .
frew run('pAccount4) .
search[1] run('pAccount4) =>* < race > B:Bag </ race > .
search[1] run('pAccount4) =>! < T > B:Bag </ T > .

frew run('pAccount5) .
search[1] run('pAccount5) =>* < race > B:Bag </ race > .
search[1] run('pAccount5) =>! < T > B:Bag </ T > .
---show search graph .
---frew run('pRace2) .
