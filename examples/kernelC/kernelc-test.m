rew run('pSum) .
rew run('pCollatz) .
rew run('pBufferOverflow) .
rew run('pStrTest) .
rew run('pStrErr) .
rew run('pAllocatePrintFree) .
rew run('pAllocatePrintReversePrintFree) .
rew run('pAllocateBadPrint) .
rew run('pSimpTest) .
rew run('pSeqQuickSort, (Int 7(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) .
rew run('pConcQuickSort, (Int 7(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) .

---search[1] run('pConcQuickSort, (Int 7(.List{K}),,Int 5(.List{K}),,Int 9(.List{K}),,Int 1(.List{K}),,Int 3(.List{K}),,Int 8(.List{K}),,Int 4(.List{K}),,Int 10(.List{K}),, Int 0(.List{K}))) =>*  < raceDetected > B:Bag </ raceDetected > .
rew run('pRace1) .
search[1] run('pRace1) =>*   < raceDetected > B:Bag </ raceDetected > .

rew run('pAccount1) .
search[1] run('pAccount2) =>* < raceDetected > B:Bag </ raceDetected > .

rew run('pAccount2) .
search[1] run('pAccount2) =>* < raceDetected > B:Bag </ raceDetected > .

frew run('pAccount3) .
search[1] run('pAccount3) =>* < raceDetected > B:Bag </ raceDetected > .
search[1] run('pAccount3) =>! < T > B:Bag </ T > .
frew run('pAccount4) .
search[1] run('pAccount4) =>* < raceDetected > B:Bag </ raceDetected > .
search[1] run('pAccount4) =>! < T > B:Bag </ T > .

frew run('pAccount5) .
search[1] run('pAccount5) =>* < raceDetected > B:Bag </ raceDetected > .
search[1] run('pAccount5) =>! < T > B:Bag </ T > .
---show search graph .
---frew run('pRace2) .
---)
