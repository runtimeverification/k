rew run('pSum) .
rew run('pCollatz) .
rew run('pBufferOverflow, pBufferOverflow.in1) .
rew run('pBufferOverflow, pBufferOverflow.in2) .
rew run('pBufferOverflow, pBufferOverflow.in3) .
---(
rew run('pStrTest) .
rew run('pStrErr) .
rew run('pAllocatePrintFree) .
rew run('pAllocatePrintReversePrintFree) .
rew run('pAllocateBadPrint) .
rew run('pSimpTest) .
---)
rew run('pSeqQuickSort, pSeqQuickSort.in) .
rew run('pConcQuickSort, pSeqQuickSort.in) .
---search[1] run('pConcQuickSort, pSeqQuickSort.in) =>*  < raceDetected > B:Bag </ raceDetected > .
---(
rew run('pRace1) .
---search[1] run('pRace1) =>*   < raceDetected > B:Bag </ raceDetected > .
rew run('pAccount1) .
---search[1] run('pAccount2) =>* < raceDetected > B:Bag </ raceDetected > .
---)
rew run('pAccount2) .
---search[1] run('pAccount2) =>* < raceDetected > B:Bag </ raceDetected > .
---search[1] run('pAccount4) =>* < raceDetected > B:Bag </ raceDetected > .
---search[1] run('pAccount4) =>! < T > B:Bag </ T > .
eof

frew run('pAccount5) .
---search[1] run('pAccount5) =>* < raceDetected > B:Bag </ raceDetected > .
---search[1] run('pAccount5) =>! < T > B:Bag </ T > .
---show search graph .
---frew run('pRace2) .
---)
