rew run('pSum) .
rew run('pCollatz) .
rew run('pBufferOverflow, pBufferOverflow.in1) .
rew run('pBufferOverflow, pBufferOverflow.in2) .
rew run('pBufferOverflow, pBufferOverflow.in3) .
rew run('pSeqQuickSort, pSeqQuickSort.in) .
rew run('pConcQuickSort, pSeqQuickSort.in) .
---search[1] run('pConcQuickSort, pSeqQuickSort.in) =>*  < raceDetected > B:Bag </ raceDetected > .
rew run('pAccount2) .
---search[1] run('pAccount2) =>* < raceDetected > B:Bag </ raceDetected > .
---search[1] run('pAccount4) =>* < raceDetected > B:Bag </ raceDetected > .
---search[1] run('pAccount4) =>! < T > B:Bag </ T > .

rew run('pPeterson.c) .
search run('pPeterson.c) =>! B:Bag .
