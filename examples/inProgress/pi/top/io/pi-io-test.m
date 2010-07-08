load pi-io-compiled

rew run('p1) .

search run('p1) =>! B:Bag .
show search graph  .


rew run('p2,Id x(.List{K})) .


rew run('p3,(Id x(.List{K}),,Id y(.List{K}),,Id z(.List{K}))) .

search run('p3,(Id x(.List{K}),,Id y(.List{K}),,Id z(.List{K}))) =>! B:Bag .

rew run('p4,(Id x(.List{K}),,Id y(.List{K}),,Id x(.List{K}))) .

