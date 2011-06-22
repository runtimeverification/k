load imppp-compiled
rew run('p1) .
rew run('p2) .
rew run('p6) .
rew run('p7) .
search[2] run('p13) =>! B:Bag .
rew run('p15,Int 10(.List{K})) .
rew run('p16,Int 10(.List{K})) .
--- search run('p17,Int 3(.List{K})) =>! B:Bag .
--- commented out because it is apparently blowing out of memeory
