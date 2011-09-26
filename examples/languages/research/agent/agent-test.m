load agent-compiled

---(
rew run('p1) .
rew run('p2) .
rew run('p3) .
rew run('p4) .
rew run('p5) .
rew run('p6) .
rew run('p7) .
rew run('p8) .
rew run('p9) .
rew run('p10) .
rew run('p11) .
rew run('p12) .
rew run('p13) .
rew run('p14, (Int 10(.List{K}),,Int -2(.List{K}),,Int -1(.List{K}),,Int 0(.List{K}),,Int 10(.List{K}))) .
rew run('p15, (Int 10(.List{K}),,Int -2(.List{K}),,Int -1(.List{K}),,Int 0(.List{K}),,Int 10(.List{K}))) .
rew run('p16) .
---search[1] run('p17) =>! B:[Bag] .
---search run('p18) =>! B:[Bag] .
---search run('p19) =>! B:[Bag] .
---search run('p20) =>! B:[Bag] .
---search run('p21) =>! B:[Bag] .
---search run('p22) =>! B:[Bag] .
---search run('p23) =>! B:[Bag] .
---search run('p24) =>! B:[Bag] .
rew run('p25) .
rew run('p26) .
rew run('p27) .
rew run('p28) .
rew run('p29) .
---)
