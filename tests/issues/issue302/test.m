load example-compiled
---set trace on .
rew start .
search start =>! B:Bag .
q
select META-LEVEL .
rew metaSearch(upModule('ISSUE, false), 'start.Bag, 'end.Bag, nil, '!, unbounded, 0)  . ---@ test1 end
