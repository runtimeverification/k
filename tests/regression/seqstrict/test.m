load example-compiled
select META-LEVEL .
rew metaSearch(upModule('ISSUE, false), 'start.Bag, 'bad.Bag, nil, '!, unbounded, 0) . ---@ test1 failure
