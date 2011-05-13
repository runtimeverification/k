load graph-coloring-semantics-compiled

search [1, 100] in GRAPH-COLORING-SEMANTICS : < top > 
 < k > 'run(.List{K}) </ k > 
 < graphType > (.).K </ graphType > 
 < time > Int 0(.List{K}) </ time > 
 < total-cost > Int 0(.List{K}) </ total-cost > 
 < graph > 
  < g-edge > 
   < ge-color > String "blue"(.List{K}) </ ge-color > 
   < ge-from > String "d"(.List{K}) </ ge-from > 
   < ge-length > Int 8(.List{K}) </ ge-length > 
   < ge-name > String "dg"(.List{K}) </ ge-name > 
   < ge-to > String "g"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A2"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "blue"(.List{K}) </ ge-color > 
   < ge-from > String "h"(.List{K}) </ ge-from > 
   < ge-length > Int 8(.List{K}) </ ge-length > 
   < ge-name > String "hi"(.List{K}) </ ge-name > 
   < ge-to > String "i"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "B1"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "blue"(.List{K}) </ ge-color > 
   < ge-from > String "i"(.List{K}) </ ge-from > 
   < ge-length > Int 5(.List{K}) </ ge-length > 
   < ge-name > String "ik"(.List{K}) </ ge-name > 
   < ge-to > String "k"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "B2"(.List{K})) </ ge-cards > 
   < ge-dependencies > SetItem(String "gi"(.List{K})) SetItem(String "hi"(.List{K})) </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "green"(.List{K}) </ ge-color > 
   < ge-from > String "b"(.List{K}) </ ge-from > 
   < ge-length > Int 8(.List{K}) </ ge-length > 
   < ge-name > String "bf"(.List{K}) </ ge-name > 
   < ge-to > String "f"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A1"(.List{K})) SetItem(String "A2"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "green"(.List{K}) </ ge-color > 
   < ge-from > String "e"(.List{K}) </ ge-from > 
   < ge-length > Int 3(.List{K}) </ ge-length > 
   < ge-name > String "eh"(.List{K}) </ ge-name > 
   < ge-to > String "h"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A1"(.List{K})) SetItem(String "B1"(.List{K})) </ ge-cards > 
   < ge-dependencies > SetItem(String "ae"(.List{K})) SetItem(String "fe"(.List{K})) </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "green"(.List{K}) </ ge-color > 
   < ge-from > String "f"(.List{K}) </ ge-from > 
   < ge-length > Int 3(.List{K}) </ ge-length > 
   < ge-name > String "fg"(.List{K}) </ ge-name > 
   < ge-to > String "g"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A2"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "green"(.List{K}) </ ge-color > 
   < ge-from > String "h"(.List{K}) </ ge-from > 
   < ge-length > Int 6(.List{K}) </ ge-length > 
   < ge-name > String "hj"(.List{K}) </ ge-name > 
   < ge-to > String "j"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "B1"(.List{K})) SetItem(String "B2"(.List{K})) </ ge-cards > 
   < ge-dependencies > SetItem(String "eh"(.List{K})) </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "purple"(.List{K}) </ ge-color > 
   < ge-from > String "f"(.List{K}) </ ge-from > 
   < ge-length > Int 3(.List{K}) </ ge-length > 
   < ge-name > String "fe"(.List{K}) </ ge-name > 
   < ge-to > String "e"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A1"(.List{K})) SetItem(String "A2"(.List{K})) </ ge-cards > 
   < ge-dependencies > SetItem(String "bf"(.List{K})) SetItem(String "cf"(.List{K})) </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "purple"(.List{K}) </ ge-color > 
   < ge-from > String "g"(.List{K}) </ ge-from > 
   < ge-length > Int 5(.List{K}) </ ge-length > 
   < ge-name > String "gi"(.List{K}) </ ge-name > 
   < ge-to > String "i"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A2"(.List{K})) SetItem(String "B2"(.List{K})) </ ge-cards > 
   < ge-dependencies > SetItem(String "dg"(.List{K})) SetItem(String "fg"(.List{K})) </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "red"(.List{K}) </ ge-color > 
   < ge-from > String "a"(.List{K}) </ ge-from > 
   < ge-length > Int 8(.List{K}) </ ge-length > 
   < ge-name > String "ae"(.List{K}) </ ge-name > 
   < ge-to > String "e"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A1"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "red"(.List{K}) </ ge-color > 
   < ge-from > String "c"(.List{K}) </ ge-from > 
   < ge-length > Int 5(.List{K}) </ ge-length > 
   < ge-name > String "cf"(.List{K}) </ ge-name > 
   < ge-to > String "f"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A2"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > 
  < g-edge > 
   < ge-color > String "red"(.List{K}) </ ge-color > 
   < ge-from > String "g"(.List{K}) </ ge-from > 
   < ge-length > Int 13(.List{K}) </ ge-length > 
   < ge-name > String "gl"(.List{K}) </ ge-name > 
   < ge-to > String "l"(.List{K}) </ ge-to > 
   < ge-cards > SetItem(String "A2"(.List{K})) SetItem(String "B2"(.List{K})) </ ge-cards > 
   < ge-dependencies > (.).Set </ ge-dependencies > </ g-edge > </ graph > 
 < meta > (.).Bag </ meta > 
 < network > 
  < master > String "master"(.List{K}) </ master > 
  < node > 
   < n-name > String "blue"(.List{K}) </ n-name > 
   < n-edges > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "green"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "red"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 10(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "master"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > </ n-edges > 
   < processors > 
    < processor > 
     < p-color > String "blue"(.List{K}) </ p-color > 
     < p-name > String "blue"(.List{K}) </ p-name > </ processor > </ processors > 
   < n-cards > SetItem(String "A1"(.List{K})) SetItem(String "A2"(.List{K})) SetItem(String "B1"(.List{K})) SetItem(String "B2"(.List{K})) </ n-cards > 
   < n-server-names > (.).Set </ n-server-names > </ node > 
  < node > 
   < n-name > String "green"(.List{K}) </ n-name > 
   < n-edges > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "blue"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 20(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "red"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > </ n-edges > 
   < processors > 
    < processor > 
     < p-color > String "green"(.List{K}) </ p-color > 
     < p-name > String "green"(.List{K}) </ p-name > </ processor > </ processors > 
   < n-cards > (.).Set </ n-cards > 
   < n-server-names > (.).Set </ n-server-names > </ node > 
  < node > 
   < n-name > String "master"(.List{K}) </ n-name > 
   < n-edges > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "purple"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "red"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "blue"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "green"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > </ n-edges > 
   < processors > (.).Bag </ processors > 
   < n-cards > (.).Set </ n-cards > 
   < n-server-names > SetItem(String "0"(.List{K})) SetItem(String "1"(.List{K})) </ n-server-names > </ node > 
  < node > 
   < n-name > String "purple"(.List{K}) </ n-name > 
   < n-edges > 
    < n-edge > 
     < ne-cost > Int 0(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "master"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 10(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "green"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 10(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "blue"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 20(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "red"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > </ n-edges > 
   < processors > 
    < processor > 
     < p-color > String "purple"(.List{K}) </ p-color > 
     < p-name > String "purple"(.List{K}) </ p-name > </ processor > </ processors > 
   < n-cards > (.).Set </ n-cards > 
   < n-server-names > (.).Set </ n-server-names > </ node > 
  < node > 
   < n-name > String "red"(.List{K}) </ n-name > 
   < n-edges > 
    < n-edge > 
     < ne-cost > Int 10(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "green"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 10(.List{K}) </ ne-cost > 
     < ne-length > Int 3(.List{K}) </ ne-length > 
     < ne-to > String "purple"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > 
    < n-edge > 
     < ne-cost > Int 20(.List{K}) </ ne-cost > 
     < ne-length > Int 2(.List{K}) </ ne-length > 
     < ne-to > String "master"(.List{K}) </ ne-to > 
     < ne-servers > (.).Bag </ ne-servers > </ n-edge > </ n-edges > 
   < processors > 
    < processor > 
     < p-color > String "red"(.List{K}) </ p-color > 
     < p-name > String "red"(.List{K}) </ p-name > </ processor > </ processors > 
   < n-cards > (.).Set </ n-cards > 
   < n-server-names > (.).Set </ n-server-names > </ node > 
  < all-edge-server-names > (.).Set </ all-edge-server-names > 
  < all-node-processor-names > (.).Set </ all-node-processor-names > 
  < all-node-server-names > (.).Set </ all-node-server-names > 
  < working-processor-names > (.).Set </ working-processor-names > 
  < working-server-names > (.).Set </ working-server-names > </ network > 
 < cards > (.).Set </ cards > 
 < dependencies > (.).Set </ dependencies > </ top > =>! B:BagItem .
