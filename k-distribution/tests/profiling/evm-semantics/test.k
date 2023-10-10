// Copyright (c) K Team. All Rights Reserved.

module WORD
  imports public INT
  imports public BOOL
  imports public BYTES
  syntax Int  ::=
    "pow256" [alias]
  | "pow255" [alias]
  | "pow248" [alias]
  | "pow240" [alias]
  | "pow232" [alias]
  | "pow224" [alias]
  | "pow216" [alias]
  | "pow208" [alias]
  | "pow200" [alias]
  | "pow192" [alias]
  | "pow184" [alias]
  | "pow176" [alias]
  | "pow168" [alias]
  | "pow160" [alias]
  | "pow152" [alias]
  | "pow144" [alias]
  | "pow136" [alias]
  | "pow128" [alias]
  | "pow120" [alias]
  | "pow112" [alias]
  | "pow104" [alias]
  | "pow96" [alias]
  | "pow88" [alias]
  | "pow80" [alias]
  | "pow72" [alias]
  | "pow64" [alias]
  | "pow56" [alias]
  | "pow48" [alias]
  | "pow40" [alias]
  | "pow32" [alias]
  | "pow24" [alias]
  | "pow16" [alias]
  | "pow8" [macro]
  rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  rule pow255 => 57896044618658097711785492504343953926634992332820282019728792003956564819968
  rule pow248 => 452312848583266388373324160190187140051835877600158453279131187530910662656
  rule pow240 => 1766847064778384329583297500742918515827483896875618958121606201292619776
  rule pow232 => 6901746346790563787434755862277025452451108972170386555162524223799296
  rule pow224 => 26959946667150639794667015087019630673637144422540572481103610249216
  rule pow216 => 105312291668557186697918027683670432318895095400549111254310977536
  rule pow208 => 411376139330301510538742295639337626245683966408394965837152256
  rule pow200 => 1606938044258990275541962092341162602522202993782792835301376
  rule pow192 => 6277101735386680763835789423207666416102355444464034512896
  rule pow184 => 24519928653854221733733552434404946937899825954937634816
  rule pow176 => 95780971304118053647396689196894323976171195136475136
  rule pow168 => 374144419156711147060143317175368453031918731001856
  rule pow160 => 1461501637330902918203684832716283019655932542976
  rule pow152 => 5708990770823839524233143877797980545530986496
  rule pow144 => 22300745198530623141535718272648361505980416
  rule pow136 => 87112285931760246646623899502532662132736
  rule pow128 => 340282366920938463463374607431768211456
  rule pow120 => 1329227995784915872903807060280344576
  rule pow112 => 5192296858534827628530496329220096
  rule pow104 => 20282409603651670423947251286016
  rule pow96  => 79228162514264337593543950336
  rule pow88  => 309485009821345068724781056
  rule pow80  => 1208925819614629174706176
  rule pow72  => 4722366482869645213696
  rule pow64  => 18446744073709551616
  rule pow56  => 72057594037927936
  rule pow48  => 281474976710656
  rule pow40  => 1099511627776
  rule pow32  => 4294967296
  rule pow24  => 16777216
  rule pow16  => 65536
  rule pow8   => 256
  syntax Int  ::=
    "minSInt8" [alias]
  | "minSInt8Word" [alias]
  | "maxSInt8" [alias]
  | "minSInt16" [alias]
  | "minSInt16Word" [alias]
  | "maxSInt16" [alias]
  | "minSInt24" [alias]
  | "minSInt24Word" [alias]
  | "maxSInt24" [alias]
  | "minSInt32" [alias]
  | "minSInt32Word" [alias]
  | "maxSInt32" [alias]
  | "minSInt40" [alias]
  | "minSInt40Word" [alias]
  | "maxSInt40" [alias]
  | "minSInt48" [alias]
  | "minSInt48Word" [alias]
  | "maxSInt48" [alias]
  | "minSInt56" [alias]
  | "minSInt56Word" [alias]
  | "maxSInt56" [alias]
  | "minSInt64" [alias]
  | "minSInt64Word" [alias]
  | "maxSInt64" [alias]
  | "minSInt72" [alias]
  | "minSInt72Word" [alias]
  | "maxSInt72" [alias]
  | "minSInt80" [alias]
  | "minSInt80Word" [alias]
  | "maxSInt80" [alias]
  | "minSInt88" [alias]
  | "minSInt88Word" [alias]
  | "maxSInt88" [alias]
  | "minSInt96" [alias]
  | "minSInt96Word" [alias]
  | "maxSInt96" [alias]
  | "minSInt104" [alias]
  | "minSInt104Word" [alias]
  | "maxSInt104" [alias]
  | "minSInt112" [alias]
  | "minSInt112Word" [alias]
  | "maxSInt112" [alias]
  | "minSInt120" [alias]
  | "minSInt120Word" [alias]
  | "maxSInt120" [alias]
  | "minSInt128" [alias]
  | "minSInt128Word" [alias]
  | "maxSInt128" [alias]
  | "minSInt136" [alias]
  | "minSInt136Word" [alias]
  | "maxSInt136" [alias]
  | "minSInt144" [alias]
  | "minSInt144Word" [alias]
  | "maxSInt144" [alias]
  | "minSInt152" [alias]
  | "minSInt152Word" [alias]
  | "maxSInt152" [alias]
  | "minSInt160" [alias]
  | "minSInt160Word" [alias]
  | "maxSInt160" [alias]
  | "minSInt168" [alias]
  | "minSInt168Word" [alias]
  | "maxSInt168" [alias]
  | "minSInt176" [alias]
  | "minSInt176Word" [alias]
  | "maxSInt176" [alias]
  | "minSInt184" [alias]
  | "minSInt184Word" [alias]
  | "maxSInt184" [alias]
  | "minSInt192" [alias]
  | "minSInt192Word" [alias]
  | "maxSInt192" [alias]
  | "minSInt200" [alias]
  | "minSInt200Word" [alias]
  | "maxSInt200" [alias]
  | "minSInt208" [alias]
  | "minSInt208Word" [alias]
  | "maxSInt208" [alias]
  | "minSInt216" [alias]
  | "minSInt216Word" [alias]
  | "maxSInt216" [alias]
  | "minSInt224" [alias]
  | "minSInt224Word" [alias]
  | "maxSInt224" [alias]
  | "minSInt232" [alias]
  | "minSInt232Word" [alias]
  | "maxSInt232" [alias]
  | "minSInt240" [alias]
  | "minSInt240Word" [alias]
  | "maxSInt240" [alias]
  | "minSInt248" [alias]
  | "minSInt248Word" [alias]
  | "maxSInt248" [alias]
  | "minSInt256" [alias]
  | "minSInt256Word" [alias]
  | "maxSInt256" [alias]
  | "minUInt8" [macro]
  | "maxUInt8" [alias]
  | "minUInt16" [macro]
  | "maxUInt16" [alias]
  | "minUInt24" [macro]
  | "maxUInt24" [alias]
  | "minUInt32" [macro]
  | "maxUInt32" [alias]
  | "minUInt40" [macro]
  | "maxUInt40" [alias]
  | "minUInt48" [macro]
  | "maxUInt48" [alias]
  | "minUInt56" [macro]
  | "maxUInt56" [alias]
  | "minUInt64" [macro]
  | "maxUInt64" [alias]
  | "minUInt72" [macro]
  | "maxUInt72" [alias]
  | "minUInt80" [macro]
  | "maxUInt80" [alias]
  | "minUInt88" [macro]
  | "maxUInt88" [alias]
  | "minUInt96" [macro]
  | "maxUInt96" [alias]
  | "minUInt104" [macro]
  | "maxUInt104" [alias]
  | "minUInt112" [macro]
  | "maxUInt112" [alias]
  | "minUInt120" [macro]
  | "maxUInt120" [alias]
  | "minUInt128" [macro]
  | "maxUInt128" [alias]
  | "minUInt136" [macro]
  | "maxUInt136" [alias]
  | "minUInt144" [macro]
  | "maxUInt144" [alias]
  | "minUInt152" [macro]
  | "maxUInt152" [alias]
  | "minUInt160" [macro]
  | "maxUInt160" [alias]
  | "minUInt168" [macro]
  | "maxUInt168" [alias]
  | "minUInt176" [macro]
  | "maxUInt176" [alias]
  | "minUInt184" [macro]
  | "maxUInt184" [alias]
  | "minUInt192" [macro]
  | "maxUInt192" [alias]
  | "minUInt200" [macro]
  | "maxUInt200" [alias]
  | "minUInt208" [macro]
  | "maxUInt208" [alias]
  | "minUInt216" [macro]
  | "maxUInt216" [alias]
  | "minUInt224" [macro]
  | "maxUInt224" [alias]
  | "minUInt232" [macro]
  | "maxUInt232" [alias]
  | "minUInt240" [macro]
  | "maxUInt240" [alias]
  | "minUInt248" [macro]
  | "maxUInt248" [alias]
  | "minUInt256" [macro]
  | "maxUInt256" [alias]
  | "minSFixed128x10" [alias]
  | "maxSFixed128x10" [alias]
  | "minUFixed128x10" [macro]
  | "maxUFixed128x10" [alias]
  rule minSInt8        => -128
  rule minSInt8Word    =>  115792089237316195423570985008687907853269984665640564039457584007913129639808
  rule maxSInt8        =>  127
  rule minSInt16       => -32768
  rule minSInt16Word   =>  115792089237316195423570985008687907853269984665640564039457584007913129607168
  rule maxSInt16       =>  32767
  rule minSInt24       => -8388608
  rule minSInt24Word   =>  115792089237316195423570985008687907853269984665640564039457584007913121251328
  rule maxSInt24       =>  8388607
  rule minSInt32       => -2147483648
  rule minSInt32Word   =>  115792089237316195423570985008687907853269984665640564039457584007910982156288
  rule maxSInt32       =>  2147483647
  rule minSInt40       => -549755813888
  rule minSInt40Word   =>  115792089237316195423570985008687907853269984665640564039457584007363373826048
  rule maxSInt40       =>  549755813887
  rule minSInt48       => -140737488355328
  rule minSInt48Word   =>  115792089237316195423570985008687907853269984665640564039457583867175641284608
  rule maxSInt48       =>  140737488355327
  rule minSInt56       => -36028797018963968
  rule minSInt56Word   =>  115792089237316195423570985008687907853269984665640564039457547979116110675968
  rule maxSInt56       =>  36028797018963967
  rule minSInt64       => -9223372036854775808
  rule minSInt64Word   =>  115792089237316195423570985008687907853269984665640564039448360635876274864128
  rule maxSInt64       =>  9223372036854775807
  rule minSInt72       => -2361183241434822606848
  rule minSInt72Word   =>  115792089237316195423570985008687907853269984665640564037096400766478307033088
  rule maxSInt72       =>  2361183241434822606847
  rule minSInt80       => -604462909807314587353088
  rule minSInt80Word   =>  115792089237316195423570985008687907853269984665640563434994674200598542286848
  rule maxSInt80       =>  604462909807314587353087
  rule minSInt88       => -154742504910672534362390528
  rule minSInt88Word   =>  115792089237316195423570985008687907853269984665640409296952673335378767249408
  rule maxSInt88       =>  154742504910672534362390527
  rule minSInt96       => -39614081257132168796771975168
  rule minSInt96Word   =>  115792089237316195423570985008687907853269984665600949958200451839116357664768
  rule maxSInt96       =>  39614081257132168796771975167
  rule minSInt104      => -10141204801825835211973625643008
  rule minSInt104Word  =>  115792089237316195423570985008687907853269984655499359237631748795939503996928
  rule maxSInt104      =>  10141204801825835211973625643007
  rule minSInt112      => -2596148429267413814265248164610048
  rule minSInt112Word  =>  115792089237316195423570985008687907853269982069492134772043769742664965029888
  rule maxSInt112      =>  2596148429267413814265248164610047
  rule minSInt120      => -664613997892457936451903530140172288
  rule minSInt120Word  =>  115792089237316195423570985008687907853269320051642671581521132104382989467648
  rule maxSInt120      =>  664613997892457936451903530140172287
  rule minSInt128      => -170141183460469231731687303715884105728
  rule minSInt128Word  =>  115792089237316195423570985008687907853099843482180094807725896704197245534208
  rule maxSInt128      =>  170141183460469231731687303715884105727
  rule minSInt136      => -43556142965880123323311949751266331066368
  rule minSInt136Word  =>  115792089237316195423570985008687907809713841699760440716145634256646798573568
  rule maxSInt136      =>  43556142965880123323311949751266331066367
  rule minSInt144      => -11150372599265311570767859136324180752990208
  rule minSInt144Word  =>  115792089237316195423570985008687896702897385400328993271598447683732376649728
  rule maxSInt144      =>  11150372599265311570767859136324180752990207
  rule minSInt152      => -2854495385411919762116571938898990272765493248
  rule minSInt152Word  =>  115792089237316195423570985008685053357884572745878447467518685017640364146688
  rule maxSInt152      =>  2854495385411919762116571938898990272765493247
  rule minSInt160      => -730750818665451459101842416358141509827966271488
  rule minSInt160Word  =>  115792089237316195423570985007957157034604533206538721623099442498085163368448
  rule maxSInt160      =>  730750818665451459101842416358141509827966271487
  rule minSInt168      => -187072209578355573530071658587684226515959365500928
  rule minSInt168Word  =>  115792089237316195423570984821615698274914411135568905451773357491953764139008
  rule maxSInt168      =>  187072209578355573530071658587684226515959365500927
  rule minSInt176      => -47890485652059026823698344598447161988085597568237568
  rule minSInt176Word  =>  115792089237316195423570937118202255794243160967295965592295595922315561402368
  rule maxSInt176      =>  47890485652059026823698344598447161988085597568237567
  rule minSInt184      => -12259964326927110866866776217202473468949912977468817408
  rule minSInt184Word  =>  115792089237316195423558725044360980742403117889423361565988634094935660822528
  rule maxSInt184      =>  12259964326927110866866776217202473468949912977468817407
  rule minSInt192      => -3138550867693340381917894711603833208051177722232017256448
  rule minSInt192Word  =>  115792089237316195420432434140994567471352089954036730831406406285681112383488
  rule maxSInt192      =>  3138550867693340381917894711603833208051177722232017256447
  rule minSInt200      => -803469022129495137770981046170581301261101496891396417650688
  rule minSInt200Word  =>  115792089237316194620101962879192770082288938495059262778356087116516711989248
  rule maxSInt200      =>  803469022129495137770981046170581301261101496891396417650687
  rule minSInt208      => -205688069665150755269371147819668813122841983204197482918576128
  rule minSInt208Word  =>  115792089237315989735501319857932638482122164996827441197474379810430211063808
  rule maxSInt208      =>  205688069665150755269371147819668813122841983204197482918576127
  rule minSInt216      => -52656145834278593348959013841835216159447547700274555627155488768
  rule minSInt216Word  =>  115792089237263539277736706415338948839428149449481116491757309452285974151168
  rule maxSInt216      =>  52656145834278593348959013841835216159447547700274555627155488767
  rule minSInt224      => -13479973333575319897333507543509815336818572211270286240551805124608
  rule minSInt224Word  =>  115792089223836222089995665111354400309760169328821991828187297767361324515328
  rule maxSInt224      =>  13479973333575319897333507543509815336818572211270286240551805124607
  rule minSInt232      => -3450873173395281893717377931138512726225554486085193277581262111899648
  rule minSInt232Word  =>  115792085786443022028289091291309976714757258440086077954264306426651017740288
  rule maxSInt232      =>  3450873173395281893717377931138512726225554486085193277581262111899647
  rule minSInt240      => -883423532389192164791648750371459257913741948437809479060803100646309888
  rule minSInt240Word  =>  115791205813783806231406193359937536394012070923692126229978523204812483330048
  rule maxSInt240      =>  883423532389192164791648750371459257913741948437809479060803100646309887
  rule minSInt248      => -226156424291633194186662080095093570025917938800079226639565593765455331328
  rule minSInt248Word  =>  115565932813024562229384322928592814283244066726840484812818018414147674308608
  rule maxSInt248      =>  226156424291633194186662080095093570025917938800079226639565593765455331327
  rule minSInt256      => -57896044618658097711785492504343953926634992332820282019728792003956564819968
  rule minSInt256Word  =>  57896044618658097711785492504343953926634992332820282019728792003956564819968
  rule maxSInt256      =>  57896044618658097711785492504343953926634992332820282019728792003956564819967
  rule minSFixed128x10 => -1701411834604692317316873037158841057280000000000
  rule maxSFixed128x10 =>  1701411834604692317316873037158841057270000000000
  rule minUInt8        =>  0
  rule maxUInt8        =>  255
  rule minUInt16       =>  0
  rule maxUInt16       =>  65535
  rule minUInt24       =>  0
  rule maxUInt24       =>  16777215
  rule minUInt32       =>  0
  rule maxUInt32       =>  4294967295
  rule minUInt40       =>  0
  rule maxUInt40       =>  1099511627775
  rule minUInt48       =>  0
  rule maxUInt48       =>  281474976710655
  rule minUInt56       =>  0
  rule maxUInt56       =>  72057594037927935
  rule minUInt64       =>  0
  rule maxUInt64       =>  18446744073709551615
  rule minUInt72       =>  0
  rule maxUInt72       =>  4722366482869645213695
  rule minUInt80       =>  0
  rule maxUInt80       =>  1208925819614629174706175
  rule minUInt88       =>  0
  rule maxUInt88       =>  309485009821345068724781055
  rule minUInt96       =>  0
  rule maxUInt96       =>  79228162514264337593543950335
  rule minUInt104      =>  0
  rule maxUInt104      =>  20282409603651670423947251286015
  rule minUInt112      =>  0
  rule maxUInt112      =>  5192296858534827628530496329220095
  rule minUInt120      =>  0
  rule maxUInt120      =>  1329227995784915872903807060280344575
  rule minUInt128      =>  0
  rule maxUInt128      =>  340282366920938463463374607431768211455
  rule minUInt136      =>  0
  rule maxUInt136      =>  87112285931760246646623899502532662132735
  rule minUInt144      =>  0
  rule maxUInt144      =>  22300745198530623141535718272648361505980415
  rule minUInt152      =>  0
  rule maxUInt152      =>  5708990770823839524233143877797980545530986495
  rule minUInt160      =>  0
  rule maxUInt160      =>  1461501637330902918203684832716283019655932542975
  rule minUInt168      =>  0
  rule maxUInt168      =>  374144419156711147060143317175368453031918731001855
  rule minUInt176      =>  0
  rule maxUInt176      =>  95780971304118053647396689196894323976171195136475135
  rule minUInt184      =>  0
  rule maxUInt184      =>  24519928653854221733733552434404946937899825954937634815
  rule minUInt192      =>  0
  rule maxUInt192      =>  6277101735386680763835789423207666416102355444464034512895
  rule minUInt200      =>  0
  rule maxUInt200      =>  1606938044258990275541962092341162602522202993782792835301375
  rule minUInt208      =>  0
  rule maxUInt208      =>  411376139330301510538742295639337626245683966408394965837152255
  rule minUInt216      =>  0
  rule maxUInt216      =>  105312291668557186697918027683670432318895095400549111254310977535
  rule minUInt224      =>  0
  rule maxUInt224      =>  26959946667150639794667015087019630673637144422540572481103610249215
  rule minUInt232      =>  0
  rule maxUInt232      =>  6901746346790563787434755862277025452451108972170386555162524223799295
  rule minUInt240      =>  0
  rule maxUInt240      =>  1766847064778384329583297500742918515827483896875618958121606201292619775
  rule minUInt248      =>  0
  rule maxUInt248      =>  452312848583266388373324160190187140051835877600158453279131187530910662655
  rule minUInt256      =>  0
  rule maxUInt256      =>  115792089237316195423570985008687907853269984665640564039457584007913129639935
  rule minUFixed128x10 =>  0
  rule maxUFixed128x10 =>  3402823669209384634633746074317682114550000000000
  syntax Int  ::=
    "notMaxUInt5" [alias]
  | "notMaxUInt96" [alias]
  | "notMaxUInt128" [alias]
  | "notMaxUInt160" [alias]
  | "notMaxUInt192" [alias]
  | "notMaxUInt208" [alias]
  | "notMaxUInt224" [alias]
  rule notMaxUInt5   => 115792089237316195423570985008687907853269984665640564039457584007913129639904
  rule notMaxUInt96  => 115792089237316195423570985008687907853269984665561335876943319670319585689600
  rule notMaxUInt128 => 115792089237316195423570985008687907852929702298719625575994209400481361428480
  rule notMaxUInt160 => 115792089237316195423570985007226406215939081747436879206741300988257197096960
  rule notMaxUInt192 => 115792089237316195417293883273301227089434195242432897623355228563449095127040
  rule notMaxUInt208 => 115792089237315784047431654707177369110974345328014318355491175612947292487680
  rule notMaxUInt224 => 115792089210356248756420345214020892766250353992003419616917011526809519390720
  syntax Int  ::=
    "eth" [macro]
  | "maxBlockNum" [macro]
  rule eth         => 1000000000000000000
  rule maxBlockNum => 57896044618658097711785492504343953926634992332820282019728792003956564819967
  syntax Bool  ::=
    "#rangeBool" "(" Int ")" [alias, klabel(#rangeBool)]
  | "#rangeSInt" "(" Int "," Int ")" [alias, klabel(#rangeSInt)]
  | "#rangeUInt" "(" Int "," Int ")" [alias, klabel(#rangeUInt)]
  | "#rangeSFixed" "(" Int "," Int "," Int ")" [alias, klabel(#rangeSFixed)]
  | "#rangeUFixed" "(" Int "," Int "," Int ")" [alias, klabel(#rangeUFixed)]
  | "#rangeAddress" "(" Int ")" [alias, klabel(#rangeAddress)]
  | "#rangeBytes" "(" Int "," Int ")" [alias, klabel(#rangeBytes)]
  | "#rangeNonce" "(" Int ")" [alias, klabel(#rangeNonce)]
  | "#rangeSmall" "(" Int ")" [alias, klabel(#rangeSmall)]
  | "#rangeBlockNum" "(" Int ")" [alias, klabel(#rangeBlockNum)]
  rule #rangeBool    (            X ) => X ==Int 0 orBool X ==Int 1
  rule #rangeSInt    (   8 ,      X ) => #range ( minSInt8        <= X <  maxSInt8        )
  rule #rangeSInt    (  16 ,      X ) => #range ( minSInt16       <= X <  maxSInt16       )
  rule #rangeSInt    (  24 ,      X ) => #range ( minSInt24       <= X <  maxSInt24       )
  rule #rangeSInt    (  32 ,      X ) => #range ( minSInt32       <= X <  maxSInt32       )
  rule #rangeSInt    (  40 ,      X ) => #range ( minSInt40       <= X <  maxSInt40       )
  rule #rangeSInt    (  48 ,      X ) => #range ( minSInt48       <= X <  maxSInt48       )
  rule #rangeSInt    (  56 ,      X ) => #range ( minSInt56       <= X <  maxSInt56       )
  rule #rangeSInt    (  64 ,      X ) => #range ( minSInt64       <= X <  maxSInt64       )
  rule #rangeSInt    (  72 ,      X ) => #range ( minSInt72       <= X <  maxSInt72       )
  rule #rangeSInt    (  80 ,      X ) => #range ( minSInt80       <= X <  maxSInt80       )
  rule #rangeSInt    (  88 ,      X ) => #range ( minSInt88       <= X <  maxSInt88       )
  rule #rangeSInt    (  96 ,      X ) => #range ( minSInt96       <= X <  maxSInt96       )
  rule #rangeSInt    ( 104 ,      X ) => #range ( minSInt104      <= X <  maxSInt104      )
  rule #rangeSInt    ( 112 ,      X ) => #range ( minSInt112      <= X <  maxSInt112      )
  rule #rangeSInt    ( 120 ,      X ) => #range ( minSInt120      <= X <  maxSInt120      )
  rule #rangeSInt    ( 128 ,      X ) => #range ( minSInt128      <= X <  maxSInt128      )
  rule #rangeSInt    ( 136 ,      X ) => #range ( minSInt136      <= X <  maxSInt136      )
  rule #rangeSInt    ( 144 ,      X ) => #range ( minSInt144      <= X <  maxSInt144      )
  rule #rangeSInt    ( 152 ,      X ) => #range ( minSInt152      <= X <  maxSInt152      )
  rule #rangeSInt    ( 160 ,      X ) => #range ( minSInt160      <= X <  maxSInt160      )
  rule #rangeSInt    ( 168 ,      X ) => #range ( minSInt168      <= X <  maxSInt168      )
  rule #rangeSInt    ( 176 ,      X ) => #range ( minSInt176      <= X <  maxSInt176      )
  rule #rangeSInt    ( 184 ,      X ) => #range ( minSInt184      <= X <  maxSInt184      )
  rule #rangeSInt    ( 192 ,      X ) => #range ( minSInt192      <= X <  maxSInt192      )
  rule #rangeSInt    ( 200 ,      X ) => #range ( minSInt200      <= X <  maxSInt200      )
  rule #rangeSInt    ( 208 ,      X ) => #range ( minSInt208      <= X <  maxSInt208      )
  rule #rangeSInt    ( 216 ,      X ) => #range ( minSInt216      <= X <  maxSInt216      )
  rule #rangeSInt    ( 224 ,      X ) => #range ( minSInt224      <= X <  maxSInt224      )
  rule #rangeSInt    ( 232 ,      X ) => #range ( minSInt232      <= X <  maxSInt232      )
  rule #rangeSInt    ( 240 ,      X ) => #range ( minSInt240      <= X <  maxSInt240      )
  rule #rangeSInt    ( 248 ,      X ) => #range ( minSInt248      <= X <  maxSInt248      )
  rule #rangeSInt    ( 256 ,      X ) => #range ( minSInt256      <= X <= maxSInt256      )
  rule #rangeUInt    (   8 ,      X ) => #range ( minUInt8        <= X <  pow8            )
  rule #rangeUInt    (  16 ,      X ) => #range ( minUInt16       <= X <  pow16           )
  rule #rangeUInt    (  24 ,      X ) => #range ( minUInt24       <= X <  pow24           )
  rule #rangeUInt    (  32 ,      X ) => #range ( minUInt32       <= X <  pow32           )
  rule #rangeUInt    (  40 ,      X ) => #range ( minUInt40       <= X <  pow40           )
  rule #rangeUInt    (  48 ,      X ) => #range ( minUInt48       <= X <  pow48           )
  rule #rangeUInt    (  56 ,      X ) => #range ( minUInt56       <= X <  pow56           )
  rule #rangeUInt    (  64 ,      X ) => #range ( minUInt64       <= X <  pow64           )
  rule #rangeUInt    (  72 ,      X ) => #range ( minUInt72       <= X <  pow72           )
  rule #rangeUInt    (  80 ,      X ) => #range ( minUInt80       <= X <  pow80           )
  rule #rangeUInt    (  88 ,      X ) => #range ( minUInt88       <= X <  pow88           )
  rule #rangeUInt    (  96 ,      X ) => #range ( minUInt96       <= X <  pow96           )
  rule #rangeUInt    ( 104 ,      X ) => #range ( minUInt104      <= X <  pow104          )
  rule #rangeUInt    ( 112 ,      X ) => #range ( minUInt112      <= X <  pow112          )
  rule #rangeUInt    ( 120 ,      X ) => #range ( minUInt120      <= X <  pow120          )
  rule #rangeUInt    ( 128 ,      X ) => #range ( minUInt128      <= X <  pow128          )
  rule #rangeUInt    ( 136 ,      X ) => #range ( minUInt136      <= X <  pow136          )
  rule #rangeUInt    ( 144 ,      X ) => #range ( minUInt144      <= X <  pow144          )
  rule #rangeUInt    ( 152 ,      X ) => #range ( minUInt152      <= X <  pow152          )
  rule #rangeUInt    ( 160 ,      X ) => #range ( minUInt160      <= X <  pow160          )
  rule #rangeUInt    ( 168 ,      X ) => #range ( minUInt168      <= X <  pow168          )
  rule #rangeUInt    ( 176 ,      X ) => #range ( minUInt176      <= X <  pow176          )
  rule #rangeUInt    ( 184 ,      X ) => #range ( minUInt184      <= X <  pow184          )
  rule #rangeUInt    ( 192 ,      X ) => #range ( minUInt192      <= X <  pow192          )
  rule #rangeUInt    ( 200 ,      X ) => #range ( minUInt200      <= X <  pow200          )
  rule #rangeUInt    ( 208 ,      X ) => #range ( minUInt208      <= X <  pow208          )
  rule #rangeUInt    ( 216 ,      X ) => #range ( minUInt216      <= X <  pow216          )
  rule #rangeUInt    ( 224 ,      X ) => #range ( minUInt224      <= X <  pow224          )
  rule #rangeUInt    ( 232 ,      X ) => #range ( minUInt232      <= X <  pow232          )
  rule #rangeUInt    ( 240 ,      X ) => #range ( minUInt240      <= X <  pow240          )
  rule #rangeUInt    ( 248 ,      X ) => #range ( minUInt248      <= X <  pow248          )
  rule #rangeUInt    ( 256 ,      X ) => #range ( minUInt256      <= X <  pow256          )
  rule #rangeSFixed   ( 128 , 10 , X ) => #range ( minSFixed128x10 <= X <= maxSFixed128x10 )
  rule #rangeUFixed   ( 128 , 10 , X ) => #range ( minUFixed128x10 <= X <= maxUFixed128x10 )
  rule #rangeAddress  (            X ) => #range ( minUInt160      <= X <  pow160          )
  rule #rangeBytes    (   N ,      X ) => #range ( 0               <= X <  1 <<Byte N      )
  rule #rangeNonce    (   X          ) => #range ( 0               <= X < maxUInt64        )
  rule #rangeSmall    (   X          ) => #range ( 0               <= X < 10               )
  rule #rangeBlockNum (   X          ) => #range ( 0               <= X <= maxBlockNum     )
  syntax Bool  ::=
    "#range" "(" Int "<" Int "<" Int ")" [macro]
  | "#range" "(" Int "<" Int "<=" Int ")" [macro]
  | "#range" "(" Int "<=" Int "<" Int ")" [macro]
  | "#range" "(" Int "<=" Int "<=" Int ")" [macro]
  rule #range ( LB <  X <  UB ) => LB  <Int X andBool X  <Int UB
  rule #range ( LB <  X <= UB ) => LB  <Int X andBool X <=Int UB
  rule #range ( LB <= X <  UB ) => LB <=Int X andBool X  <Int UB
  rule #range ( LB <= X <= UB ) => LB <=Int X andBool X <=Int UB
  syntax Int  ::=
    "chop" "(" Int ")" [function, klabel(chop), smtlib(chop), total]
  rule chop ( I:Int ) => I modInt pow256  [concrete, smt-lemma]
  syntax Int  ::=
    Int "<<Byte" Int [function]
  | Int ">>Byte" Int [function]
  rule N <<Byte M => N <<Int (8 *Int M)
  rule N >>Byte M => N >>Int (8 *Int M)
endmodule

module EVM-TYPES
  imports public STRING
  imports public COLLECTIONS
  imports public K-EQUAL
  imports public JSON
  imports public WORD
  syntax Int  ::=
    "bool2Word" "(" Bool ")" [function, klabel(bool2Word), smtlib(bool2Word), total]
  rule bool2Word( true  ) => 1
  rule bool2Word( false ) => 0
  syntax Bool  ::=
    "word2Bool" "(" Int ")" [function, klabel(word2Bool), total]
  rule word2Bool( W ) => false requires W  ==Int 0
  rule word2Bool( W ) => true  requires W =/=Int 0
  syntax Int  ::=
    "sgn" "(" Int ")" [function, klabel(sgn), total]
  | "abs" "(" Int ")" [function, klabel(abs), total]
  rule sgn(I) => -1 requires pow255 <=Int I andBool I <Int pow256
  rule sgn(I) =>  1 requires 0 <=Int I andBool I <Int pow255
  rule sgn(I) =>  0 requires I <Int 0 orBool pow256 <=Int I
  rule abs(I) => 0 -Word I requires sgn(I) ==Int -1
  rule abs(I) => I         requires sgn(I) ==Int  1
  rule abs(I) => 0         requires sgn(I) ==Int  0
  syntax Int  ::=
    Int "up/Int" Int [function, smtlib(upDivInt), total]
  rule _I1 up/Int 0  => 0                                                   [concrete]
  rule _I1 up/Int I2 => 0                             requires I2 <=Int 0   [concrete]
  rule I1 up/Int 1  => I1                                                  [concrete]
  rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires 1  <Int  I2  [concrete]
  syntax Int  ::=
    "log256Int" "(" Int ")" [function, klabel(log256Int)]
  rule log256Int(N) => log2Int(N) /Int 8
  syntax Int  ::=
    Int "+Word" Int [function, total]
  | Int "*Word" Int [function, total]
  | Int "-Word" Int [function, total]
  | Int "/Word" Int [function, total]
  | Int "%Word" Int [function, total]
  rule W0 +Word W1 => chop( W0 +Int W1 )
  rule W0 -Word W1 => chop( W0 -Int W1 )
  rule W0 *Word W1 => chop( W0 *Int W1 )
  rule _ /Word W1 => 0            requires W1  ==Int 0
  rule W0 /Word W1 => W0 /Int W1   requires W1 =/=Int 0
  rule _ %Word W1 => 0            requires W1  ==Int 0
  rule W0 %Word W1 => W0 modInt W1 requires W1 =/=Int 0
  syntax Int  ::=
    Int "^Word" Int [function]
  syntax Int  ::=
    "powmod" "(" Int "," Int "," Int ")" [function, klabel(powmod), total]
  rule W0 ^Word W1 => powmod(W0, W1, pow256)
  rule [powmod.nonzero]: powmod(W0, W1, W2) => W0 ^%Int W1 W2  requires W2 =/=Int 0  [concrete]
  rule [powmod.zero]: powmod( _,  _, W2) => 0               requires W2  ==Int 0  [concrete]
  syntax Int  ::=
    Int "/sWord" Int [function]
  | Int "%sWord" Int [function]
  rule [divSWord.same]: W0 /sWord W1 =>          abs(W0) /Word abs(W1)  requires sgn(W0) *Int sgn(W1) ==Int  1
  rule [divSWord.diff]: W0 /sWord W1 => 0 -Word (abs(W0) /Word abs(W1)) requires sgn(W0) *Int sgn(W1) ==Int -1
  rule [modSWord.pos]: W0 %sWord W1 =>          abs(W0) %Word abs(W1)  requires sgn(W0) ==Int  1
  rule [modSWord.neg]: W0 %sWord W1 => 0 -Word (abs(W0) %Word abs(W1)) requires sgn(W0) ==Int -1
  syntax Int  ::=
    Int "<Word" Int [function, total]
  | Int ">Word" Int [function, total]
  | Int "<=Word" Int [function, total]
  | Int ">=Word" Int [function, total]
  | Int "==Word" Int [function, total]
  rule W0 <Word  W1 => bool2Word(W0 <Int  W1)
  rule W0 >Word  W1 => bool2Word(W0 >Int  W1)
  rule W0 <=Word W1 => bool2Word(W0 <=Int W1)
  rule W0 >=Word W1 => bool2Word(W0 >=Int W1)
  rule W0 ==Word W1 => bool2Word(W0 ==Int W1)
  syntax Int  ::=
    Int "s<Word" Int [function, total]
  rule [s<Word.pp]: W0 s<Word W1 => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
  rule [s<Word.pn]: W0 s<Word W1 => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
  rule [s<Word.np]: W0 s<Word W1 => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
  rule [s<Word.nn]: W0 s<Word W1 => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1
  syntax Int  ::=
    "~Word" Int [function, total]
  | Int "|Word" Int [function, total]
  | Int "&Word" Int [function, total]
  | Int "xorWord" Int [function, total]
  | Int "<<Word" Int [function, total]
  | Int ">>Word" Int [function, total]
  | Int ">>sWord" Int [function, total]
  rule ~Word W       => W xorInt maxUInt256
  rule W0 |Word   W1 => W0 |Int W1
  rule W0 &Word   W1 => W0 &Int W1
  rule W0 xorWord W1 => W0 xorInt W1
  rule W0 <<Word  W1 => chop( W0 <<Int W1 ) requires 0 <=Int W0 andBool 0 <=Int W1 andBool W1 <Int 256
  rule _ <<Word  _  => 0  [owise]
  rule W0 >>Word  W1 => W0 >>Int W1 requires 0 <=Int W0 andBool 0 <=Int W1
  rule _ >>Word   _ => 0  [owise]
  rule W0 >>sWord W1 => chop( (abs(W0) *Int sgn(W0)) >>Int W1 ) requires 0 <=Int W0 andBool 0 <=Int W1
  rule _ >>sWord  _ => 0  [owise]
  syntax Int  ::=
    "bit" "(" Int "," Int ")" [function, klabel(bit)]
  | "byte" "(" Int "," Int ")" [function, klabel(byte)]
  rule bit (N, _) => 0 requires notBool (N >=Int 0 andBool N <Int 256)
  rule byte(N, _) => 0 requires notBool (N >=Int 0 andBool N <Int  32)
  rule bit (N, W) => bitRangeInt(W , (255 -Int N)        , 1) requires N >=Int 0 andBool N <Int 256
  rule byte(N, W) => bitRangeInt(W , ( 31 -Int N) *Int 8 , 8) requires N >=Int 0 andBool N <Int  32
  syntax Int  ::=
    "#nBits" "(" Int ")" [function, klabel(#nBits)]
  | "#nBytes" "(" Int ")" [function, klabel(#nBytes)]
  rule #nBits(N)  => (1 <<Int N) -Int 1 requires N >=Int 0
  rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
  syntax Int  ::=
    "signextend" "(" Int "," Int ")" [function, klabel(signextend), total]
  rule [signextend.invalid]: signextend(N, W) => W requires N >=Int 32 orBool N <Int 0                                                                                                                       [concrete]
  rule [signextend.negative]: signextend(N, W) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))  [concrete]
  rule [signextend.positive]: signextend(N, W) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))  [concrete]
  syntax WordStack  ::=
    ".WordStack" [smtlib(_dotWS)]
  | Int ":" WordStack [klabel(_:_WS), smtlib(_WS_)]
  syntax Bytes  ::=
    Int ":" Bytes [function]
  rule I : BS => Int2Bytes(1, I, BE) +Bytes BS requires I <Int 256
  syntax WordStack  ::=
    "#take" "(" Int "," WordStack ")" [function, klabel(takeWordStack), total]
  rule [#take.base]: #take(N, _WS)                => .WordStack                      requires notBool N >Int 0
  rule [#take.zero-pad]: #take(N, .WordStack)         => 0 : #take(N -Int 1, .WordStack) requires N >Int 0
  rule [#take.recursive]: #take(N, (W : WS):WordStack) => W : #take(N -Int 1, WS)         requires N >Int 0
  syntax WordStack  ::=
    "#drop" "(" Int "," WordStack ")" [function, klabel(dropWordStack), total]
  rule #drop(N, WS:WordStack)       => WS                                  requires notBool N >Int 0
  rule #drop(N, .WordStack)         => .WordStack                          requires         N >Int 0
  rule #drop(N, (W : WS):WordStack) => #drop(1, #drop(N -Int 1, (W : WS))) requires         N >Int 1
  rule #drop(1, (_ : WS):WordStack) => WS
  syntax Int  ::=
    WordStack "[" Int "]" [function, total]
  rule (W : _):WordStack [ N ] => W                  requires N ==Int 0
  rule WS:WordStack      [ N ] => #drop(N, WS) [ 0 ] requires N  >Int 0
  rule _:WordStack      [ N ] => 0                  requires N  <Int 0
  syntax WordStack  ::=
    WordStack "[" Int ":=" Int "]" [function, total]
  rule (_W0 : WS):WordStack [ N := W ] => W  : WS                     requires N ==Int 0
  rule ( W0 : WS):WordStack [ N := W ] => W0 : (WS [ N -Int 1 := W ]) requires N  >Int 0
  rule WS :WordStack [ N := _ ] => WS                          requires N  <Int 0
  rule .WordStack           [ N := W ] => (0 : .WordStack) [ N := W ]
  syntax Int  ::=
    "#sizeWordStack" "(" WordStack ")" [function, klabel(#sizeWordStack), smtlib(sizeWordStack), total]
  | "#sizeWordStack" "(" WordStack "," Int ")" [function, klabel(sizeWordStackAux), smtlib(sizeWordStackAux), total]
  rule #sizeWordStack ( WS ) => #sizeWordStack(WS, 0)
  rule #sizeWordStack ( .WordStack, SIZE ) => SIZE
  rule #sizeWordStack ( _ : WS, SIZE )     => #sizeWordStack(WS, SIZE +Int 1)
  syntax Bool  ::=
    Int "in" WordStack [function]
  rule _ in .WordStack => false
  rule W in (W' : WS)  => (W ==K W') orElseBool (W in WS)
  syntax WordStack  ::=
    "#replicate" "(" Int "," Int ")" [function, klabel(#replicate), total]
  | "#replicateAux" "(" Int "," Int "," WordStack ")" [function, klabel(#replicateAux), total]
  rule #replicate   ( N,  A )     => #replicateAux(N, A, .WordStack)
  rule #replicateAux( N,  A, WS ) => #replicateAux(N -Int 1, A, A : WS) requires         N >Int 0
  rule #replicateAux( N, _A, WS ) => WS                                 requires notBool N >Int 0
  syntax List  ::=
    "WordStack2List" "(" WordStack ")" [function, klabel(WordStack2List), total]
  rule WordStack2List(.WordStack) => .List
  rule WordStack2List(W : WS) => ListItem(W) WordStack2List(WS)
  syntax Bytes  ::=
    "#write" "(" Bytes "," Int "," Int ")" [function]
  | Bytes "[" Int ":=" Bytes "]" [function, klabel(mapWriteRange), total]
  rule #write(WM, IDX, VAL) => padRightBytes(WM, IDX +Int 1, 0) [ IDX <- VAL ]
  rule WS [ START := WS' ] => WS                                                                            requires 0     <=Int START andBool lengthBytes(WS')  ==Int 0  [concrete]
  rule WS [ START := WS' ] => replaceAtBytes(padRightBytes(WS, START +Int lengthBytes(WS'), 0), START, WS') requires 0     <=Int START andBool lengthBytes(WS') =/=Int 0  [concrete]
  rule _  [ START := _ ]   => .Bytes                                                                        requires START  <Int 0                                        [concrete]
  syntax Int  ::=
    "#asWord" "(" Bytes ")" [function, klabel(#asWord), smtlib(asWord), total]
  rule #asWord(WS) => chop(Bytes2Int(WS, BE, Unsigned))  [concrete]
  syntax Int  ::=
    "#asInteger" "(" Bytes ")" [function, klabel(#asInteger), total]
  rule #asInteger(WS) => Bytes2Int(WS, BE, Unsigned)  [concrete]
  syntax Account  ::=
    "#asAccount" "(" Bytes ")" [function, klabel(#asAccount)]
  rule #asAccount(BS) => .Account    requires lengthBytes(BS) ==Int 0
  rule #asAccount(BS) => #asWord(BS)  [owise]
  syntax Bytes  ::=
    "#asByteStack" "(" Int ")" [function, klabel(#asByteStack), total]
  rule #asByteStack(W) => Int2Bytes(W, BE, Unsigned)  [concrete]
  syntax Bytes  ::=
    "#range" "(" Bytes "," Int "," Int ")" [function, klabel(#range), total]
  rule #range(_, START, WIDTH)  => .Bytes                                                                       requires notBool (WIDTH >=Int 0 andBool START >=Int 0)  [concrete]
  rule [bytesRange]: #range(WS, START, WIDTH) => substrBytes(padRightBytes(WS, START +Int WIDTH, 0), START, START +Int WIDTH) requires WIDTH >=Int 0 andBool START >=Int 0 andBool START <Int lengthBytes(WS)  [concrete]
  rule #range(_, _, WIDTH)      => padRightBytes(.Bytes, WIDTH, 0)  [concrete, owise]
  syntax Bytes  ::=
    "#padToWidth" "(" Int "," Bytes ")" [function, klabel(#padToWidth), total]
  | "#padRightToWidth" "(" Int "," Bytes ")" [function, klabel(#padRightToWidth), total]
  rule #padToWidth(N, BS)      =>               BS        requires notBool (0 <=Int N)  [concrete]
  rule #padToWidth(N, BS)      =>  padLeftBytes(BS, N, 0) requires          0 <=Int N   [concrete]
  rule #padRightToWidth(N, BS) =>               BS        requires notBool (0 <=Int N)  [concrete]
  rule #padRightToWidth(N, BS) => padRightBytes(BS, N, 0) requires          0 <=Int N   [concrete]
  syntax Account  ::=
    ".Account"
  | Int
  syntax AccountCode  ::=
    Bytes
  syntax Int  ::=
    "#addr" "(" Int ")" [function, klabel(#addr), total]
  rule #addr(W) => W %Word pow160
  syntax Int  ::=
    "#lookup" "(" Map "," Int ")" [function, klabel(#lookup), smtlib(lookup), total]
  | "#lookupMemory" "(" Map "," Int ")" [function, klabel(#lookupMemory), smtlib(lookupMemory), total]
  rule [#lookup.some]: #lookup(       (KEY |-> VAL:Int) _M, KEY ) => VAL modInt pow256
  rule [#lookup.none]: #lookup(                          M, KEY ) => 0                 requires notBool KEY in_keys(M)
  rule [#lookup.notInt]: #lookup(       (KEY |-> VAL    ) _M, KEY ) => 0                 requires notBool isInt(VAL)
  rule [#lookupMemory.some]: #lookupMemory( (KEY |-> VAL:Int) _M, KEY ) => VAL modInt 256
  rule [#lookupMemory.none]: #lookupMemory(                    M, KEY ) => 0                 requires notBool KEY in_keys(M)
  rule [#lookupMemory.notInt]: #lookupMemory( (KEY |-> VAL    ) _M, KEY ) => 0                 requires notBool isInt(VAL)
  syntax SubstateLogEntry  ::=
    "{" Int "|" List "|" Bytes "}" [klabel(logEntry)]
  syntax TxType  ::=
    ".TxType"
  | "Legacy"
  | "AccessList"
  | "DynamicFee"
  syntax Int  ::=
    "#dasmTxPrefix" "(" TxType ")" [function, klabel(#dasmTxPrefix)]
  rule #dasmTxPrefix (Legacy)     => 0
  rule #dasmTxPrefix (AccessList) => 1
  rule #dasmTxPrefix (DynamicFee) => 2
  syntax TxType  ::=
    "#asmTxPrefix" "(" Int ")" [function, klabel(#asmTxPrefix)]
  rule #asmTxPrefix (0) => Legacy
  rule #asmTxPrefix (1) => AccessList
  rule #asmTxPrefix (2) => DynamicFee
  syntax TxData  ::=
    LegacyTx
  | AccessListTx
  | DynamicFeeTx
  syntax LegacyTx  ::=
    "LegacyTxData" "(" nonce: Int "," gasPrice: Int "," gasLimit: Int "," to: Account "," value: Int "," data: Bytes ")" [klabel(LegacyTxData)]
  | "LegacyProtectedTxData" "(" nonce: Int "," gasPrice: Int "," gasLimit: Int "," to: Account "," value: Int "," data: Bytes "," chainId: Int ")" [klabel(LegacyProtectedTxData)]
  syntax AccessListTx  ::=
    "AccessListTxData" "(" nonce: Int "," gasPrice: Int "," gasLimit: Int "," to: Account "," value: Int "," data: Bytes "," chainId: Int "," accessLists: JSONs ")" [klabel(AccessListTxData)]
  syntax DynamicFeeTx  ::=
    "DynamicFeeTxData" "(" nonce: Int "," priorityGasFee: Int "," maxGasFee: Int "," gasLimit: Int "," to: Account "," value: Int "," data: Bytes "," chainId: Int "," accessLists: JSONs ")" [klabel(DynamicFeeTxData)]
endmodule

module JSON-SYNTAX
  imports public INT-SYNTAX
  imports public STRING-SYNTAX
  imports public BOOL-SYNTAX
  imports public FLOAT-SYNTAX
  syntax JSONs  ::=
    List{JSON,","} [klabel(JSONs), symbol]
  syntax JSONKey  ::=
    String
  syntax JSON  ::=
    "null" [klabel(JSONnull), symbol]
  | String
  | Int
  | Float
  | Bool
  | JSONKey ":" JSON [klabel(JSONEntry), symbol]
  | "{" JSONs "}" [klabel(JSONObject), symbol]
  | "[" JSONs "]" [klabel(JSONList), symbol]
endmodule

module JSON
  imports public JSON-SYNTAX
  syntax String  ::=
    "JSON2String" "(" JSON ")" [function, hook(JSON.json2string), klabel(JSON2String)]
  syntax JSON  ::=
    "String2JSON" "(" String ")" [function, hook(JSON.string2json), klabel(String2JSON)]
endmodule

module JSON-EXT
  imports public JSON
  imports public STRING
  imports public BOOL
  syntax JSONs  ::=
    JSONs "+JSONs" JSONs [function]
  rule .JSONs   +JSONs JS' => JS'
  rule (J , JS) +JSONs JS' => J , (JS +JSONs JS')
  syntax JSONs  ::=
    "reverseJSONs" "(" JSONs ")" [function, klabel(reverseJSONs)]
  | "reverseJSONsAux" "(" JSONs "," JSONs ")" [function, klabel(reverseJSONsAux)]
  rule reverseJSONs(JS) => reverseJSONsAux(JS, .JSONs)
  rule reverseJSONsAux(.JSONs, JS') => JS'
  rule reverseJSONsAux((J, JS:JSONs), JS') => reverseJSONsAux(JS, (J, JS'))
  syntax JSONs  ::=
    "qsortJSONs" "(" JSONs ")" [function, klabel(qsortJSONs)]
  | "#entriesLT" "(" String "," JSONs ")" [function, klabel(#entriesLT)]
  | "#entriesGE" "(" String "," JSONs ")" [function, klabel(#entriesGE)]
  rule qsortJSONs(.JSONs)            => .JSONs
  rule qsortJSONs(KEY : VALUE, REST) => qsortJSONs(#entriesLT(KEY, REST)) +JSONs (KEY : VALUE , qsortJSONs(#entriesGE(KEY, REST)))
  rule #entriesLT(_KEY, .JSONs)              => .JSONs
  rule #entriesLT( KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesLT(KEY, REST) requires         KEY' <String KEY
  rule #entriesLT( KEY, (KEY':     _, REST)) =>               #entriesLT(KEY, REST) requires notBool KEY' <String KEY
  rule #entriesGE(_KEY, .JSONs)              => .JSONs
  rule #entriesGE( KEY, (KEY': VALUE, REST)) => KEY': VALUE , #entriesGE(KEY, REST) requires         KEY' >=String KEY
  rule #entriesGE( KEY, (KEY':     _, REST)) =>               #entriesGE(KEY, REST) requires notBool KEY' >=String KEY
  syntax Bool  ::=
    "sortedJSONs" "(" JSONs ")" [function, klabel(sortedJSONs)]
  rule sortedJSONs( .JSONs   ) => true
  rule sortedJSONs( _KEY : _ ) => true
  rule sortedJSONs( (KEY : _) , (KEY' : VAL) , REST ) => KEY <=String KEY' andThenBool sortedJSONs((KEY' : VAL) , REST)
  syntax JSONKey  ::=
    Int
endmodule

module JSON-RPC
  imports public K-IO
  imports public LIST
  imports public JSON-EXT
  configuration <json-rpc>
        <web3input> $INPUT:Int </web3input>
        <web3output> $OUTPUT:Int </web3output>
        <web3request>
          <jsonrpc> "":JSON </jsonrpc>
          <callid> 0:JSON </callid>
          <method> "":JSON </method>
          <params> [ .JSONs ] </params>
          <batch> undef </batch>
        </web3request>
        <web3response> .List </web3response>
      </json-rpc>
  syntax JSON  ::=
    "undef" [klabel(JSON-RPCundef), symbol]
  syntax Bool  ::=
    "isProperJson" "(" JSON ")" [function, klabel(isProperJson)]
  | "isProperJsonList" "(" JSONs ")" [function, klabel(isProperJsonList)]
  rule isProperJson(_) => false  [owise]
  rule isProperJson(null) => true
  rule isProperJson(_:Int)    => true
  rule isProperJson(_:Bool)   => true
  rule isProperJson(_:String) => true
  rule isProperJson(_:JSONKey : J) => isProperJson(J)
  rule isProperJson([ JS ]) => isProperJsonList(JS)
  rule isProperJson({ JS }) => isProperJsonList(JS)
  rule isProperJsonList(.JSONs) => true
  rule isProperJsonList(J, JS)  => isProperJson(J) andBool isProperJsonList(JS)
  syntax JSONs  ::=
    "flattenJSONs" "(" JSONs ")" [function, klabel(flattenJSONs)]
  rule flattenJSONs(.JSONs      ) => .JSONs
  rule flattenJSONs([.JSONs], JL) => flattenJSONs(JL)
  rule flattenJSONs([J,JS]  , JL) => J, flattenJSONs([JS], JL)
endmodule

module KRYPTO
  imports public STRING-SYNTAX
  imports public INT-SYNTAX
  imports public LIST
  syntax String  ::=
    "Keccak256" "(" String ")" [function, hook(KRYPTO.keccak256), klabel(Keccak256)]
  | "Sha256" "(" String ")" [function, hook(KRYPTO.sha256), klabel(Sha256)]
  | "Sha512" "(" String ")" [function, hook(KRYPTO.sha512), klabel(Sha512)]
  | "Sha512_256" "(" String ")" [function, hook(KRYPTO.sha512_256)]
  | "Sha3_256" "(" String ")" [function, hook(KRYPTO.sha3)]
  | "RipEmd160" "(" String ")" [function, hook(KRYPTO.ripemd160), klabel(RipEmd160)]
  | "Blake2Compress" "(" String ")" [function, hook(KRYPTO.blake2compress), klabel(Blake2Compress)]
  syntax String  ::=
    "Keccak256raw" "(" String ")" [function, hook(KRYPTO.keccak256raw), klabel(Keccak256raw)]
  | "Sha256raw" "(" String ")" [function, hook(KRYPTO.sha256raw), klabel(Sha256raw)]
  | "Sha512raw" "(" String ")" [function, hook(KRYPTO.sha512raw), klabel(Sha512raw)]
  | "Sha512_256raw" "(" String ")" [function, hook(KRYPTO.sha512_256raw)]
  | "Sha3_256raw" "(" String ")" [function, hook(KRYPTO.sha3raw)]
  | "RipEmd160raw" "(" String ")" [function, hook(KRYPTO.ripemd160raw), klabel(RipEmd160raw)]
  syntax String  ::=
    "ECDSARecover" "(" String "," Int "," String "," String ")" [function, hook(KRYPTO.ecdsaRecover), klabel(ECDSARecover)]
  | "ECDSASign" "(" String "," String ")" [function, hook(KRYPTO.ecdsaSign), klabel(ECDSASign)]
  | "ECDSAPubKey" "(" String ")" [function, hook(KRYPTO.ecdsaPubKey), klabel(ECDSAPubKey)]
  syntax G1Point  ::=
    "(" Int "," Int ")" [prefer]
  syntax G2Point  ::=
    "(" Int "x" Int "," Int "x" Int ")"
  syntax G1Point  ::=
    "BN128Add" "(" G1Point "," G1Point ")" [function, hook(KRYPTO.bn128add), klabel(BN128Add)]
  | "BN128Mul" "(" G1Point "," Int ")" [function, hook(KRYPTO.bn128mul), klabel(BN128Mul)]
  syntax Bool  ::=
    "BN128AtePairing" "(" List "," List ")" [function, hook(KRYPTO.bn128ate), klabel(BN128AtePairing)]
  syntax Bool  ::=
    "isValidPoint" "(" G1Point ")" [function, hook(KRYPTO.bn128valid), klabel(isValidPoint)]
  | "isValidPoint" "(" G2Point ")" [function, hook(KRYPTO.bn128g2valid), klabel(isValidG2Point)]
endmodule

module SERIALIZATION
  imports public KRYPTO
  imports public EVM-TYPES
  imports public STRING-BUFFER
  imports public JSON-EXT
  syntax Int  ::=
    "keccak" "(" Bytes ")" [function, klabel(keccak), smtlib(smt_keccak), total]
  rule [keccak]: keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))  [concrete]
  syntax Int  ::=
    "#newAddr" "(" Int "," Int ")" [function, klabel(#newAddr)]
  | "#newAddr" "(" Int "," Int "," Bytes ")" [function, klabel(#newAddrCreate2)]
  rule [#newAddr]: #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncode([#addrBytes(ACCT), NONCE]))))                                                                                                                                                      [concrete]
  rule [#newAddrCreate2]: #newAddr(ACCT, SALT, INITCODE) => #addr(#parseHexWord(Keccak256("\xff" +String #unparseByteStack(#addrBytes(ACCT)) +String #unparseByteStack(#wordBytes(SALT)) +String #unparseByteStack(#parseHexBytes(Keccak256(#unparseByteStack(INITCODE)))))))  [concrete]
  syntax Account  ::=
    "#sender" "(" TxData "," Int "," Bytes "," Bytes ")" [function, klabel(#senderTxData)]
  | "#sender" "(" String "," Int "," String "," String ")" [function, klabel(#senderAux)]
  | "#sender" "(" String ")" [function, klabel(#senderAux2)]
  rule #sender(_:TxData, TW => TW +Int 27, _, _)
      requires TW ==Int 0 orBool TW ==Int 1
  rule #sender(TXDATA, TW, TR, TS)
      => #sender(Hex2Raw(#hashTxData(TXDATA)), TW, #unparseByteStack(TR), #unparseByteStack(TS))
      requires TW =/=Int 0 andBool TW =/=Int 1
  rule #sender(HT, TW, TR, TS) => #sender(ECDSARecover(HT, TW, TR, TS))
  rule #sender("")  => .Account
  rule #sender(STR) => #addr(#parseHexWord(Keccak256(STR))) requires STR =/=String ""
  syntax Int  ::=
    "#addrFromPrivateKey" "(" String ")" [function, klabel(addrFromPrivateKey)]
  rule [addrFromPrivateKey]: #addrFromPrivateKey ( KEY ) => #addr( #parseHexWord( Keccak256 ( Hex2Raw( ECDSAPubKey( Hex2Raw( KEY ) ) ) ) ) )  [concrete]
  syntax Int  ::=
    "#blockHeaderHash" "(" Int "," Int "," Int "," Int "," Int "," Int "," Bytes "," Int "," Int "," Int "," Int "," Int "," Bytes "," Int "," Int ")" [function, klabel(blockHeaderHash), symbol]
  | "#blockHeaderHash" "(" String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String ")" [function, klabel(#blockHashHeaderStr), symbol]
  | "#blockHeaderHash" "(" Int "," Int "," Int "," Int "," Int "," Int "," Bytes "," Int "," Int "," Int "," Int "," Int "," Bytes "," Int "," Int "," Int ")" [function, klabel(blockHeaderHashBaseFee), symbol]
  | "#blockHeaderHash" "(" String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String "," String ")" [function, klabel(#blockHashHeaderBaseFeeStr), symbol]
  rule #blockHeaderHash(HP:String, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord( Keccak256( #rlpEncode( [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN ] ) ) )
  rule #blockHeaderHash(HP:Int, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)
         => #parseHexWord( Keccak256( #rlpEncode( [ #wordBytes(HP), #wordBytes(HO), #addrBytes(HC)
                                                  , #wordBytes(HR), #wordBytes(HT), #wordBytes(HE)
                                                  , HB, HD, HI, HL, HG, HS, HX
                                                  , #wordBytes(HM), #padToWidth(8, #asByteStack(HN))
                                                  ]
                                                )
                                    )
                         )
  rule #blockHeaderHash(HP:String, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)
         => #parseHexWord( Keccak256( #rlpEncode( [ HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF ] ) ) )
  rule #blockHeaderHash(HP:Int, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)
         => #parseHexWord( Keccak256( #rlpEncode( [ #wordBytes(HP), #wordBytes(HO), #addrBytes(HC)
                                                  , #wordBytes(HR), #wordBytes(HT), #wordBytes(HE)
                                                  , HB, HD, HI, HL, HG, HS, HX
                                                  , #wordBytes(HM), #padToWidth(8, #asByteStack(HN))
                                                  , HF
                                                  ]
                                                )
                                    )
                         )
  syntax String  ::=
    "#hashSignedTx" "(" Int "," Int "," Int "," Account "," Int "," Bytes "," Int "," Bytes "," Bytes ")" [function, klabel(#hashSignedTx)]
  | "#hashTxData" "(" TxData ")" [function, klabel(#hashTxData)]
  rule #hashSignedTx(TN, TP, TG, TT, TV, TD, TW, TR, TS)
      => Keccak256( #rlpEncode([ TN, TP, TG, #addrBytes(TT), TV, TD, TW, TR, TS ]) )
  rule #hashTxData( TXDATA ) => Keccak256(                #rlpEncodeTxData(TXDATA) ) requires isLegacyTx    (TXDATA)
  rule #hashTxData( TXDATA ) => Keccak256( "\x01" +String #rlpEncodeTxData(TXDATA) ) requires isAccessListTx(TXDATA)
  rule #hashTxData( TXDATA ) => Keccak256( "\x02" +String #rlpEncodeTxData(TXDATA) ) requires isDynamicFeeTx(TXDATA)
  syntax Int  ::=
    "#parseHexWord" "(" String ")" [function, klabel(#parseHexWord)]
  | "#parseWord" "(" String ")" [function, klabel(#parseWord)]
  rule #parseHexWord("")   => 0
  rule #parseHexWord("0x") => 0
  rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")
  rule #parseWord("") => 0
  rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
  rule #parseWord(S)  => String2Int(S)  [owise]
  syntax String  ::=
    "#alignHexString" "(" String ")" [function, klabel(#alignHexString), total]
  rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
  rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0
  syntax Bytes  ::=
    "#parseHexBytes" "(" String ")" [function, klabel(#parseHexBytes)]
  | "#parseHexBytesAux" "(" String ")" [function, klabel(#parseHexBytesAux)]
  | "#parseByteStack" "(" String ")" [function, klabel(#parseByteStack), memo]
  | "#parseByteStackRaw" "(" String ")" [function, klabel(#parseByteStackRaw)]
  rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
  rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
  rule #parseHexBytesAux("") => .Bytes
  rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires lengthString(S) >=Int 2
  rule #parseByteStackRaw(S) => String2Bytes(S)
  syntax Map  ::=
    "#parseMap" "(" JSON ")" [function, klabel(#parseMap)]
  rule #parseMap( { .JSONs                      } ) => .Map
  rule #parseMap( { _   : (VALUE:String) , REST } ) => #parseMap({ REST })                                                requires #parseHexWord(VALUE) ==K 0
  rule #parseMap( { KEY : (VALUE:String) , REST } ) => #parseMap({ REST }) [ #parseHexWord(KEY) <- #parseHexWord(VALUE) ] requires #parseHexWord(VALUE) =/=K 0
  syntax Int  ::=
    "#parseAddr" "(" String ")" [function, klabel(#parseAddr)]
  rule #parseAddr(S) => #addr(#parseHexWord(S))
  syntax List  ::=
    "#parseAccessListStorageKeys" "(" JSONs ")" [function, klabel(#parseAccessListStorageKeys)]
  | "#parseAccessListStorageKeys" "(" JSONs "," List ")" [function, klabel(#parseAccessListStorageKeysAux)]
  rule #parseAccessListStorageKeys( J                           ) => #parseAccessListStorageKeys(J, .List)
  rule #parseAccessListStorageKeys([S:String, REST], RESULT:List) => #parseAccessListStorageKeys([REST], ListItem(#asWord(#parseByteStackRaw(S))) RESULT )
  rule #parseAccessListStorageKeys([ .JSONs       ], RESULT:List) => RESULT
  syntax String  ::=
    "#unparseByteStack" "(" Bytes ")" [function, klabel(unparseByteStack), symbol]
  rule #unparseByteStack(WS) => Bytes2String(WS)
  syntax String  ::=
    "#padByte" "(" String ")" [function, klabel(#padByte)]
  rule #padByte( S ) => S             requires lengthString(S) ==K 2
  rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1
  syntax String  ::=
    "#unparseQuantity" "(" Int ")" [function, klabel(#unparseQuantity)]
  rule #unparseQuantity( I ) => "0x" +String Base2String(I, 16)
  syntax String  ::=
    "#unparseData" "(" Int "," Int ")" [function, klabel(#unparseData)]
  | "#unparseDataBytes" "(" Bytes ")" [function, klabel(#unparseDataBytes)]
  rule #unparseData( DATA, LENGTH ) => #unparseDataBytes(#padToWidth(LENGTH,#asByteStack(DATA)))
  rule #unparseDataBytes( DATA ) => replaceFirst(Base2String(#asInteger(#asByteStack(1) +Bytes DATA), 16), "1", "0x")
  syntax Bytes  ::=
    "#addrBytes" "(" Account ")" [function, klabel(#addrBytes)]
  | "#wordBytes" "(" Int ")" [function, klabel(#wordBytes)]
  rule #addrBytes(.Account) => .Bytes
  rule #addrBytes(ACCT)     => #padToWidth(20, #asByteStack(ACCT)) requires #rangeAddress(ACCT)
  rule #wordBytes(WORD)     => #padToWidth(32, #asByteStack(WORD)) requires #rangeUInt(256, WORD)
  syntax String  ::=
    "Hex2Raw" "(" String ")" [function, klabel(Hex2Raw)]
  | "Raw2Hex" "(" String ")" [function, klabel(Raw2Hex)]
  rule Hex2Raw ( S ) => #unparseByteStack( #parseByteStack ( S ) )
  rule Raw2Hex ( S ) => #unparseDataBytes( #parseByteStackRaw ( S ) )
  syntax String  ::=
    "#rlpEncodeInt" "(" Int ")" [function, klabel(#rlpEncodeInt)]
  | "#rlpEncodeWord" "(" Int ")" [function, klabel(#rlpEncodeWord)]
  | "#rlpEncodeAddress" "(" Account ")" [function, klabel(#rlpEncodeAddress)]
  | "#rlpEncodeBytes" "(" Bytes ")" [function, klabel(#rlpEncodeBytes)]
  | "#rlpEncodeString" "(" String ")" [function, klabel(#rlpEncodeString)]
  | "#rlpEncode" "(" JSON ")" [function, klabel(#rlpEncode)]
  | "#rlpEncode" "(" JSONs "," StringBuffer ")" [function, klabel(#rlpEncodeJsonAux)]
  rule #rlpEncodeInt(0) => "\x80"
  rule #rlpEncodeInt(WORD) => chrChar(WORD) requires WORD >Int 0 andBool WORD <Int 128
  rule #rlpEncodeInt(WORD) => #rlpEncodeBytes(#asByteStack(WORD)) requires WORD >=Int 128
  rule #rlpEncodeWord(WORD) => #rlpEncodeBytes(#wordBytes(WORD))
  rule #rlpEncodeAddress(ACCT) => #rlpEncodeBytes(#addrBytes(ACCT))
  rule #rlpEncodeBytes(BYTES) => #rlpEncodeString(#unparseByteStack(BYTES))
  rule #rlpEncodeString(STR) => "\x80"                     requires lengthString(STR)  <Int 1
  rule #rlpEncodeString(STR) => STR                        requires lengthString(STR) ==Int 1 andBool ordChar(substrString(STR, 0, 1)) <Int 128
  rule #rlpEncodeString(STR) => #rlpEncodeLength(STR, 128)  [owise]
  syntax JSON  ::=
    Bytes
  rule #rlpEncode( [ J:JSONs ] ) => #rlpEncodeLength( #rlpEncode(J, .StringBuffer) , 192 )
  rule #rlpEncode( .JSONs                   , BUF ) => StringBuffer2String(BUF)
  rule #rlpEncode( (J:Int,       REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String #rlpEncodeInt(J)   )
  rule #rlpEncode( (J:String,    REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String #rlpEncodeString(J))
  rule #rlpEncode( (J:Bytes,     REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String #rlpEncodeBytes(J) )
  rule #rlpEncode( ([ J ],       REST:JSONs), BUF ) => #rlpEncode(REST, BUF +String #rlpEncode([ J ])  )
  syntax String  ::=
    "#rlpEncodeLength" "(" String "," Int ")" [function, klabel(#rlpEncodeLength)]
  | "#rlpEncodeLength" "(" String "," Int "," String ")" [function, klabel(#rlpEncodeLengthAux)]
  rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR                                requires           lengthString(STR) <Int 56
  rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires notBool ( lengthString(STR) <Int 56 )
  rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR
  syntax String  ::=
    "#rlpEncodeFullAccount" "(" Int "," Int "," Map "," Bytes ")" [function, klabel(#rlpEncodeFullAccount)]
  rule [rlpAcct]: #rlpEncodeFullAccount( NONCE, BAL, STORAGE, CODE )
                 => #rlpEncodeLength(         #rlpEncodeInt(NONCE)
                                      +String #rlpEncodeInt(BAL)
                                      +String #rlpEncodeString( Hex2Raw( Keccak256( #rlpEncodeMerkleTree( #storageRoot( STORAGE ) ) ) ) )
                                      +String #rlpEncodeString( Hex2Raw( Keccak256( #unparseByteStack( CODE ) ) ) )
                                    , 192
                                    )
  syntax String  ::=
    "#rlpEncodeReceipt" "(" Int "," Int "," Bytes "," List ")" [function, klabel(#rlpEncodeReceipt)]
  | "#rlpEncodeLogs" "(" List ")" [function, klabel(#rlpEncodeLogs)]
  | "#rlpEncodeLogsAux" "(" List "," StringBuffer ")" [function, klabel(#rlpEncodeLogsAux)]
  | "#rlpEncodeTopics" "(" List "," StringBuffer ")" [function, klabel(#rlpEncodeTopics)]
  rule [rlpReceipt]: #rlpEncodeReceipt(RS, RG, RB, RL)
                    => #rlpEncodeLength(         #rlpEncodeInt(RS)
                                         +String #rlpEncodeInt(RG)
                                         +String #rlpEncodeString(#unparseByteStack(RB))
                                         +String #rlpEncodeLogs(RL)
                                       , 192
                                       )
  rule #rlpEncodeLogs( LOGS ) => #rlpEncodeLogsAux( LOGS, .StringBuffer )
  rule #rlpEncodeLogsAux( .List, OUT ) => #rlpEncodeLength(StringBuffer2String(OUT),192)
  rule #rlpEncodeLogsAux( ( ListItem({ ACCT | TOPICS | DATA }) => .List ) _
                          , ( OUT => OUT +String #rlpEncodeLength(         #rlpEncodeAddress(ACCT)
                                                                   +String #rlpEncodeTopics(TOPICS,.StringBuffer)
                                                                   +String #rlpEncodeString(#unparseByteStack(DATA))
                                                                 , 192
                                                                 )
                            )
                          )
  rule #rlpEncodeTopics( .List, OUT ) => #rlpEncodeLength(StringBuffer2String(OUT),192)
  rule #rlpEncodeTopics( ( ListItem( X:Int ) => .List ) _
                         , ( OUT => OUT +String #rlpEncodeWord(X) )
                         )
  syntax String  ::=
    "#rlpEncodeTxData" "(" TxData ")" [function, klabel(#rlpEncodeTxData)]
  rule #rlpEncodeTxData( LegacyTxData( TN, TP, TG, TT, TV, TD ) )
      => #rlpEncode( [ TN, TP, TG, #addrBytes(TT), TV, TD ] )
  rule #rlpEncodeTxData( LegacyProtectedTxData( TN, TP, TG, TT, TV, TD, CID ) )
      => #rlpEncode( [ TN, TP, TG, #addrBytes(TT), TV, TD, CID, "", "" ] )
  rule #rlpEncodeTxData( AccessListTxData( TN, TP, TG, TT, TV, TD, CID, [TA] ) )
      => #rlpEncode( [ CID, TN, TP, TG, #addrBytes(TT), TV, TD, [TA] ] )
  rule #rlpEncodeTxData( DynamicFeeTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, [TA]) )
      => #rlpEncode( [ CID, TN, TPF, TM, TG, #addrBytes(TT), TV, DATA, [TA] ] )
  syntax String  ::=
    "#rlpEncodeMerkleTree" "(" MerkleTree ")" [function, klabel(#rlpEncodeMerkleTree)]
  rule #rlpEncodeMerkleTree ( .MerkleTree ) => "\x80"
  rule #rlpEncodeMerkleTree ( MerkleLeaf ( PATH, VALUE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #unparseByteStack( #HPEncode( PATH, 1 ) ) )
                           +String #rlpEncodeString( VALUE )
                         , 192
                         )
  rule #rlpEncodeMerkleTree ( MerkleExtension ( PATH, TREE ) )
      => #rlpEncodeLength(         #rlpEncodeString( #unparseByteStack( #HPEncode( PATH, 0 ) ) )
                           +String #rlpMerkleH( #rlpEncodeMerkleTree( TREE ) )
                         , 192
                         )
  rule #rlpEncodeMerkleTree ( MerkleBranch ( M , VALUE ) )
      => #rlpEncodeLength(         MerkleMapRLP(M, 0) +String MerkleMapRLP(M, 1)
                           +String MerkleMapRLP(M, 2) +String MerkleMapRLP(M, 3)
                           +String MerkleMapRLP(M, 4) +String MerkleMapRLP(M, 5)
                           +String MerkleMapRLP(M, 6) +String MerkleMapRLP(M, 7)
                           +String MerkleMapRLP(M, 8) +String MerkleMapRLP(M, 9)
                           +String MerkleMapRLP(M,10) +String MerkleMapRLP(M,11)
                           +String MerkleMapRLP(M,12) +String MerkleMapRLP(M,13)
                           +String MerkleMapRLP(M,14) +String MerkleMapRLP(M,15)
                           +String #rlpEncodeString( VALUE )
                         , 192
                         )
  syntax String  ::=
    "MerkleMapRLP" "(" Map "," Int ")" [function, klabel(MerkleMapRLP)]
  rule MerkleMapRLP(M, I) => #rlpMerkleH( #rlpEncodeMerkleTree( { M[I] orDefault .MerkleTree }:>MerkleTree ) )
  syntax String  ::=
    "#rlpMerkleH" "(" String ")" [function, klabel(MerkleRLPAux)]
  rule #rlpMerkleH ( X ) => #rlpEncodeString( Hex2Raw( Keccak256( X ) ) )
      requires lengthString(X) >=Int 32
  rule #rlpMerkleH ( X ) => X
      requires notBool lengthString(X) >=Int 32
  syntax JSON  ::=
    "#rlpDecode" "(" String ")" [function, klabel(#rlpDecode)]
  | "#rlpDecode" "(" String "," LengthPrefix ")" [function, klabel(#rlpDecodeAux)]
  rule #rlpDecode(STR) => #rlpDecode(STR, #decodeLengthPrefix(STR, 0))
  rule #rlpDecode(STR,  #str( LEN, POS)) => substrString(STR, POS, POS +Int LEN)
  rule #rlpDecode(STR, #list(_LEN, POS)) => [#rlpDecodeList(STR, POS)]
  syntax JSONs  ::=
    "#rlpDecodeList" "(" String "," Int ")" [function, klabel(#rlpDecodeList)]
  | "#rlpDecodeList" "(" String "," Int "," LengthPrefix ")" [function, klabel(#rlpDecodeListAux)]
  rule #rlpDecodeList(STR, POS) => #rlpDecodeList(STR, POS, #decodeLengthPrefix(STR, POS)) requires POS <Int lengthString(STR)
  rule #rlpDecodeList(  _,   _) => .JSONs  [owise]
  rule #rlpDecodeList(STR, POS, _:LengthPrefixType(L, P)) => #rlpDecode(substrString(STR, POS, L +Int P)) , #rlpDecodeList(STR, L +Int P)
  syntax LengthPrefixType  ::=
    "#str"
  | "#list"
  syntax LengthPrefix  ::=
    LengthPrefixType "(" Int "," Int ")"
  | "#decodeLengthPrefix" "(" String "," Int ")" [function, klabel(#decodeLengthPrefix)]
  | "#decodeLengthPrefix" "(" String "," Int "," Int ")" [function, klabel(#decodeLengthPrefixAux)]
  | "#decodeLengthPrefixLength" "(" LengthPrefixType "," String "," Int "," Int ")" [function, klabel(#decodeLengthPrefixLength)]
  | "#decodeLengthPrefixLength" "(" LengthPrefixType "," Int "," Int "," Int ")" [function, klabel(#decodeLengthPrefixLengthAux)]
  rule #decodeLengthPrefix(STR, START) => #decodeLengthPrefix(STR, START, ordChar(substrString(STR, START, START +Int 1)))
  rule #decodeLengthPrefix(  _, START, B0) => #str(1, START)                                   requires B0 <Int 128
  rule #decodeLengthPrefix(  _, START, B0) => #str(B0 -Int 128, START +Int 1)                  requires B0 >=Int 128 andBool B0 <Int (128 +Int 56)
  rule #decodeLengthPrefix(STR, START, B0) => #decodeLengthPrefixLength(#str, STR, START, B0)  requires B0 >=Int (128 +Int 56) andBool B0 <Int 192
  rule #decodeLengthPrefix(  _, START, B0) => #list(B0 -Int 192, START +Int 1)                 requires B0 >=Int 192 andBool B0 <Int 192 +Int 56
  rule #decodeLengthPrefix(STR, START, B0) => #decodeLengthPrefixLength(#list, STR, START, B0)  [owise]
  rule #decodeLengthPrefixLength(#str,  STR, START, B0) => #decodeLengthPrefixLength(#str,  START, B0 -Int 128 -Int 56 +Int 1, #asWord(#parseByteStackRaw(substrString(STR, START +Int 1, START +Int 1 +Int (B0 -Int 128 -Int 56 +Int 1)))))
  rule #decodeLengthPrefixLength(#list, STR, START, B0) => #decodeLengthPrefixLength(#list, START, B0 -Int 192 -Int 56 +Int 1, #asWord(#parseByteStackRaw(substrString(STR, START +Int 1, START +Int 1 +Int (B0 -Int 192 -Int 56 +Int 1)))))
  rule #decodeLengthPrefixLength(TYPE, START, LL, L) => TYPE(L, START +Int 1 +Int LL)
  syntax JSONs  ::=
    "#rlpDecodeTransaction" "(" Bytes ")" [function, klabel(#rlpDecodeTransaction)]
  rule #rlpDecodeTransaction(T) => #unparseByteStack(#range(T, 0, 1)), #rlpDecode(#unparseByteStack(#range(T, 1,  lengthBytes(T) -Int 1)))
  syntax KItem  ::=
    Int
  | MerkleTree
  syntax MerkleTree  ::=
    ".MerkleTree"
  | "MerkleBranch" "(" Map "," String ")" [klabel(MerkleBranch)]
  | "MerkleExtension" "(" Bytes "," MerkleTree ")" [klabel(MerkleExtension)]
  | "MerkleLeaf" "(" Bytes "," String ")" [klabel(MerkleLeaf)]
  syntax MerkleTree  ::=
    "MerkleUpdate" "(" MerkleTree "," String "," String ")" [function, klabel(MerkleUpdate)]
  | "MerkleUpdate" "(" MerkleTree "," Bytes "," String ")" [function, klabel(MerkleUpdateAux)]
  | "MerklePut" "(" MerkleTree "," Bytes "," String ")" [function, klabel(MerklePut)]
  | "MerkleDelete" "(" MerkleTree "," Bytes ")" [function, klabel(MerkleDelete)]
  rule MerkleUpdate ( TREE, S:String, VALUE ) => MerkleUpdate ( TREE, #nibbleize ( #parseByteStackRaw( S ) ), VALUE )
  rule MerkleUpdate ( TREE, PATH:Bytes, VALUE ) => MerklePut ( TREE, PATH, VALUE ) requires VALUE =/=String ""
  rule MerkleUpdate ( TREE, PATH:Bytes, ""    ) => MerkleDelete ( TREE, PATH )
  rule MerklePut ( .MerkleTree, PATH:Bytes, VALUE ) => MerkleLeaf ( PATH, VALUE )
  rule MerklePut ( MerkleLeaf ( LEAFPATH, _ ), PATH, VALUE )
      => MerkleLeaf( LEAFPATH, VALUE )
      requires LEAFPATH ==K PATH
  rule MerklePut ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => MerklePut ( MerklePut ( MerkleBranch( .Map, "" ), LEAFPATH, LEAFVALUE ), PATH, VALUE )
      requires lengthBytes( LEAFPATH ) >Int 0
       andBool lengthBytes( PATH ) >Int 0
       andBool LEAFPATH[0] =/=Int PATH[0]
  rule MerklePut ( MerkleLeaf ( LEAFPATH, LEAFVALUE ), PATH, VALUE )
      => #merkleExtensionBuilder( .Bytes, LEAFPATH, LEAFVALUE, PATH, VALUE )
      requires #unparseByteStack( LEAFPATH ) =/=String #unparseByteStack( PATH )
       andBool lengthBytes( LEAFPATH ) >Int 0
       andBool lengthBytes( PATH )     >Int 0
       andBool LEAFPATH[0] ==Int PATH[0]
  rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => MerkleExtension ( EXTPATH, MerklePut ( EXTTREE, .Bytes, VALUE ) )
      requires EXTPATH ==K PATH
  rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), PATH, VALUE ), EXTPATH, EXTTREE )
      requires lengthBytes( PATH ) >Int 0
       andBool EXTPATH[0] =/=Int PATH[0]
  rule MerklePut ( MerkleExtension ( EXTPATH, EXTTREE ), PATH, VALUE )
      => #merkleExtensionSplitter( .Bytes, EXTPATH, EXTTREE, PATH, VALUE )
      requires #unparseByteStack( EXTPATH ) =/=String #unparseByteStack( PATH )
       andBool lengthBytes( PATH ) >Int 0
       andBool EXTPATH[0] ==Int PATH[0]
  rule MerklePut ( MerkleBranch( M, _ ), PATH, VALUE )
      => MerkleBranch( M, VALUE )
      requires lengthBytes( PATH ) ==Int 0
  rule MerklePut ( MerkleBranch( M, BRANCHVALUE ), PATH, VALUE )
      => #merkleUpdateBranch ( M, BRANCHVALUE, PATH[0], #range(PATH, 1, lengthBytes(PATH) -Int 1), VALUE )
      requires lengthBytes( PATH ) >Int 0
  rule MerkleDelete( .MerkleTree, _ ) => .MerkleTree
  rule MerkleDelete( MerkleLeaf( LPATH, _V ), PATH ) => .MerkleTree                           requires LPATH ==K  PATH
  rule MerkleDelete( MerkleLeaf( LPATH,  V ), PATH ) => MerkleCheck( MerkleLeaf( LPATH, V ) ) requires LPATH =/=K PATH
  rule MerkleDelete( MerkleExtension( EXTPATH, TREE ), PATH ) => MerkleExtension( EXTPATH, TREE ) requires notBool (lengthBytes(EXTPATH) <=Int lengthBytes(PATH) andBool #range(PATH, 0, lengthBytes(EXTPATH)) ==K EXTPATH)
  rule MerkleDelete( MerkleExtension( EXTPATH, TREE ), PATH )
      => MerkleCheck( MerkleExtension( EXTPATH, MerkleDelete( TREE, #range(PATH, lengthBytes(EXTPATH), lengthBytes(PATH) -Int lengthBytes(EXTPATH)) ) ) )
      requires lengthBytes(EXTPATH) <=Int lengthBytes(PATH) andBool #range(PATH, 0, lengthBytes(EXTPATH)) ==K EXTPATH
  rule MerkleDelete( MerkleBranch( M, _V ), PATH ) => MerkleCheck( MerkleBranch( M, "" ) ) requires lengthBytes(PATH) ==Int 0
  rule MerkleDelete( MerkleBranch( M,  V ), PATH ) => MerkleBranch( M, V )                 requires lengthBytes(PATH) >Int 0 andBool notBool PATH[0] in_keys(M)
  rule MerkleDelete( MerkleBranch( M,  V ), PATH )
      => MerkleCheck( MerkleBranch( M[PATH[0] <- MerkleDelete( {M[PATH[0]]}:>MerkleTree, #range(PATH, 1, lengthBytes(PATH) -Int 1) )], V ) )
      requires lengthBytes(PATH) >Int 0 andBool PATH[0] in_keys(M)
  syntax MerkleTree  ::=
    "MerkleCheck" "(" MerkleTree ")" [function, klabel(MerkleCheck)]
  rule MerkleCheck( TREE ) => TREE  [owise]
  rule MerkleCheck( MerkleLeaf( _, "" ) => .MerkleTree )
  rule MerkleCheck( MerkleBranch( .Map                   , V  ) => MerkleLeaf( .Bytes, V )                             )
  rule MerkleCheck( MerkleBranch( X |-> T                , "" ) => MerkleExtension( #range(#asByteStack(X), 0, 1), T ) ) requires T =/=K .MerkleTree
  rule MerkleCheck( MerkleBranch( M => #cleanBranchMap(M), _  )                                                        ) requires .MerkleTree in values(M)
  rule MerkleCheck( MerkleExtension( _, .MerkleTree                                      ) => .MerkleTree               )
  rule MerkleCheck( MerkleExtension( P1, MerkleLeaf( P2, V )                             ) => MerkleLeaf( P1 +Bytes P2, V ) )
  rule MerkleCheck( MerkleExtension( P1 => P1 +Bytes P2, MerkleExtension( P2, TREE ) => TREE )                              )
  syntax MerkleTree  ::=
    "MerkleUpdateMap" "(" MerkleTree "," Map ")" [function, klabel(MerkleUpdateMap)]
  | "MerkleUpdateMapAux" "(" MerkleTree "," Map "," List ")" [function, klabel(MerkleUpdateMapAux)]
  rule MerkleUpdateMap(TREE, MMAP) => MerkleUpdateMapAux(TREE, MMAP, keys_list(MMAP))
  rule MerkleUpdateMapAux(TREE, _, .List ) => TREE
  rule MerkleUpdateMapAux(TREE                                                    , MMAP, ListItem(KEY) REST)
      => MerkleUpdateMapAux(MerkleUpdate(TREE, #nibbleize(KEY), {MMAP[KEY]}:>String), MMAP,               REST)
  syntax Bytes  ::=
    "#nibbleize" "(" Bytes ")" [function, klabel(#nibbleize)]
  | "#byteify" "(" Bytes ")" [function, klabel(#byteify)]
  rule #nibbleize ( B ) => (          #range( #asByteStack ( B [ 0 ] /Int 16 ), 0, 1 )
                               +Bytes ( #range( #asByteStack ( B [ 0 ] %Int 16 ), 0, 1 ) )
                             ) +Bytes #nibbleize ( #range(B, 1, lengthBytes(B) -Int 1) )
      requires lengthBytes(B) >Int 0
  rule #nibbleize ( B ) => .Bytes requires notBool lengthBytes(B) >Int 0
  rule #byteify ( B ) =>    #range( #asByteStack ( B[0] *Int 16 +Int B[1] ), 0, 1 )
                       +Bytes #byteify ( #range( B, 2, lengthBytes(B) -Int 2 ) )
      requires lengthBytes(B) >Int 0
  rule #byteify ( B ) => .Bytes requires notBool lengthBytes(B) >Int 0
  syntax Bytes  ::=
    "#HPEncode" "(" Bytes "," Int ")" [function, klabel(#HPEncode)]
  rule #HPEncode ( X, T ) => #asByteStack ( ( HPEncodeAux(T) +Int 1 ) *Int 16 +Int X[0] ) +Bytes #byteify( #range(X, 1, lengthBytes(X) -Int 1) )
      requires lengthBytes(X) %Int 2 =/=Int 0
  rule #HPEncode ( X, T ) => #range(#asByteStack ( HPEncodeAux(T) *Int 16 ), 0, 1) +Bytes #byteify( X )
      requires notBool lengthBytes(X) %Int 2 =/=Int 0
  syntax Int  ::=
    "HPEncodeAux" "(" Int ")" [function, klabel(HPEncodeAux)]
  rule HPEncodeAux ( X ) => 0 requires         X ==Int 0
  rule HPEncodeAux ( X ) => 2 requires notBool X ==Int 0
  syntax Map  ::=
    "#cleanBranchMap" "(" Map ")" [function, klabel(#cleanBranchMap)]
  | "#cleanBranchMapAux" "(" Map "," List "," Set ")" [function, klabel(#cleanBranchMapAux)]
  rule #cleanBranchMap( M ) => #cleanBranchMapAux( M, keys_list(M), .Set )
  rule #cleanBranchMapAux(                   M,                        .List,                      S ) => removeAll( M, S )
  rule #cleanBranchMapAux( X |-> .MerkleTree _, (ListItem(X) => .List) _    , (.Set => SetItem(X)) _ )
  rule #cleanBranchMapAux(                   _, (ListItem(_) => .List) _    ,                      _ )  [owise]
  syntax MerkleTree  ::=
    "#merkleUpdateBranch" "(" Map "," String "," Int "," Bytes "," String ")" [function, klabel(#merkleUpdateBranch)]
  rule #merkleUpdateBranch ( X |-> TREE M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerklePut( TREE, PATH, VALUE )], BRANCHVALUE )
  rule #merkleUpdateBranch ( M, BRANCHVALUE, X, PATH, VALUE )
      => MerkleBranch( M[X <- MerkleLeaf( PATH, VALUE )], BRANCHVALUE )  [owise]
  syntax MerkleTree  ::=
    "#merkleExtensionBuilder" "(" Bytes "," Bytes "," String "," Bytes "," String ")" [function, klabel(#merkleExtensionBuilder)]
  | "#merkleExtensionBuilderAux" "(" Bytes "," Bytes "," String "," Bytes "," String ")" [function, klabel(#merkleExtensionBuilderAux)]
  rule #merkleExtensionBuilder(PATH, P1, V1, P2, V2)
      => #merkleExtensionBuilderAux(PATH, P1, V1, P2, V2)
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0
  rule #merkleExtensionBuilder(PATH, P1, V1, P2, V2)
      => MerkleExtension( PATH, MerklePut( MerklePut( MerkleBranch( .Map, "" ), P1, V1 ), P2, V2 ) )
       [owise]
  rule #merkleExtensionBuilderAux( PATH, P1, V1, P2, V2 )
      => #merkleExtensionBuilder( PATH +Bytes (#range(P1, 0, 1))
                                , #range(P1, 1, lengthBytes(P1) -Int 1), V1
                                , #range(P2, 1, lengthBytes(P2) -Int 1), V2
                                )
      requires P1[0] ==Int P2[0]
  rule #merkleExtensionBuilderAux( PATH, P1, V1, P2, V2 )
      => MerkleExtension( PATH, MerklePut( MerklePut( MerkleBranch( .Map, "" ), P1, V1 ), P2, V2 ) )
       [owise]
  syntax MerkleTree  ::=
    "#merkleExtensionBrancher" "(" MerkleTree "," Bytes "," MerkleTree ")" [function, klabel(#merkleExtensionBrancher)]
  rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- MerkleExtension( #range(PATH, 1, lengthBytes(PATH) -Int 1), EXTTREE )], VALUE )
      requires lengthBytes(PATH) >Int 1
  rule #merkleExtensionBrancher( MerkleBranch(M, VALUE), PATH, EXTTREE )
      => MerkleBranch( M[PATH[0] <- EXTTREE], VALUE )
      requires lengthBytes(PATH) ==Int 1
  syntax MerkleTree  ::=
    "#merkleExtensionSplitter" "(" Bytes "," Bytes "," MerkleTree "," Bytes "," String ")" [function, klabel(#merkleExtensionSplitter)]
  rule #merkleExtensionSplitter( PATH => PATH +Bytes (#range(P1, 0, 1))
                                 , P1   => #range(P1, 1, lengthBytes(P1) -Int 1), _
                                 , P2   => #range(P2, 1, lengthBytes(P2) -Int 1), _
                                 )
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0
       andBool P1[0] ==Int P2[0]
  rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), P2, VALUE ), P1, TREE ) )
      requires lengthBytes(P1) >Int 0
       andBool lengthBytes(P2) >Int 0
       andBool P1[0] =/=Int P2[0]
  rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, MerklePut( TREE, P2, VALUE ) )
      requires lengthBytes(P1) ==Int 0
  rule #merkleExtensionSplitter( PATH, P1, TREE, P2, VALUE )
      => MerkleExtension( PATH, #merkleExtensionBrancher( MerklePut( MerkleBranch( .Map, "" ), P2, VALUE ), P1, TREE ) )
      requires lengthBytes(P2) ==Int 0
  syntax Map  ::=
    "#intMap2StorageMap" "(" Map ")" [function, klabel(#intMap2StorageMap)]
  | "#intMap2StorageMapAux" "(" Map "," Map "," List ")" [function, klabel(#intMap2StorageMapAux)]
  rule #intMap2StorageMap( M ) => #intMap2StorageMapAux( .Map, M, keys_list(M) )
  rule #intMap2StorageMapAux( SMAP, _, .List ) => SMAP
  rule #intMap2StorageMapAux( SMAP, IMAP, ListItem(K) REST )
      => #intMap2StorageMapAux( #wordBytes(K) |-> #rlpEncodeInt({IMAP[K]}:>Int) SMAP, IMAP, REST )
      requires {IMAP[K]}:>Int =/=Int 0
  rule #intMap2StorageMapAux( SMAP, IMAP, ListItem(K) REST )
      => #intMap2StorageMapAux( SMAP, IMAP, REST )
      requires {IMAP[K]}:>Int ==Int 0
  syntax MerkleTree  ::=
    "#storageRoot" "(" Map ")" [function, klabel(#storageRoot)]
  rule #storageRoot( STORAGE ) => MerkleUpdateMap( .MerkleTree, #intMap2StorageMap( STORAGE ) )
  syntax Map  ::=
    "#precompiledAccountsMap" "(" Set ")" [function, klabel(#precompiledAccountsMap)]
  | "#precompiledAccountsMapAux" "(" List "," Map ")" [function, klabel(#precompiledAccountsMapAux)]
  rule #precompiledAccountsMap( ACCTS ) => #precompiledAccountsMapAux( Set2List( ACCTS ), .Map )
  rule #precompiledAccountsMapAux( .List, M ) => M
  rule #precompiledAccountsMapAux( (ListItem( ACCT ) => .List) _, M => M[#parseByteStackRaw( Hex2Raw( #unparseData( ACCT, 20 ) ) ) <- #emptyContractRLP] )
  syntax String  ::=
    "#emptyContractRLP" [function]
  rule #emptyContractRLP => #rlpEncodeLength(         #rlpEncodeInt(0)
                                                +String #rlpEncodeInt(0)
                                                +String #rlpEncodeString( Hex2Raw( Keccak256("\x80") ) )
                                                +String #rlpEncodeString( Hex2Raw( Keccak256("") ) )
                                              , 192
                                              )
endmodule

module EVM-DATA
  imports public EVM-TYPES
  imports public SERIALIZATION
  imports public STRING-BUFFER
  imports public MAP-SYMBOLIC
  imports public SET-SYMBOLIC
  imports public COLLECTIONS
  imports public JSON-EXT
endmodule

module NETWORK
  imports public STRING-SYNTAX
  syntax String  ::=
    "StatusCode2String" "(" StatusCode ")" [function, klabel(StatusCode2String)]
  syntax ExceptionalStatusCode  ::=
    "EVMC_FAILURE"
  | "EVMC_INVALID_INSTRUCTION"
  | "EVMC_UNDEFINED_INSTRUCTION"
  | "EVMC_OUT_OF_GAS"
  | "EVMC_BAD_JUMP_DESTINATION"
  | "EVMC_STACK_OVERFLOW"
  | "EVMC_STACK_UNDERFLOW"
  | "EVMC_CALL_DEPTH_EXCEEDED"
  | "EVMC_INVALID_MEMORY_ACCESS"
  | "EVMC_STATIC_MODE_VIOLATION"
  | "EVMC_PRECOMPILE_FAILURE"
  | "EVMC_NONCE_EXCEEDED"
  rule StatusCode2String(EVMC_FAILURE)               => "EVMC_FAILURE"
  rule StatusCode2String(EVMC_INVALID_INSTRUCTION)   => "EVMC_INVALID_INSTRUCTION"
  rule StatusCode2String(EVMC_UNDEFINED_INSTRUCTION) => "EVMC_UNDEFINED_INSTRUCTION"
  rule StatusCode2String(EVMC_OUT_OF_GAS)            => "EVMC_OUT_OF_GAS"
  rule StatusCode2String(EVMC_BAD_JUMP_DESTINATION)  => "EVMC_BAD_JUMP_DESTINATION"
  rule StatusCode2String(EVMC_STACK_OVERFLOW)        => "EVMC_STACK_OVERFLOW"
  rule StatusCode2String(EVMC_STACK_UNDERFLOW)       => "EVMC_STACK_UNDERFLOW"
  rule StatusCode2String(EVMC_CALL_DEPTH_EXCEEDED)   => "EVMC_CALL_DEPTH_EXCEEDED"
  rule StatusCode2String(EVMC_INVALID_MEMORY_ACCESS) => "EVMC_INVALID_MEMORY_ACCESS"
  rule StatusCode2String(EVMC_STATIC_MODE_VIOLATION) => "EVMC_STATIC_MODE_VIOLATION"
  rule StatusCode2String(EVMC_PRECOMPILE_FAILURE)    => "EVMC_PRECOMPILE_FAILURE"
  rule StatusCode2String(EVMC_NONCE_EXCEEDED)        => "EVMC_NONCE_EXCEEDED"
  syntax EndStatusCode  ::=
    ExceptionalStatusCode
  | "EVMC_SUCCESS"
  | "EVMC_REVERT"
  rule StatusCode2String(EVMC_SUCCESS) => "EVMC_SUCCESS"
  rule StatusCode2String(EVMC_REVERT)  => "EVMC_REVERT"
  syntax StatusCode  ::=
    EndStatusCode
  | "EVMC_REJECTED"
  | "EVMC_INTERNAL_ERROR"
  | ".StatusCode"
  rule StatusCode2String(EVMC_REJECTED)       => "EVMC_REJECTED"
  rule StatusCode2String(EVMC_INTERNAL_ERROR) => "EVMC_INTERNAL_ERROR"
  rule StatusCode2String(.StatusCode)         => ""
  syntax ExceptionalStatusCode  ::=
    "EVMC_ACCOUNT_ALREADY_EXISTS"
  | "EVMC_BALANCE_UNDERFLOW"
  rule StatusCode2String(EVMC_ACCOUNT_ALREADY_EXISTS) => "EVMC_ACCOUNT_ALREADY_EXISTS"
  rule StatusCode2String(EVMC_BALANCE_UNDERFLOW)      => "EVMC_BALANCE_UNDERFLOW"
endmodule

module SCHEDULE
  imports public EVM-DATA
  syntax Bool  ::=
    ScheduleFlag "<<" Schedule ">>" [function, total]
  syntax ScheduleFlag  ::=
    "Gselfdestructnewaccount"
  | "Gstaticcalldepth"
  | "Gemptyisnonexistent"
  | "Gzerovaluenewaccountgas"
  | "Ghasrevert"
  | "Ghasreturndata"
  | "Ghasstaticcall"
  | "Ghasshift"
  | "Ghasdirtysstore"
  | "Ghascreate2"
  | "Ghasextcodehash"
  | "Ghasselfbalance"
  | "Ghassstorestipend"
  | "Ghaschainid"
  | "Ghasaccesslist"
  | "Ghasbasefee"
  | "Ghasrejectedfirstbyte"
  | "Ghasprevrandao"
  syntax Int  ::=
    ScheduleConst "<" Schedule ">" [function, total]
  syntax ScheduleConst  ::=
    "Gzero"
  | "Gbase"
  | "Gverylow"
  | "Glow"
  | "Gmid"
  | "Ghigh"
  | "Gextcodesize"
  | "Gextcodecopy"
  | "Gbalance"
  | "Gsload"
  | "Gjumpdest"
  | "Gsstoreset"
  | "Gsstorereset"
  | "Rsstoreclear"
  | "Rselfdestruct"
  | "Gselfdestruct"
  | "Gcreate"
  | "Gcodedeposit"
  | "Gcall"
  | "Gcallvalue"
  | "Gcallstipend"
  | "Gnewaccount"
  | "Gexp"
  | "Gexpbyte"
  | "Gmemory"
  | "Gtxcreate"
  | "Gtxdatazero"
  | "Gtxdatanonzero"
  | "Gtransaction"
  | "Glog"
  | "Glogdata"
  | "Glogtopic"
  | "Gsha3"
  | "Gsha3word"
  | "Gcopy"
  | "Gblockhash"
  | "Gquadcoeff"
  | "maxCodeSize"
  | "Rb"
  | "Gquaddivisor"
  | "Gecadd"
  | "Gecmul"
  | "Gecpairconst"
  | "Gecpaircoeff"
  | "Gfround"
  | "Gcoldsload"
  | "Gcoldaccountaccess"
  | "Gwarmstorageread"
  | "Gaccesslistaddress"
  | "Gaccessliststoragekey"
  | "Rmaxquotient"
  syntax Schedule  ::=
    "DEFAULT" [klabel(DEFAULT_EVM), smtlib(schedule_DEFAULT), symbol]
  rule Gzero    < DEFAULT > => 0
  rule Gbase    < DEFAULT > => 2
  rule Gverylow < DEFAULT > => 3
  rule Glow     < DEFAULT > => 5
  rule Gmid     < DEFAULT > => 8
  rule Ghigh    < DEFAULT > => 10
  rule Gexp      < DEFAULT > => 10
  rule Gexpbyte  < DEFAULT > => 10
  rule Gsha3     < DEFAULT > => 30
  rule Gsha3word < DEFAULT > => 6
  rule Gsload       < DEFAULT > => 50
  rule Gsstoreset   < DEFAULT > => 20000
  rule Gsstorereset < DEFAULT > => 5000
  rule Rsstoreclear < DEFAULT > => 15000
  rule Glog      < DEFAULT > => 375
  rule Glogdata  < DEFAULT > => 8
  rule Glogtopic < DEFAULT > => 375
  rule Gcall        < DEFAULT > => 40
  rule Gcallstipend < DEFAULT > => 2300
  rule Gcallvalue   < DEFAULT > => 9000
  rule Gnewaccount  < DEFAULT > => 25000
  rule Gcreate       < DEFAULT > => 32000
  rule Gcodedeposit  < DEFAULT > => 200
  rule Gselfdestruct < DEFAULT > => 0
  rule Rselfdestruct < DEFAULT > => 24000
  rule Gmemory      < DEFAULT > => 3
  rule Gquadcoeff   < DEFAULT > => 512
  rule Gcopy        < DEFAULT > => 3
  rule Gquaddivisor < DEFAULT > => 20
  rule Gtransaction   < DEFAULT > => 21000
  rule Gtxcreate      < DEFAULT > => 53000
  rule Gtxdatazero    < DEFAULT > => 4
  rule Gtxdatanonzero < DEFAULT > => 68
  rule Gjumpdest    < DEFAULT > => 1
  rule Gbalance     < DEFAULT > => 20
  rule Gblockhash   < DEFAULT > => 20
  rule Gextcodesize < DEFAULT > => 20
  rule Gextcodecopy < DEFAULT > => 20
  rule Gecadd       < DEFAULT > => 500
  rule Gecmul       < DEFAULT > => 40000
  rule Gecpairconst < DEFAULT > => 100000
  rule Gecpaircoeff < DEFAULT > => 80000
  rule Gfround      < DEFAULT > => 1
  rule maxCodeSize < DEFAULT > => 2 ^Int 32 -Int 1
  rule Rb          < DEFAULT > => 5 *Int (10 ^Int 18)
  rule Gcoldsload         < DEFAULT > => 0
  rule Gcoldaccountaccess < DEFAULT > => 0
  rule Gwarmstorageread   < DEFAULT > => 0
  rule Gaccessliststoragekey < DEFAULT > => 0
  rule Gaccesslistaddress    < DEFAULT > => 0
  rule Rmaxquotient < DEFAULT > => 2
  rule Gselfdestructnewaccount << DEFAULT >> => false
  rule Gstaticcalldepth        << DEFAULT >> => true
  rule Gemptyisnonexistent     << DEFAULT >> => false
  rule Gzerovaluenewaccountgas << DEFAULT >> => true
  rule Ghasrevert              << DEFAULT >> => false
  rule Ghasreturndata          << DEFAULT >> => false
  rule Ghasstaticcall          << DEFAULT >> => false
  rule Ghasshift               << DEFAULT >> => false
  rule Ghasdirtysstore         << DEFAULT >> => false
  rule Ghassstorestipend       << DEFAULT >> => false
  rule Ghascreate2             << DEFAULT >> => false
  rule Ghasextcodehash         << DEFAULT >> => false
  rule Ghasselfbalance         << DEFAULT >> => false
  rule Ghaschainid             << DEFAULT >> => false
  rule Ghasaccesslist          << DEFAULT >> => false
  rule Ghasbasefee             << DEFAULT >> => false
  rule Ghasrejectedfirstbyte   << DEFAULT >> => false
  rule Ghasprevrandao          << DEFAULT >> => false
  syntax Schedule  ::=
    "FRONTIER" [klabel(FRONTIER_EVM), smtlib(schedule_FRONTIER), symbol]
  rule Gtxcreate  < FRONTIER > => 21000
  rule SCHEDCONST < FRONTIER > => SCHEDCONST < DEFAULT > requires SCHEDCONST =/=K Gtxcreate
  rule SCHEDFLAG << FRONTIER >> => SCHEDFLAG << DEFAULT >>
  syntax Schedule  ::=
    "HOMESTEAD" [klabel(HOMESTEAD_EVM), smtlib(schedule_HOMESTEAD), symbol]
  rule SCHEDCONST < HOMESTEAD > => SCHEDCONST < DEFAULT >
  rule SCHEDFLAG << HOMESTEAD >> => SCHEDFLAG << DEFAULT >>
  syntax Schedule  ::=
    "TANGERINE_WHISTLE" [klabel(TANGERINE_WHISTLE_EVM), smtlib(schedule_TANGERINE_WHISTLE), symbol]
  rule Gbalance      < TANGERINE_WHISTLE > => 400
  rule Gsload        < TANGERINE_WHISTLE > => 200
  rule Gcall         < TANGERINE_WHISTLE > => 700
  rule Gselfdestruct < TANGERINE_WHISTLE > => 5000
  rule Gextcodesize  < TANGERINE_WHISTLE > => 700
  rule Gextcodecopy  < TANGERINE_WHISTLE > => 700
  rule SCHEDCONST    < TANGERINE_WHISTLE > => SCHEDCONST < HOMESTEAD >
      requires notBool      ( SCHEDCONST ==K Gbalance      orBool SCHEDCONST ==K Gsload       orBool SCHEDCONST ==K Gcall
                       orBool SCHEDCONST ==K Gselfdestruct orBool SCHEDCONST ==K Gextcodesize orBool SCHEDCONST ==K Gextcodecopy
                            )
  rule Gselfdestructnewaccount << TANGERINE_WHISTLE >> => true
  rule Gstaticcalldepth        << TANGERINE_WHISTLE >> => false
  rule SCHEDCONST              << TANGERINE_WHISTLE >> => SCHEDCONST << HOMESTEAD >>
      requires notBool      ( SCHEDCONST ==K Gselfdestructnewaccount orBool SCHEDCONST ==K Gstaticcalldepth )
  syntax Schedule  ::=
    "SPURIOUS_DRAGON" [klabel(SPURIOUS_DRAGON_EVM), smtlib(schedule_SPURIOUS_DRAGON), symbol]
  rule Gexpbyte    < SPURIOUS_DRAGON > => 50
  rule maxCodeSize < SPURIOUS_DRAGON > => 24576
  rule SCHEDCONST  < SPURIOUS_DRAGON > => SCHEDCONST < TANGERINE_WHISTLE > requires SCHEDCONST =/=K Gexpbyte andBool SCHEDCONST =/=K maxCodeSize
  rule Gemptyisnonexistent     << SPURIOUS_DRAGON >> => true
  rule Gzerovaluenewaccountgas << SPURIOUS_DRAGON >> => false
  rule SCHEDCONST              << SPURIOUS_DRAGON >> => SCHEDCONST << TANGERINE_WHISTLE >>
      requires notBool      ( SCHEDCONST ==K Gemptyisnonexistent orBool SCHEDCONST ==K Gzerovaluenewaccountgas )
  syntax Schedule  ::=
    "BYZANTIUM" [klabel(BYZANTIUM_EVM), smtlib(schedule_BYZANTIUM), symbol]
  rule Rb         < BYZANTIUM > => 3 *Int eth
  rule SCHEDCONST < BYZANTIUM > => SCHEDCONST < SPURIOUS_DRAGON >
      requires notBool ( SCHEDCONST ==K Rb )
  rule Ghasrevert     << BYZANTIUM >> => true
  rule Ghasreturndata << BYZANTIUM >> => true
  rule Ghasstaticcall << BYZANTIUM >> => true
  rule SCHEDFLAG      << BYZANTIUM >> => SCHEDFLAG << SPURIOUS_DRAGON >>
      requires notBool ( SCHEDFLAG ==K Ghasrevert orBool SCHEDFLAG ==K Ghasreturndata orBool SCHEDFLAG ==K Ghasstaticcall )
  syntax Schedule  ::=
    "CONSTANTINOPLE" [klabel(CONSTANTINOPLE_EVM), smtlib(schedule_CONSTANTINOPLE), symbol]
  rule Rb         < CONSTANTINOPLE > => 2 *Int eth
  rule SCHEDCONST < CONSTANTINOPLE > => SCHEDCONST < BYZANTIUM >
      requires notBool ( SCHEDCONST ==K Rb )
  rule Ghasshift       << CONSTANTINOPLE >> => true
  rule Ghasdirtysstore << CONSTANTINOPLE >> => true
  rule Ghascreate2     << CONSTANTINOPLE >> => true
  rule Ghasextcodehash << CONSTANTINOPLE >> => true
  rule SCHEDFLAG       << CONSTANTINOPLE >> => SCHEDFLAG << BYZANTIUM >>
      requires notBool ( SCHEDFLAG ==K Ghasshift orBool SCHEDFLAG ==K Ghasdirtysstore orBool SCHEDFLAG ==K Ghascreate2 orBool SCHEDFLAG ==K Ghasextcodehash )
  syntax Schedule  ::=
    "PETERSBURG" [klabel(PETERSBURG_EVM), smtlib(schedule_PETERSBURG), symbol]
  rule SCHEDCONST < PETERSBURG > => SCHEDCONST < CONSTANTINOPLE >
  rule Ghasdirtysstore << PETERSBURG >> => false
  rule SCHEDFLAG       << PETERSBURG >> => SCHEDFLAG << CONSTANTINOPLE >>
      requires notBool ( SCHEDFLAG ==K Ghasdirtysstore )
  syntax Schedule  ::=
    "ISTANBUL" [klabel(ISTANBUL_EVM), smtlib(schedule_ISTANBUL), symbol]
  rule Gecadd         < ISTANBUL > => 150
  rule Gecmul         < ISTANBUL > => 6000
  rule Gecpairconst   < ISTANBUL > => 45000
  rule Gecpaircoeff   < ISTANBUL > => 34000
  rule Gtxdatanonzero < ISTANBUL > => 16
  rule Gsload         < ISTANBUL > => 800
  rule Gbalance       < ISTANBUL > => 700
  rule SCHEDCONST     < ISTANBUL > => SCHEDCONST < PETERSBURG >
      requires notBool ( SCHEDCONST ==K Gecadd
                  orBool SCHEDCONST ==K Gecmul
                  orBool SCHEDCONST ==K Gecpairconst
                  orBool SCHEDCONST ==K Gecpaircoeff
                  orBool SCHEDCONST ==K Gtxdatanonzero
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gbalance
                       )
  rule Ghasselfbalance   << ISTANBUL >> => true
  rule Ghasdirtysstore   << ISTANBUL >> => true
  rule Ghassstorestipend << ISTANBUL >> => true
  rule Ghaschainid       << ISTANBUL >> => true
  rule SCHEDFLAG         << ISTANBUL >> => SCHEDFLAG << PETERSBURG >>
      requires notBool ( SCHEDFLAG ==K Ghasselfbalance
                  orBool SCHEDFLAG ==K Ghasdirtysstore
                  orBool SCHEDFLAG ==K Ghassstorestipend
                  orBool SCHEDFLAG ==K Ghaschainid
                       )
  syntax Schedule  ::=
    "BERLIN" [klabel(BERLIN_EVM), smtlib(schedule_BERLIN), symbol]
  rule Gcoldsload            < BERLIN > => 2100
  rule Gcoldaccountaccess    < BERLIN > => 2600
  rule Gwarmstorageread      < BERLIN > => 100
  rule Gsload                < BERLIN > => Gwarmstorageread < BERLIN >
  rule Gsstorereset          < BERLIN > => 5000 -Int Gcoldsload < BERLIN >
  rule Gquaddivisor          < BERLIN > => 3
  rule Gaccessliststoragekey < BERLIN > => 1900
  rule Gaccesslistaddress    < BERLIN > => 2400
  rule SCHEDCONST            < BERLIN > => SCHEDCONST < ISTANBUL >
      requires notBool ( SCHEDCONST ==K Gcoldsload
                  orBool SCHEDCONST ==K Gcoldaccountaccess
                  orBool SCHEDCONST ==K Gwarmstorageread
                  orBool SCHEDCONST ==K Gsload
                  orBool SCHEDCONST ==K Gsstorereset
                  orBool SCHEDCONST ==K Gquaddivisor
                  orBool SCHEDCONST ==K Gaccessliststoragekey
                  orBool SCHEDCONST ==K Gaccesslistaddress
                       )
  rule Ghasaccesslist << BERLIN >> => true
  rule SCHEDFLAG      << BERLIN >> => SCHEDFLAG << ISTANBUL >>
      requires notBool ( SCHEDFLAG ==K Ghasaccesslist )
  syntax Schedule  ::=
    "LONDON" [klabel(LONDON_EVM), smtlib(schedule_LONDON), symbol]
  rule Rselfdestruct < LONDON > => 0
  rule Rsstoreclear  < LONDON > => Gsstorereset < LONDON > +Int Gaccessliststoragekey < LONDON >
  rule Rmaxquotient  < LONDON > => 5
  rule SCHEDCONST    < LONDON > => SCHEDCONST < BERLIN >
      requires notBool ( SCHEDCONST ==K Rselfdestruct
                  orBool SCHEDCONST ==K Rsstoreclear
                  orBool SCHEDCONST ==K Rmaxquotient
                       )
  rule Ghasbasefee           << LONDON >> => true
  rule Ghasrejectedfirstbyte << LONDON >> => true
  rule SCHEDFLAG             << LONDON >> => SCHEDFLAG << BERLIN >>
      requires notBool ( SCHEDFLAG ==K Ghasbasefee
                  orBool SCHEDFLAG ==K Ghasrejectedfirstbyte
                       )
  syntax Schedule  ::=
    "MERGE" [klabel(MERGE_EVM), smtlib(schedule_MERGE), symbol]
  rule Rb         < MERGE > => 0
  rule SCHEDCONST < MERGE > => SCHEDCONST < LONDON >
      requires notBool SCHEDCONST ==K Rb
  rule Ghasprevrandao << MERGE >> => true
  rule SCHEDFLAG      << MERGE >> => SCHEDFLAG << LONDON >>
      requires notBool SCHEDFLAG ==K Ghasprevrandao
endmodule

module GAS-SYNTAX
  imports public INT-SYNTAX
  syntax Gas  ::=
    Int
  syntax Int  ::=
    "gas2Int" "(" Gas ")" [function, total]
  syntax Gas  ::=
    "minGas" "(" Gas "," Gas ")" [function, total]
  > left:
    Gas "*Gas" Gas [function, total]
  | Gas "/Gas" Gas [function]
  > left:
    Gas "+Gas" Gas [function, total]
  | Gas "-Gas" Gas [function, total]
  syntax Bool  ::=
    Gas "<Gas" Gas [function, total]
  | Gas "<=Gas" Gas [function, total]
endmodule

module GAS
  imports public INT
  imports public BOOL
  imports public GAS-SYNTAX
  imports public GAS-SIMPLIFICATION
  imports public GAS-FEES
  rule I1:Int *Gas I2:Int => I1 *Int I2
  rule I1:Int /Gas I2:Int => I1 /Int I2
  rule I1:Int +Gas I2:Int => I1 +Int I2
  rule I1:Int -Gas I2:Int => I1 -Int I2
  rule I1:Int  <Gas I2:Int => I1  <Int I2
  rule I1:Int <=Gas I2:Int => I1 <=Int I2
  rule minGas(I1:Int, I2:Int) => minInt(I1, I2)
  rule gas2Int(G:Int) => G
endmodule

module INFINITE-GAS
  imports public GAS
  syntax Gas  ::=
    "#gas" "(" Int ")" [klabel(infGas), smtlib(infGas), symbol]
  rule #gas(G) +Gas G'       => #gas(G +Int G')
  rule #gas(G) -Gas G'       => #gas(G -Int G')
  rule #gas(G) *Gas G'       => #gas(G *Int G')
  rule #gas(G) /Gas G'       => #gas(G /Int G')  requires G' =/=Int 0
  rule G  +Gas #gas(G') => #gas(G +Int G')
  rule G  -Gas #gas(G') => #gas(G -Int G')
  rule G  *Gas #gas(G') => #gas(G *Int G')
  rule G  /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0
  rule #gas(G) +Gas #gas(G') => #gas(G +Int G')
  rule #gas(G) -Gas #gas(G') => #gas(G -Int G')
  rule #gas(G) *Gas #gas(G') => #gas(G *Int G')
  rule #gas(G) /Gas #gas(G') => #gas(G /Int G')  requires G' =/=Int 0
  rule _:Int    <Gas #gas(_) => true
  rule #gas(_)  <Gas _       => false  [simplification]
  rule #gas(_) <=Gas _:Int   => false
  rule _       <=Gas #gas(_) => true   [simplification]
  rule minGas(#gas(G), #gas(G')) => #gas(minInt(G, G'))
  rule minGas(G:Int  , #gas(G')) => #gas(minInt(G, G'))
  rule minGas(#gas(G), G':Int)   => #gas(minInt(G, G'))
  rule gas2Int(#gas(G)) => G
  rule #allBut64th(#gas(G)) => #gas(#allBut64th(G))
  rule Cgascap(SCHED, #gas(GCAP), #gas(GAVAIL), GEXTRA) => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA))  [simplification]
  rule Cgascap(SCHED, #gas(GCAP), GAVAIL:Int, GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA))  [simplification]
  rule Cgascap(SCHED, GCAP:Int, #gas(GAVAIL), GEXTRA)   => #gas(Cgascap(SCHED, GCAP, GAVAIL, GEXTRA))  [simplification]
  rule #if B #then #gas(G) #else #gas(G') #fi => #gas(#if B #then G #else G' #fi)  [simplification]
endmodule

module GAS-FEES
  imports public GAS-SYNTAX
  imports public SCHEDULE
  syntax Gas  ::=
    "Cgascap" "(" Schedule "," Gas "," Gas "," Int ")" [function, klabel(Cgascap), smtlib(gas_Cgascap_Gas), total]
  syntax Int  ::=
    "Cgascap" "(" Schedule "," Int "," Int "," Int ")" [function, klabel(Cgascap), smtlib(gas_Cgascap_Int), total]
  | "Csstore" "(" Schedule "," Int "," Int "," Int ")" [function, klabel(Csstore), smtlib(gas_Csstore), total]
  | "Rsstore" "(" Schedule "," Int "," Int "," Int ")" [function, klabel(Rsstore), smtlib(gas_Rsstore), total]
  | "Cextra" "(" Schedule "," Bool "," Int "," Bool ")" [function, klabel(Cextra), smtlib(gas_Cextra), total]
  | "Cnew" "(" Schedule "," Bool "," Int ")" [function, klabel(Cnew), smtlib(gas_Cnew), total]
  | "Cxfer" "(" Schedule "," Int ")" [function, klabel(Cxfer), smtlib(gas_Cxfer), total]
  | "Cmem" "(" Schedule "," Int ")" [function, klabel(Cmem), memo, smtlib(gas_Cmem), total]
  | "Caddraccess" "(" Schedule "," Bool ")" [function, klabel(Caddraccess), smtlib(gas_Caddraccess), total]
  | "Cstorageaccess" "(" Schedule "," Bool ")" [function, klabel(Cstorageaccess), smtlib(gas_Cstorageaccess), total]
  | "Csload" "(" Schedule "," Bool ")" [function, klabel(Csload), smtlib(gas_Csload), total]
  | "Cextcodesize" "(" Schedule ")" [function, klabel(Cextcodesize), smtlib(gas_Cextcodesize), total]
  | "Cextcodecopy" "(" Schedule "," Int ")" [function, klabel(Cextcodecopy), smtlib(gas_Cextcodecopy), total]
  | "Cextcodehash" "(" Schedule ")" [function, klabel(Cextcodehash), smtlib(gas_Cextcodehash), total]
  | "Cbalance" "(" Schedule ")" [function, klabel(Cbalance), smtlib(gas_Cbalance), total]
  | "Cmodexp" "(" Schedule "," Bytes "," Int "," Int "," Int ")" [function, klabel(Cmodexp), smtlib(gas_Cmodexp), total]
  rule [Cgascap]: Cgascap(SCHED, GCAP:Int, GAVAIL:Int, GEXTRA)
      => #if GAVAIL <Int GEXTRA orBool Gstaticcalldepth << SCHED >> #then GCAP #else minInt(#allBut64th(GAVAIL -Int GEXTRA), GCAP) #fi
      requires 0 <=Int GCAP
       [concrete]
  rule Cgascap(_, GCAP, _, _) => 0 requires GCAP <Gas 0  [concrete]
  rule [Csstore.new]: Csstore(SCHED, NEW, CURR, ORIG)
      => #if CURR ==Int NEW orBool ORIG =/=Int CURR #then Gsload < SCHED > #else #if ORIG ==Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi #fi
      requires Ghasdirtysstore << SCHED >>
       [concrete]
  rule [Csstore.old]: Csstore(SCHED, NEW, CURR, _ORIG)
      => #if CURR ==Int 0 andBool NEW =/=Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi
      requires notBool Ghasdirtysstore << SCHED >>
       [concrete]
  rule [Rsstore.new]: Rsstore(SCHED, NEW, CURR, ORIG)
      => #if CURR =/=Int NEW andBool ORIG ==Int CURR andBool NEW ==Int 0 #then
             Rsstoreclear < SCHED >
         #else
             #if CURR =/=Int NEW andBool ORIG =/=Int CURR andBool ORIG =/=Int 0 #then
                 #if CURR ==Int 0 #then 0 -Int Rsstoreclear < SCHED > #else #if NEW ==Int 0 #then Rsstoreclear < SCHED > #else 0 #fi #fi
             #else
                 0
             #fi +Int
             #if CURR =/=Int NEW andBool ORIG ==Int NEW #then
                 #if ORIG ==Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi -Int Gsload < SCHED >
             #else
                 0
             #fi
         #fi
      requires Ghasdirtysstore << SCHED >>
       [concrete]
  rule [Rsstore.old]: Rsstore(SCHED, NEW, CURR, _ORIG)
      => #if CURR =/=Int 0 andBool NEW ==Int 0 #then Rsstoreclear < SCHED > #else 0 #fi
      requires notBool Ghasdirtysstore << SCHED >>
       [concrete]
  rule [Cextra.new]: Cextra(SCHED, ISEMPTY, VALUE, ISWARM)  => Caddraccess(SCHED, ISWARM) +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE) requires         Ghasaccesslist << SCHED >>
  rule [Cextra.old]: Cextra(SCHED, ISEMPTY, VALUE, _ISWARM) => Gcall < SCHED > +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE)            requires notBool Ghasaccesslist << SCHED >>
  rule [Cnew]: Cnew(SCHED, ISEMPTY:Bool, VALUE)
      => #if ISEMPTY andBool (VALUE =/=Int 0 orBool Gzerovaluenewaccountgas << SCHED >>) #then Gnewaccount < SCHED > #else 0 #fi
  rule [Cxfer.none]: Cxfer(_SCHED, 0) => 0
  rule [Cxfer.some]: Cxfer( SCHED, N) => Gcallvalue < SCHED > requires N =/=Int 0
  rule [Cmem]: Cmem(SCHED, N) => (N *Int Gmemory < SCHED >) +Int ((N *Int N) /Int Gquadcoeff < SCHED >)  [concrete]
  rule [Caddraccess]: Caddraccess(SCHED, ISWARM)    => #if ISWARM #then Gwarmstorageread < SCHED > #else Gcoldaccountaccess < SCHED > #fi
  rule [Cstorageaccess]: Cstorageaccess(SCHED, ISWARM) => #if ISWARM #then Gwarmstorageread < SCHED > #else Gcoldsload < SCHED >         #fi
  rule [Csload.new]: Csload(SCHED, ISWARM)  => Cstorageaccess(SCHED, ISWARM) requires         Ghasaccesslist << SCHED >>
  rule [Csload.old]: Csload(SCHED, _ISWARM) => Gsload < SCHED >              requires notBool Ghasaccesslist << SCHED >>
  rule [Cextcodesize.new]: Cextcodesize(SCHED) => 0                      requires         Ghasaccesslist << SCHED >>
  rule [Cextcodesize.old]: Cextcodesize(SCHED) => Gextcodesize < SCHED > requires notBool Ghasaccesslist << SCHED >>
  rule [Cextcodehash.new]: Cextcodehash(SCHED) => 0                  requires         Ghasaccesslist << SCHED >>
  rule [Cextcodehash.old]: Cextcodehash(SCHED) => Gbalance < SCHED > requires notBool Ghasaccesslist << SCHED >>
  rule [Cbalance.new]: Cbalance(SCHED) => 0                  requires         Ghasaccesslist << SCHED >>
  rule [Cbalance.old]: Cbalance(SCHED) => Gbalance < SCHED > requires notBool Ghasaccesslist << SCHED >>
  rule [Cextcodecopy.new]: Cextcodecopy(SCHED, WIDTH) => Gcopy < SCHED > *Int (WIDTH up/Int 32)                               requires         Ghasaccesslist << SCHED >>  [concrete]
  rule [Cextcodecopy.old]: Cextcodecopy(SCHED, WIDTH) => Gextcodecopy < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) requires notBool Ghasaccesslist << SCHED >>  [concrete]
  rule [Cmodexp.old]: Cmodexp(SCHED, DATA, BASELEN, EXPLEN, MODLEN) => #multComplexity(maxInt(BASELEN, MODLEN)) *Int maxInt(#adjustedExpLength(BASELEN, EXPLEN, DATA), 1) /Int Gquaddivisor < SCHED >
      requires notBool Ghasaccesslist << SCHED >>
       [concrete]
  rule [Cmodexp.new]: Cmodexp(SCHED, DATA, BASELEN, EXPLEN, MODLEN) => maxInt(200, (#newMultComplexity(maxInt(BASELEN, MODLEN)) *Int maxInt(#adjustedExpLength(BASELEN, EXPLEN, DATA), 1)) /Int Gquaddivisor < SCHED > )
      requires Ghasaccesslist << SCHED >>
       [concrete]
  syntax Bool  ::=
    "#accountEmpty" "(" AccountCode "," Int "," Int ")" [function, klabel(accountEmpty), symbol, total]
  rule #accountEmpty(CODE, NONCE, BAL) => CODE ==K .Bytes andBool NONCE ==Int 0 andBool BAL ==Int 0
  syntax Gas  ::=
    "#allBut64th" "(" Gas ")" [function, klabel(#allBut64th), smtlib(gas_allBut64th_Gas), total]
  syntax Int  ::=
    "#allBut64th" "(" Int ")" [function, klabel(#allBut64th), smtlib(gas_allBut64th_Int), total]
  rule [allBut64th.pos]: #allBut64th(N) => N -Int (N /Int 64) requires 0 <=Int N
  rule [allBut64th.neg]: #allBut64th(N) => 0                  requires N  <Int 0
  syntax Int  ::=
    "G0" "(" Schedule "," Bytes "," Bool ")" [function, klabel(G0)]
  | "G0" "(" Schedule "," Bytes "," Int "," Int "," Int ")" [function, klabel(G0data)]
  | "G0" "(" Schedule "," Bool ")" [function, klabel(G0base)]
  rule G0(SCHED, WS, B) => G0(SCHED, WS, 0, lengthBytes(WS), 0) +Int G0(SCHED, B)
  rule G0(SCHED, true)  => Gtxcreate    < SCHED >
  rule G0(SCHED, false) => Gtransaction < SCHED >
  rule G0(    _,  _, I, I, R) => R
  rule G0(SCHED, WS, I, J, R) => G0(SCHED, WS, I +Int 1, J, R +Int #if WS[I] ==Int 0 #then Gtxdatazero < SCHED > #else Gtxdatanonzero < SCHED > #fi)  [owise]
  syntax Gas  ::=
    "G*" "(" Gas "," Int "," Int "," Schedule ")" [function]
  rule G*(GAVAIL, GLIMIT, REFUND, SCHED) => GAVAIL +Gas minGas((GLIMIT -Gas GAVAIL) /Gas Rmaxquotient < SCHED >, REFUND)
  syntax Int  ::=
    "#multComplexity" "(" Int ")" [function, klabel(#multComplexity)]
  | "#newMultComplexity" "(" Int ")" [function, klabel(#newMultComplexity)]
  rule #multComplexity(X) => X *Int X                                     requires X <=Int 64
  rule #multComplexity(X) => X *Int X /Int 4 +Int 96 *Int X -Int 3072     requires X >Int 64 andBool X <=Int 1024
  rule #multComplexity(X) => X *Int X /Int 16 +Int 480 *Int X -Int 199680 requires X >Int 1024
  rule #newMultComplexity(X) => (X up/Int 8) ^Int 2
  syntax Int  ::=
    "#adjustedExpLength" "(" Int "," Int "," Bytes ")" [function, klabel(#adjustedExpLength)]
  | "#adjustedExpLength" "(" Int ")" [function, klabel(#adjustedExpLengthAux)]
  rule #adjustedExpLength(BASELEN, EXPLEN, DATA) => #if EXPLEN <=Int 32 #then 0 #else 8 *Int (EXPLEN -Int 32) #fi +Int #adjustedExpLength(#asInteger(#range(DATA, 96 +Int BASELEN, minInt(EXPLEN, 32))))
  rule #adjustedExpLength(0) => 0
  rule #adjustedExpLength(1) => 0
  rule #adjustedExpLength(N) => 1 +Int #adjustedExpLength(N /Int 2) requires N >Int 1
endmodule

module GAS-SIMPLIFICATION [symbolic]
  imports public GAS-SYNTAX
  imports public INT
  imports public BOOL
  rule A <Gas B => false requires B <=Gas A  [simplification]
endmodule

module EVM
  imports public STRING
  imports public EVM-DATA
  imports public NETWORK
  imports public GAS
  configuration <kevm>
        <k> $PGM:EthereumSimulation </k>
        <exit-code exit=""> 1 </exit-code>
        <mode> $MODE:Mode </mode>
        <schedule> $SCHEDULE:Schedule </schedule>

        <ethereum>

          // EVM Specific
          // ============

          <evm>

            // Mutable during a single transaction
            // -----------------------------------

            <output>          .Bytes      </output>           // H_RETURN
            <statusCode>      .StatusCode </statusCode>
            <callStack>       .List       </callStack>
            <interimStates>   .List       </interimStates>
            <touchedAccounts> .Set        </touchedAccounts>

            <callState>
              <program>   .Bytes </program>
              <jumpDests> .Set   </jumpDests>

              // I_*
              <id>        .Account </id>                    // I_a
              <caller>    .Account </caller>                // I_s
              <callData>  .Bytes   </callData>              // I_d
              <callValue> 0        </callValue>             // I_v

              // \mu_*
              <wordStack>   .WordStack </wordStack>           // \mu_s
              <localMem>    .Bytes     </localMem>            // \mu_m
              <pc>          0          </pc>                  // \mu_pc
              <gas>         0:Gas      </gas>                 // \mau_g
              <memoryUsed>  0          </memoryUsed>          // \mu_i
              <callGas>     0:Gas      </callGas>

              <static>    false </static>
              <callDepth> 0     </callDepth>
            </callState>

            // A_* (execution substate)
            <substate>
              <selfDestruct>     .Set  </selfDestruct>            // A_s
              <log>              .List </log>                     // A_l
              <refund>           0     </refund>                  // A_r
              <accessedAccounts> .Set  </accessedAccounts>
              <accessedStorage>  .Map  </accessedStorage>
            </substate>

            // Immutable during a single transaction
            // -------------------------------------

            <gasPrice> 0        </gasPrice>                   // I_p
            <origin>   .Account </origin>                     // I_o

            // I_H* (block information)
            <blockhashes> .List </blockhashes>
            <block>
              <previousHash>     0      </previousHash>     // I_Hp
              <ommersHash>       0      </ommersHash>       // I_Ho
              <coinbase>         0      </coinbase>         // I_Hc
              <stateRoot>        0      </stateRoot>        // I_Hr
              <transactionsRoot> 0      </transactionsRoot> // I_Ht
              <receiptsRoot>     0      </receiptsRoot>     // I_He
              <logsBloom>        .Bytes </logsBloom>        // I_Hb
              <difficulty>       0      </difficulty>       // I_Hd
              <number>           0      </number>           // I_Hi
              <gasLimit>         0      </gasLimit>         // I_Hl
              <gasUsed>          0:Gas  </gasUsed>          // I_Hg
              <timestamp>        0      </timestamp>        // I_Hs
              <extraData>        .Bytes </extraData>        // I_Hx
              <mixHash>          0      </mixHash>          // I_Hm
              <blockNonce>       0      </blockNonce>       // I_Hn
              <baseFee>          0      </baseFee>

              <ommerBlockHeaders> [ .JSONs ] </ommerBlockHeaders>
            </block>

          </evm>

          // Ethereum Network
          // ================

          <network>

            // Chain identifier
            // ----------------
            <chainID> $CHAINID:Int </chainID>

            // Accounts Record
            // ---------------

            <accounts>
              <account multiplicity="*" type="Map">
                <acctID>      0                  </acctID>
                <balance>     0                  </balance>
                <code>        .Bytes:AccountCode </code>
                <storage>     .Map               </storage>
                <origStorage> .Map               </origStorage>
                <nonce>       0                  </nonce>
              </account>
            </accounts>

            // Transactions Record
            // -------------------

            <txOrder>   .List </txOrder>
            <txPending> .List </txPending>

            <messages>
              <message multiplicity="*" type="Map">
                <msgID>         0          </msgID>
                <txNonce>       0          </txNonce>       // T_n
                <txGasPrice>    0          </txGasPrice>    // T_p
                <txGasLimit>    0          </txGasLimit>    // T_g
                <to>            .Account   </to>            // T_t
                <value>         0          </value>         // T_v
                <sigV>          0          </sigV>          // T_w
                <sigR>          .Bytes     </sigR>          // T_r
                <sigS>          .Bytes     </sigS>          // T_s
                <data>          .Bytes     </data>          // T_i/T_e
                <txAccess>      [ .JSONs ] </txAccess>      // T_a
                <txChainID>     0          </txChainID>     // T_c
                <txPriorityFee> 0          </txPriorityFee>
                <txMaxFee>      0          </txMaxFee>
                <txType>        .TxType    </txType>
              </message>
            </messages>

          </network>

        </ethereum>
      </kevm>
  syntax EthereumSimulation
  syntax Mode  ::=
    "NORMAL" [klabel(NORMAL), symbol]
  | "VMTESTS" [klabel(VMTESTS), symbol]
  syntax InternalOp  ::=
    "#pushCallStack"
  rule <k> #pushCallStack => . ... </k>
         <callStack> STACK => ListItem(CALLSTATE) STACK </callStack>
         <callState> CALLSTATE </callState>
  syntax InternalOp  ::=
    "#popCallStack"
  rule <k> #popCallStack => . ... </k>
         <callStack> ListItem(CALLSTATE) REST => REST </callStack>
         <callState> _ => CALLSTATE </callState>
  syntax InternalOp  ::=
    "#dropCallStack"
  rule <k> #dropCallStack => . ... </k>
         <callStack> ListItem(_) REST => REST </callStack>
  syntax Accounts  ::=
    "{" AccountsCellFragment "|" SubstateCellFragment "}"
  syntax InternalOp  ::=
    "#pushWorldState"
  rule <k> #pushWorldState => .K ... </k>
         <interimStates> STATES => ListItem({ ACCTDATA | SUBSTATE }) STATES </interimStates>
         <accounts>       ACCTDATA </accounts>
         <substate>       SUBSTATE </substate>
  syntax InternalOp  ::=
    "#popWorldState"
  rule <k> #popWorldState => .K ... </k>
         <interimStates> ListItem({ ACCTDATA | SUBSTATE }) REST => REST </interimStates>
         <accounts>       _ => ACCTDATA </accounts>
         <substate>       _ => SUBSTATE </substate>
  syntax InternalOp  ::=
    "#dropWorldState"
  rule <k> #dropWorldState => . ... </k> <interimStates> ListItem(_) REST => REST </interimStates>
  syntax KItem  ::=
    "#halt"
  | "#end" StatusCode
  rule [end]: <k> #end SC => #halt ... </k>
         <statusCode> _ => SC </statusCode>
  rule <k> #halt ~> (_:Int    => .) ... </k>
  rule <k> #halt ~> (_:OpCode => .) ... </k>
  syntax MaybeOpCode  ::=
    ".NoOpCode"
  | OpCode
  syntax MaybeOpCode  ::=
    "#lookupOpCode" "(" Bytes "," Int "," Schedule ")" [function, total]
  rule #lookupOpCode(BA, I, SCHED) => #dasmOpCode(BA[I], SCHED) requires 0 <=Int I andBool I <Int lengthBytes(BA)
  rule #lookupOpCode(_, _, _)  => .NoOpCode  [owise]
  syntax KItem  ::=
    "#execute"
  rule [halt]: <k> #halt ~> (#execute => .) ... </k>
  rule [step]: <k> (. => #next [ #lookupOpCode(PGM, PCOUNT, SCHED) ]) ~> #execute ... </k>
         <program> PGM </program>
         <pc> PCOUNT </pc>
         <schedule> SCHED </schedule>
  syntax InternalOp  ::=
    "#next" "[" MaybeOpCode "]"
  rule <k> #next [ .NoOpCode ] => #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>
  rule <k> #next [ OP:OpCode ]
          => #addr [ OP ]
          ~> #exec [ OP ]
          ~> #pc   [ OP ]
         ...
         </k>
         <wordStack> WS </wordStack>
         <static> STATIC:Bool </static>
      requires notBool ( #stackUnderflow(WS, OP) orBool #stackOverflow(WS, OP) )
       andBool notBool ( STATIC andBool #changesState(OP, WS) )
  rule <k> #next [ OP ] => #end EVMC_STACK_UNDERFLOW ... </k>
         <wordStack> WS </wordStack>
      requires #stackUnderflow(WS, OP)
  rule <k> #next [ OP ] => #end EVMC_STACK_OVERFLOW ... </k>
         <wordStack> WS </wordStack>
      requires #stackOverflow(WS, OP)
  rule <k> #next [ OP ] => #end EVMC_STATIC_MODE_VIOLATION ... </k>
         <wordStack> WS </wordStack>
         <static> STATIC:Bool </static>
      requires STATIC andBool #changesState(OP, WS)
       andBool notBool ( #stackUnderflow(WS, OP) orBool #stackOverflow(WS, OP) )
  syntax Bool  ::=
    "#stackUnderflow" "(" WordStack "," OpCode ")" [klabel(#stackUnderflow), macro]
  | "#stackOverflow" "(" WordStack "," OpCode ")" [klabel(#stackOverflow), macro]
  rule #stackUnderflow(WS, OP:OpCode) => #sizeWordStack(WS) <Int #stackNeeded(OP)
  rule #stackOverflow (WS, OP) => #sizeWordStack(WS) +Int #stackDelta(OP) >Int 1024
  syntax Int  ::=
    "#stackNeeded" "(" OpCode ")" [function, klabel(#stackNeeded)]
  rule #stackNeeded(PUSH(_))          => 0
  rule #stackNeeded(_IOP:InvalidOp)   => 0
  rule #stackNeeded(_NOP:NullStackOp) => 0
  rule #stackNeeded(_UOP:UnStackOp)   => 1
  rule #stackNeeded(BOP:BinStackOp)   => 2 requires notBool isLogOp(BOP)
  rule #stackNeeded(_TOP:TernStackOp) => 3
  rule #stackNeeded(_QOP:QuadStackOp) => 4
  rule #stackNeeded(DUP(N))           => N
  rule #stackNeeded(SWAP(N))          => N +Int 1
  rule #stackNeeded(LOG(N))           => N +Int 2
  rule #stackNeeded(_CSOP:CallSixOp)  => 6
  rule #stackNeeded(COP:CallOp)       => 7 requires notBool isCallSixOp(COP)
  syntax Int  ::=
    "#stackAdded" "(" OpCode ")" [function, klabel(#stackAdded)]
  rule #stackAdded(CALLDATACOPY)   => 0
  rule #stackAdded(RETURNDATACOPY) => 0
  rule #stackAdded(CODECOPY)       => 0
  rule #stackAdded(EXTCODECOPY)    => 0
  rule #stackAdded(POP)            => 0
  rule #stackAdded(MSTORE)         => 0
  rule #stackAdded(MSTORE8)        => 0
  rule #stackAdded(SSTORE)         => 0
  rule #stackAdded(JUMP)           => 0
  rule #stackAdded(JUMPI)          => 0
  rule #stackAdded(JUMPDEST)       => 0
  rule #stackAdded(STOP)           => 0
  rule #stackAdded(RETURN)         => 0
  rule #stackAdded(REVERT)         => 0
  rule #stackAdded(SELFDESTRUCT)   => 0
  rule #stackAdded(PUSH(_))        => 1
  rule #stackAdded(LOG(_))         => 0
  rule #stackAdded(SWAP(N))        => N +Int 1
  rule #stackAdded(DUP(N))         => N +Int 1
  rule #stackAdded(_IOP:InvalidOp) => 0
  rule #stackAdded(_OP)            => 1  [owise]
  syntax Int  ::=
    "#stackDelta" "(" OpCode ")" [function, klabel(#stackDelta)]
  rule #stackDelta(OP) => #stackAdded(OP) -Int #stackNeeded(OP)
  syntax Bool  ::=
    "#changesState" "(" OpCode "," WordStack ")" [function, klabel(#changesState)]
  rule #changesState(CALL         , _ : _ : VALUE : _) => true  requires VALUE =/=Int 0
  rule #changesState(LOG(_)       , _)                 => true
  rule #changesState(SSTORE       , _)                 => true
  rule #changesState(CREATE       , _)                 => true
  rule #changesState(CREATE2      , _)                 => true
  rule #changesState(SELFDESTRUCT , _)                 => true
  rule #changesState(_            , _)                 => false  [owise]
  syntax InternalOp  ::=
    "#exec" "[" OpCode "]"
  rule <k> #exec [ IOP:InvalidOp ] => IOP ... </k>
  rule <k> #exec [ OP ] => #gas [ OP , OP ] ~> OP ... </k> requires isNullStackOp(OP) orBool isPushOp(OP)
  syntax KItem  ::=
    OpCode
  syntax OpCode  ::=
    NullStackOp
  | UnStackOp
  | BinStackOp
  | TernStackOp
  | QuadStackOp
  | InvalidOp
  | StackOp
  | InternalOp
  | CallOp
  | CallSixOp
  | PushOp
  syntax InternalOp  ::=
    UnStackOp Int
  | BinStackOp Int Int
  | TernStackOp Int Int Int
  | QuadStackOp Int Int Int Int
  rule <k> #exec [ UOP:UnStackOp   ] => #gas [ UOP , UOP W0          ] ~> UOP W0          ... </k> <wordStack> W0 : WS                => WS </wordStack>
  rule <k> #exec [ BOP:BinStackOp  ] => #gas [ BOP , BOP W0 W1       ] ~> BOP W0 W1       ... </k> <wordStack> W0 : W1 : WS           => WS </wordStack>
  rule <k> #exec [ TOP:TernStackOp ] => #gas [ TOP , TOP W0 W1 W2    ] ~> TOP W0 W1 W2    ... </k> <wordStack> W0 : W1 : W2 : WS      => WS </wordStack>
  rule <k> #exec [ QOP:QuadStackOp ] => #gas [ QOP , QOP W0 W1 W2 W3 ] ~> QOP W0 W1 W2 W3 ... </k> <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>
  syntax InternalOp  ::=
    StackOp WordStack
  rule <k> #exec [ SO:StackOp ] => #gas [ SO , SO WS ] ~> SO WS ... </k> <wordStack> WS </wordStack>
  syntax InternalOp  ::=
    CallSixOp Int Int Int Int Int Int
  | CallOp Int Int Int Int Int Int Int
  rule <k> #exec [ CSO:CallSixOp ] => #gas [ CSO , CSO W0 W1    W2 W3 W4 W5 ] ~> CSO W0 W1    W2 W3 W4 W5 ... </k> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
  rule <k> #exec [ CO:CallOp     ] => #gas [ CO  , CO  W0 W1 W2 W3 W4 W5 W6 ] ~> CO  W0 W1 W2 W3 W4 W5 W6 ... </k> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
  syntax InternalOp  ::=
    "#addr" "[" OpCode "]"
  rule <k> #addr [ OP:OpCode ] => . ... </k>
         <wordStack> (W0 => #addr(W0)) : _WS </wordStack>
      requires isAddr1Op(OP)
  rule <k> #addr [ OP:OpCode ] => . ... </k>
         <wordStack> _W0 : (W1 => #addr(W1)) : _WS </wordStack>
      requires isAddr2Op(OP)
  rule <k> #addr [ OP:OpCode ] => . ... </k>
      requires notBool ( isAddr1Op(OP) orBool isAddr2Op(OP) )
  syntax Bool  ::=
    "isAddr1Op" "(" OpCode ")" [function, klabel(isAddr1Op), total]
  | "isAddr2Op" "(" OpCode ")" [function, klabel(isAddr2Op), total]
  rule isAddr1Op(BALANCE)      => true
  rule isAddr1Op(SELFDESTRUCT) => true
  rule isAddr1Op(EXTCODEHASH)  => true
  rule isAddr1Op(EXTCODESIZE)  => true
  rule isAddr1Op(EXTCODECOPY)  => true
  rule isAddr1Op(_)            => false  [owise]
  rule isAddr2Op(_:CallOp)    => true
  rule isAddr2Op(_:CallSixOp) => true
  rule isAddr2Op(_)           => false  [owise]
  syntax InternalOp  ::=
    "#pc" "[" OpCode "]"
  rule <k> #pc [ OP ] => . ... </k>
         <pc> PCOUNT => PCOUNT +Int #widthOp(OP) </pc>
  syntax Int  ::=
    "#widthOp" "(" OpCode ")" [function, klabel(#widthOp), total]
  rule #widthOp(PUSH(N)) => 1 +Int N
  rule #widthOp(_)       => 1         [owise]
  syntax InternalOp  ::=
    "#finalizeStorage" "(" List ")" [klabel(#finalizeStorage)]
  rule <k> #finalizeStorage(ListItem(ACCT) REST => REST) ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           <origStorage> _ => STORAGE </origStorage>
           ...
         </account>
  rule <k> #finalizeStorage(.List) => . ... </k>
  rule <k> (.K => #newAccount ACCT) ~> #finalizeStorage(ListItem(ACCT) _ACCTS) ... </k>  [owise]
  syntax InternalOp  ::=
    "#finalizeTx" "(" Bool ")" [klabel(#finalizeTx)]
  | "#deleteAccounts" "(" List ")" [klabel(#deleteAccounts)]
  rule <k> #finalizeTx(true) => #finalizeStorage(Set2List(SetItem(MINER) |Set ACCTS)) ... </k>
         <selfDestruct> .Set </selfDestruct>
         <coinbase> MINER </coinbase>
         <touchedAccounts> ACCTS </touchedAccounts>
         <accessedAccounts> _ => .Set </accessedAccounts>
         <accessedStorage> _ => .Map </accessedStorage>
  rule <k> #finalizeTx(false) ... </k>
         <schedule> SCHED </schedule>
         <gas> GAVAIL => G*(GAVAIL, GLIMIT, REFUND, SCHED) </gas>
         <refund> REFUND => 0 </refund>
         <txPending> ListItem(MSGID:Int) ... </txPending>
         <message>
            <msgID> MSGID </msgID>
            <txGasLimit> GLIMIT </txGasLimit>
            ...
         </message>
      requires REFUND =/=Int 0
  rule <k> #finalizeTx(false => true) ... </k>
         <baseFee> BFEE </baseFee>
         <origin> ORG </origin>
         <coinbase> MINER </coinbase>
         <gas> GAVAIL </gas>
         <gasUsed> GUSED => GUSED +Gas GLIMIT -Gas GAVAIL </gasUsed>
         <gasPrice> GPRICE </gasPrice>
         <refund> 0 </refund>
         <account>
           <acctID> ORG </acctID>
           <balance> ORGBAL => ORGBAL +Int GAVAIL *Int GPRICE </balance>
           ...
         </account>
         <account>
           <acctID> MINER </acctID>
           <balance> MINBAL => MINBAL +Int (GLIMIT -Int GAVAIL) *Int (GPRICE -Int BFEE) </balance>
           ...
         </account>
         <txPending> ListItem(TXID:Int) REST => REST </txPending>
         <message>
           <msgID> TXID </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           ...
         </message>
      requires ORG =/=Int MINER
  rule <k> #finalizeTx(false => true) ... </k>
         <baseFee> BFEE </baseFee>
         <origin> ACCT </origin>
         <coinbase> ACCT </coinbase>
         <gas> GAVAIL </gas>
         <gasUsed> GUSED => GUSED +Gas GLIMIT -Gas GAVAIL </gasUsed>
         <gasPrice> GPRICE </gasPrice>
         <refund> 0 </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL => BAL +Int GLIMIT *Int (GPRICE -Int BFEE) </balance>
           ...
         </account>
         <txPending> ListItem(MsgId:Int) REST => REST </txPending>
         <message>
           <msgID> MsgId </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           ...
         </message>
  rule <k> (. => #deleteAccounts(Set2List(ACCTS))) ~> #finalizeTx(true) ... </k>
         <selfDestruct> ACCTS => .Set </selfDestruct>
      requires size(ACCTS) >Int 0
  rule <k> (. => #newAccount MINER) ~> #finalizeTx(_) ... </k>
         <coinbase> MINER </coinbase>  [owise]
  rule <k> #deleteAccounts(ListItem(ACCT) ACCTS) => #deleteAccounts(ACCTS) ... </k>
         <accounts>
           ( <account>
               <acctID> ACCT </acctID>
               ...
             </account>
          => .Bag
           )
           ...
         </accounts>
  rule <k> #deleteAccounts(.List) => . ... </k>
  syntax EthereumCommand  ::=
    "#startBlock"
  rule <k> #startBlock => . ... </k>
         <gasUsed> _ => 0 </gasUsed>
         <log> _ => .List </log>
         <logsBloom> _ => #padToWidth(256, .Bytes) </logsBloom>
  syntax EthereumCommand  ::=
    "#finalizeBlock"
  | "#rewardOmmers" "(" JSONs ")" [klabel(#rewardOmmers)]
  rule <k> #finalizeBlock => #rewardOmmers(OMMERS) ... </k>
         <schedule> SCHED </schedule>
         <ommerBlockHeaders> [ OMMERS ] </ommerBlockHeaders>
         <coinbase> MINER </coinbase>
         <account>
           <acctID> MINER </acctID>
           <balance> MINBAL => MINBAL +Int Rb < SCHED > </balance>
           ...
         </account>
         <log> LOGS </log>
         <logsBloom> _ => #bloomFilter(LOGS) </logsBloom>
  rule <k> (.K => #newAccount MINER) ~> #finalizeBlock ... </k>
         <coinbase> MINER </coinbase>  [owise]
  rule <k> #rewardOmmers(.JSONs) => . ... </k>
  rule <k> #rewardOmmers([ _ , _ , OMMER , _ , _ , _ , _ , _ , OMMNUM , _ ] , REST) => #rewardOmmers(REST) ... </k>
         <schedule> SCHED </schedule>
         <coinbase> MINER </coinbase>
         <number> CURNUM </number>
         <account>
           <acctID> MINER </acctID>
           <balance> MINBAL => MINBAL +Int Rb < SCHED > /Int 32 </balance>
          ...
         </account>
         <account>
           <acctID> OMMER </acctID>
           <balance> OMMBAL => OMMBAL +Int Rb < SCHED > +Int (OMMNUM -Int CURNUM) *Int (Rb < SCHED > /Int 8) </balance>
          ...
         </account>
  syntax Bytes  ::=
    "#bloomFilter" "(" List ")" [function, klabel(#bloomFilter)]
  | "#bloomFilter" "(" List "," Int ")" [function, klabel(#bloomFilterAux)]
  rule #bloomFilter(L) => #bloomFilter(L, 0)
  rule #bloomFilter(.List, B) => #padToWidth(256, #asByteStack(B))
  rule #bloomFilter(ListItem({ ACCT | TOPICS | _ }) L, B) => #bloomFilter(ListItem(#padToWidth(20, #asByteStack(ACCT))) listAsBytes(TOPICS) L, B)
  syntax List  ::=
    "listAsBytes" "(" List ")" [function, klabel(listAsBytes)]
  rule listAsBytes(.List) => .List
  rule listAsBytes(ListItem(TOPIC) L) => ListItem(#padToWidth(32, #asByteStack(TOPIC))) listAsBytes(L)
  rule #bloomFilter(ListItem(WS:Bytes) L, B) => #bloomFilter(L, B |Int M3:2048(WS))
  syntax Int  ::=
    "M3:2048" "(" Bytes ")" [function]
  rule M3:2048(WS) => setBloomFilterBits(#parseByteStack(Keccak256(#unparseByteStack(WS))))
  syntax Int  ::=
    "setBloomFilterBits" "(" Bytes ")" [function, klabel(setBloomFilterBits)]
  rule setBloomFilterBits(HASH) => (1 <<Int getBloomFilterBit(HASH, 0)) |Int (1 <<Int getBloomFilterBit(HASH, 2)) |Int (1 <<Int getBloomFilterBit(HASH, 4))
  syntax Int  ::=
    "getBloomFilterBit" "(" Bytes "," Int ")" [function, klabel(getBloomFilterBit)]
  rule getBloomFilterBit(X, I) => #asInteger(#range(X, I, 2)) %Int 2048
  syntax InternalOp  ::=
    "#push"
  | "#setStack" WordStack
  rule <k> W0:Int ~> #push => . ... </k> <wordStack> WS => W0 : WS </wordStack>
  rule <k> #setStack WS    => . ... </k> <wordStack> _  => WS      </wordStack>
  syntax InternalOp  ::=
    "#newAccount" Int
  | "#newExistingAccount" Int
  | "#newFreshAccount" Int
  rule <k> #newAccount ACCT => #newExistingAccount ACCT ... </k> <account> <acctID> ACCT </acctID> ... </account>
  rule <k> #newAccount ACCT => #newFreshAccount ACCT    ... </k>  [owise]
  rule <k> #newExistingAccount ACCT => #end EVMC_ACCOUNT_ALREADY_EXISTS ... </k>
         <account>
           <acctID> ACCT  </acctID>
           <code>   CODE  </code>
           <nonce>  NONCE </nonce>
           ...
         </account>
      requires CODE =/=K .Bytes orBool NONCE =/=Int 0
  rule <k> #newExistingAccount ACCT => . ... </k>
         <account>
           <acctID>      ACCT      </acctID>
           <code>        CODE      </code>
           <nonce>       0         </nonce>
           <storage>     _ => .Map </storage>
           <origStorage> _ => .Map </origStorage>
           ...
         </account>
      requires lengthBytes(CODE) ==Int 0
  rule <k> #newFreshAccount ACCT => . ... </k>
         <accounts>
           ( .Bag
          => <account>
               <acctID> ACCT </acctID>
               ...
             </account>
           )
           ...
         </accounts>
  syntax InternalOp  ::=
    "#transferFunds" Int Int Int
  | "#transferFundsToNonExistent" Int Int Int
  rule <k> #transferFunds ACCT ACCT VALUE => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE <=Int ORIGFROM
  rule <k> #transferFunds ACCTFROM ACCTTO VALUE => . ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM => ORIGFROM -Word VALUE </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTO </acctID>
           <balance> ORIGTO => ORIGTO +Word VALUE </balance>
           ...
         </account>
      requires ACCTFROM =/=K ACCTTO andBool VALUE <=Int ORIGFROM
  rule <k> #transferFunds ACCTFROM _ACCTTO VALUE => #end EVMC_BALANCE_UNDERFLOW ... </k>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> ORIGFROM </balance>
           ...
         </account>
      requires VALUE >Int ORIGFROM
  rule <k> #transferFunds ACCTFROM ACCTTO VALUE => #transferFundsToNonExistent ACCTFROM ACCTTO VALUE ... </k>  [owise]
  rule <k> #transferFundsToNonExistent ACCTFROM ACCTTO VALUE => #newAccount ACCTTO ~> #transferFunds ACCTFROM ACCTTO VALUE ... </k>
         <schedule> SCHED </schedule>
      requires ACCTFROM =/=K ACCTTO
       andBool (VALUE >Int 0 orBool notBool Gemptyisnonexistent << SCHED >>)
  rule <k> #transferFundsToNonExistent ACCTFROM ACCTTO 0 => . ... </k>
         <schedule> SCHED </schedule>
      requires ACCTFROM =/=K ACCTTO
       andBool Gemptyisnonexistent << SCHED >>
  syntax InvalidOp  ::=
    "INVALID"
  | "UNDEFINED" "(" Int ")"
  rule <k> INVALID      => #end EVMC_INVALID_INSTRUCTION   ... </k>
  rule <k> UNDEFINED(_) => #end EVMC_UNDEFINED_INSTRUCTION ... </k>
  syntax UnStackOp  ::=
    "POP"
  rule <k> POP _ => . ... </k>
  syntax StackOp  ::=
    "DUP" "(" Int ")" [klabel(DUP)]
  | "SWAP" "(" Int ")" [klabel(SWAP)]
  rule <k> DUP(N)  WS:WordStack => #setStack ((WS [ N -Int 1 ]) : WS)                      ... </k>
  rule <k> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Int 1 ]) : (WS [ N -Int 1 := W0 ])) ... </k>
  syntax PushOp  ::=
    "PUSH" "(" Int ")" [klabel(PUSH)]
  rule <k> PUSH(N) => #asWord(#range(PGM, PCOUNT +Int 1, N)) ~> #push ... </k>
         <pc> PCOUNT </pc>
         <program> PGM </program>
  syntax UnStackOp  ::=
    "MLOAD"
  rule <k> MLOAD INDEX => #asWord(#range(LM, INDEX, 32)) ~> #push ... </k>
         <localMem> LM </localMem>
  syntax BinStackOp  ::=
    "MSTORE"
  | "MSTORE8"
  rule <k> MSTORE INDEX VALUE => . ... </k>
         <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>
  rule <k> MSTORE8 INDEX VALUE => . ... </k>
         <localMem> LM => #write(LM, INDEX, (VALUE modInt 256)) </localMem>
  syntax UnStackOp  ::=
    "ISZERO"
  | "NOT"
  rule <k> ISZERO W => W ==Word 0 ~> #push ... </k>
  rule <k> NOT    W => ~Word W    ~> #push ... </k>
  syntax BinStackOp  ::=
    "ADD"
  | "MUL"
  | "SUB"
  | "DIV"
  | "EXP"
  | "MOD"
  rule <k> ADD W0 W1 => W0 +Word W1 ~> #push ... </k>
  rule <k> MUL W0 W1 => W0 *Word W1 ~> #push ... </k>
  rule <k> SUB W0 W1 => W0 -Word W1 ~> #push ... </k>
  rule <k> DIV W0 W1 => W0 /Word W1 ~> #push ... </k>
  rule <k> EXP W0 W1 => W0 ^Word W1 ~> #push ... </k>
  rule <k> MOD W0 W1 => W0 %Word W1 ~> #push ... </k>
  syntax BinStackOp  ::=
    "SDIV"
  | "SMOD"
  rule <k> SDIV W0 W1 => W0 /sWord W1 ~> #push ... </k>
  rule <k> SMOD W0 W1 => W0 %sWord W1 ~> #push ... </k>
  syntax TernStackOp  ::=
    "ADDMOD"
  | "MULMOD"
  rule <k> ADDMOD W0 W1 W2 => (W0 +Int W1) %Word W2 ~> #push ... </k>
  rule <k> MULMOD W0 W1 W2 => (W0 *Int W1) %Word W2 ~> #push ... </k>
  syntax BinStackOp  ::=
    "BYTE"
  | "SIGNEXTEND"
  rule <k> BYTE INDEX W     => byte(INDEX, W)     ~> #push ... </k>
  rule <k> SIGNEXTEND W0 W1 => signextend(W0, W1) ~> #push ... </k>
  syntax BinStackOp  ::=
    "SHL"
  | "SHR"
  | "SAR"
  rule <k> SHL W0 W1 => W1 <<Word  W0 ~> #push ... </k>
  rule <k> SHR W0 W1 => W1 >>Word  W0 ~> #push ... </k>
  rule <k> SAR W0 W1 => W1 >>sWord W0 ~> #push ... </k>
  syntax BinStackOp  ::=
    "AND"
  | "EVMOR"
  | "XOR"
  rule <k> AND   W0 W1 => W0 &Word W1   ~> #push ... </k>
  rule <k> EVMOR W0 W1 => W0 |Word W1   ~> #push ... </k>
  rule <k> XOR   W0 W1 => W0 xorWord W1 ~> #push ... </k>
  syntax BinStackOp  ::=
    "LT"
  | "GT"
  | "EQ"
  rule <k> LT W0 W1 => W0 <Word  W1 ~> #push ... </k>
  rule <k> GT W0 W1 => W0 >Word  W1 ~> #push ... </k>
  rule <k> EQ W0 W1 => W0 ==Word W1 ~> #push ... </k>
  syntax BinStackOp  ::=
    "SLT"
  | "SGT"
  rule <k> SLT W0 W1 => W0 s<Word W1 ~> #push ... </k>
  rule <k> SGT W0 W1 => W1 s<Word W0 ~> #push ... </k>
  syntax BinStackOp  ::=
    "SHA3"
  rule <k> SHA3 MEMSTART MEMWIDTH => keccak(#range(LM, MEMSTART, MEMWIDTH)) ~> #push ... </k>
         <localMem> LM </localMem>
  syntax NullStackOp  ::=
    "PC"
  | "GAS"
  | "GASPRICE"
  | "GASLIMIT"
  | "BASEFEE"
  rule <k> PC       => PCOUNT          ~> #push ... </k> <pc> PCOUNT </pc>
  rule <k> GAS      => gas2Int(GAVAIL) ~> #push ... </k> <gas> GAVAIL </gas>
  rule <k> GASPRICE => GPRICE          ~> #push ... </k> <gasPrice> GPRICE </gasPrice>
  rule <k> GASLIMIT => GLIMIT          ~> #push ... </k> <gasLimit> GLIMIT </gasLimit>
  rule <k> BASEFEE  => BFEE            ~> #push ... </k> <baseFee> BFEE </baseFee>
  syntax NullStackOp  ::=
    "COINBASE"
  | "TIMESTAMP"
  | "NUMBER"
  | "DIFFICULTY"
  | "PREVRANDAO"
  rule <k> COINBASE   => CB   ~> #push ... </k> <coinbase> CB </coinbase>
  rule <k> TIMESTAMP  => TS   ~> #push ... </k> <timestamp> TS </timestamp>
  rule <k> NUMBER     => NUMB ~> #push ... </k> <number> NUMB </number>
  rule <k> DIFFICULTY => DIFF ~> #push ... </k> <difficulty> DIFF </difficulty>
  rule <k> PREVRANDAO => RDAO ~> #push ... </k> <mixHash> RDAO </mixHash>
  syntax NullStackOp  ::=
    "ADDRESS"
  | "ORIGIN"
  | "CALLER"
  | "CALLVALUE"
  | "CHAINID"
  | "SELFBALANCE"
  rule <k> ADDRESS     => ACCT ~> #push ... </k> <id> ACCT </id>
  rule <k> ORIGIN      => ORG  ~> #push ... </k> <origin> ORG </origin>
  rule <k> CALLER      => CL   ~> #push ... </k> <caller> CL </caller>
  rule <k> CALLVALUE   => CV   ~> #push ... </k> <callValue> CV </callValue>
  rule <k> CHAINID     => CID  ~> #push ... </k> <chainID> CID </chainID>
  rule <k> SELFBALANCE => BAL  ~> #push ... </k>
         <id> ACCT </id>
         <account>
            <acctID> ACCT </acctID>
            <balance> BAL </balance>
            ...
         </account>
  syntax NullStackOp  ::=
    "MSIZE"
  | "CODESIZE"
  rule <k> MSIZE    => 32 *Word MU         ~> #push ... </k> <memoryUsed> MU </memoryUsed>
  rule <k> CODESIZE => lengthBytes(PGM) ~> #push ... </k> <program> PGM </program>
  syntax TernStackOp  ::=
    "CODECOPY"
  rule <k> CODECOPY MEMSTART PGMSTART WIDTH => . ... </k>
         <program> PGM </program>
         <localMem> LM =>  LM [ MEMSTART := #range(PGM, PGMSTART, WIDTH) ] </localMem>
  syntax UnStackOp  ::=
    "BLOCKHASH"
  rule <k> BLOCKHASH N => #blockhash(HASHES, N, HI -Int 1, 0) ~> #push ... </k>
         <number>      HI     </number>
         <blockhashes> HASHES </blockhashes>
  syntax Int  ::=
    "#blockhash" "(" List "," Int "," Int "," Int ")" [function, klabel(#blockhash)]
  rule #blockhash(_, N, HI, _) => 0 requires N >Int HI
  rule #blockhash(_, _, _, 256) => 0
  rule #blockhash(ListItem(0) _, _, _, _) => 0
  rule #blockhash(ListItem(H) _, N, N, _) => H
  rule #blockhash(ListItem(_) L, N, HI, A) => #blockhash(L, N, HI -Int 1, A +Int 1)  [owise]
  syntax NullStackOp  ::=
    "JUMPDEST"
  rule <k> JUMPDEST => . ... </k>
  syntax UnStackOp  ::=
    "JUMP"
  rule <k> JUMP DEST => #endBasicBlock... </k>
         <pc> _ => DEST </pc>
         <jumpDests> DESTS </jumpDests>
      requires DEST in DESTS
  rule <k> JUMP DEST => #end EVMC_BAD_JUMP_DESTINATION ... </k>
         <jumpDests> DESTS </jumpDests>
      requires notBool DEST in DESTS
  syntax BinStackOp  ::=
    "JUMPI"
  rule [jumpi.false]: <k> JUMPI _DEST I => .         ... </k> requires I  ==Int 0
  rule [jumpi.true]: <k> JUMPI  DEST I => JUMP DEST ... </k> requires I =/=Int 0
  syntax InternalOp  ::=
    "#endBasicBlock"
  rule <k> #endBasicBlock ~> (_:OpCode => .) ... </k>
  rule <k> (#endBasicBlock => .) ~> #execute ... </k>
  syntax NullStackOp  ::=
    "STOP"
  rule <k> STOP => #end EVMC_SUCCESS ... </k>
         <output> _ => .Bytes </output>
  syntax BinStackOp  ::=
    "RETURN"
  rule <k> RETURN RETSTART RETWIDTH => #end EVMC_SUCCESS ... </k>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
  syntax BinStackOp  ::=
    "REVERT"
  rule <k> REVERT RETSTART RETWIDTH => #end EVMC_REVERT ... </k>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
  syntax NullStackOp  ::=
    "CALLDATASIZE"
  rule <k> CALLDATASIZE => lengthBytes(CD) ~> #push ... </k>
         <callData> CD </callData>
  syntax UnStackOp  ::=
    "CALLDATALOAD"
  rule <k> CALLDATALOAD DATASTART => #asWord(#range(CD, DATASTART, 32)) ~> #push ... </k>
         <callData> CD </callData>
  syntax TernStackOp  ::=
    "CALLDATACOPY"
  rule <k> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := #range(CD, DATASTART, DATAWIDTH) ] </localMem>
         <callData> CD </callData>
  syntax NullStackOp  ::=
    "RETURNDATASIZE"
  rule <k> RETURNDATASIZE => lengthBytes(RD) ~> #push ... </k>
         <output> RD </output>
  syntax TernStackOp  ::=
    "RETURNDATACOPY"
  rule <k> RETURNDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := #range(RD, DATASTART, DATAWIDTH) ] </localMem>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH <=Int lengthBytes(RD)
  rule <k> RETURNDATACOPY _MEMSTART DATASTART DATAWIDTH => #end EVMC_INVALID_MEMORY_ACCESS ... </k>
         <output> RD </output>
      requires DATASTART +Int DATAWIDTH >Int lengthBytes(RD)
  syntax BinStackOp  ::=
    LogOp
  syntax LogOp  ::=
    "LOG" "(" Int ")" [klabel(LOG)]
  rule <k> LOG(N) MEMSTART MEMWIDTH => . ... </k>
         <id> ACCT </id>
         <wordStack> WS => #drop(N, WS) </wordStack>
         <localMem> LM </localMem>
         <log> L => L ListItem({ ACCT | WordStack2List(#take(N, WS)) | #range(LM, MEMSTART, MEMWIDTH) }) </log>
      requires #sizeWordStack(WS) >=Int N
  syntax UnStackOp  ::=
    "BALANCE"
  rule <k> BALANCE ACCT => BAL ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
  rule <k> BALANCE _ => 0 ~> #push ... </k>  [owise]
  syntax UnStackOp  ::=
    "EXTCODESIZE"
  rule <k> EXTCODESIZE ACCT => lengthBytes(CODE) ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>
  rule <k> EXTCODESIZE _ => 0 ~> #push ... </k>  [owise]
  syntax UnStackOp  ::=
    "EXTCODEHASH"
  rule <k> EXTCODEHASH ACCT => keccak(CODE) ~> #push ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE:Bytes </code>
           <nonce> NONCE </nonce>
           <balance> BAL </balance>
           ...
         </account>
      requires notBool #accountEmpty(CODE, NONCE, BAL)
  rule <k> EXTCODEHASH _ => 0 ~> #push ... </k>  [owise]
  syntax QuadStackOp  ::=
    "EXTCODECOPY"
  rule <k> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := #range(PGM, PGMSTART, WIDTH) ] </localMem>
         <account>
           <acctID> ACCT </acctID>
           <code> PGM </code>
           ...
         </account>
  rule <k> EXTCODECOPY _ MEMSTART _ WIDTH => . ... </k>
         <localMem> LM => LM [ MEMSTART := #padToWidth(WIDTH, .Bytes) ] </localMem>  [owise]
  syntax UnStackOp  ::=
    "SLOAD"
  rule <k> SLOAD INDEX => #lookup(STORAGE, INDEX) ~> #push ... </k>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
  syntax BinStackOp  ::=
    "SSTORE"
  rule <k> SSTORE INDEX NEW => . ... </k>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- NEW ] </storage>
           ...
         </account>
  syntax InternalOp  ::=
    "#checkCall" Int Int
  | "#call" Int Int Int Int Int Bytes Bool
  | "#callWithCode" Int Int Int Bytes Int Int Bytes Bool
  | "#mkCall" Int Int Int Bytes Int Bytes Bool
  rule <k> #checkCall ACCT VALUE
          => #refund GCALL ~> #pushCallStack ~> #pushWorldState
          ~> #end #if VALUE >Int BAL #then EVMC_BALANCE_UNDERFLOW #else #if CD >=Int 1024 #then EVMC_CALL_DEPTH_EXCEEDED #else EVMC_NONCE_EXCEEDED #fi #fi
         ...
         </k>
         <callDepth> CD </callDepth>
         <output> _ => .Bytes </output>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           <nonce> NONCE </nonce>
           ...
         </account>
         <callGas> GCALL </callGas>
      requires VALUE >Int BAL orBool CD >=Int 1024 orBool notBool #rangeNonce(NONCE)
  rule <k> #checkCall ACCT VALUE => . ... </k>
         <callDepth> CD </callDepth>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           <nonce> NONCE </nonce>
           ...
         </account>
      requires notBool (VALUE >Int BAL orBool CD >=Int 1024 orBool notBool #rangeNonce(NONCE))
  rule <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE CODE VALUE APPVALUE ARGS STATIC
         ...
         </k>
         <account>
           <acctID> ACCTCODE </acctID>
           <code> CODE </code>
           ...
         </account>
  rule <k> #call ACCTFROM ACCTTO ACCTCODE VALUE APPVALUE ARGS STATIC
          => #callWithCode ACCTFROM ACCTTO ACCTCODE .Bytes VALUE APPVALUE ARGS STATIC
         ...
         </k>  [owise]
  rule <k> #callWithCode ACCTFROM ACCTTO ACCTCODE BYTES VALUE APPVALUE ARGS STATIC
          => #pushCallStack ~> #pushWorldState
          ~> #transferFunds ACCTFROM ACCTTO VALUE
          ~> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC
         ...
         </k>
  rule <k> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC:Bool
          => #touchAccounts ACCTFROM ACCTTO ~> #accessAccounts ACCTFROM ACCTTO ~> #loadProgram BYTES ~> #initVM ~> #precompiled?(ACCTCODE, SCHED) ~> #execute
         ...
         </k>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => ARGS </callData>
         <callValue> _ => APPVALUE </callValue>
         <id> _ => ACCTTO </id>
         <gas> _ => GCALL </gas>
         <callGas> GCALL => 0 </callGas>
         <caller> _ => ACCTFROM </caller>
         <static> OLDSTATIC:Bool => OLDSTATIC orBool STATIC </static>
         <schedule> SCHED </schedule>
  syntax InternalOp  ::=
    "#precompiled?" "(" Int "," Schedule ")"
  rule <k> #precompiled?(ACCTCODE, SCHED) => #next [ #precompiled(ACCTCODE) ] ... </k> requires         #isPrecompiledAccount(ACCTCODE, SCHED)
       [preserves-definedness]
  rule <k> #precompiled?(ACCTCODE, SCHED) => .                                ... </k> requires notBool #isPrecompiledAccount(ACCTCODE, SCHED)
  syntax Bool  ::=
    "#isPrecompiledAccount" "(" Int "," Schedule ")" [function, klabel(#isPrecompiledAccount), smtlib(isPrecompiledAccount), total]
  rule [isPrecompiledAccount.true]: #isPrecompiledAccount(ACCTCODE, SCHED) => true  requires         ACCTCODE in #precompiledAccounts(SCHED)
  rule [isPrecompiledAccount.false]: #isPrecompiledAccount(ACCTCODE, SCHED) => false requires notBool ACCTCODE in #precompiledAccounts(SCHED)
  syntax KItem  ::=
    "#initVM"
  rule <k> #initVM      => . ...      </k>
         <pc>           _ => 0          </pc>
         <memoryUsed>   _ => 0          </memoryUsed>
         <output>       _ => .Bytes     </output>
         <wordStack>    _ => .WordStack </wordStack>
         <localMem>     _ => .Bytes     </localMem>
  syntax KItem  ::=
    "#loadProgram" Bytes
  rule <k> #loadProgram BYTES => . ... </k>
         <program> _ => BYTES </program>
         <jumpDests> _ => #computeValidJumpDests(BYTES) </jumpDests>
  syntax KItem  ::=
    "#touchAccounts" Account
  | "#touchAccounts" Account Account
  rule <k> #touchAccounts ADDR1 ADDR2 => #touchAccounts ADDR1 ~> #touchAccounts ADDR2 ... </k>
  rule <k> #touchAccounts ADDR => . ... </k>
         <touchedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set SetItem(ADDR) </touchedAccounts>
  syntax KItem  ::=
    "#accessStorage" Account Int
  rule <k> #accessStorage ACCT INDEX => . ... </k>
         <accessedStorage> ... ACCT |-> (TS:Set => TS |Set SetItem(INDEX)) ... </accessedStorage>
  rule <k> #accessStorage ACCT INDEX => . ... </k>
         <accessedStorage> TS => TS[ACCT <- SetItem(INDEX)] </accessedStorage>
      requires notBool ACCT in_keys(TS)
  syntax KItem  ::=
    "#accessAccounts" Account
  | "#accessAccounts" Set
  | "#accessAccounts" Account Account
  | "#accessAccounts" Account Account Set
  rule <k> #accessAccounts ADDR1:Account ADDR2:Account ADDRSET:Set => #accessAccounts ADDR1 ~> #accessAccounts ADDR2 ~> #accessAccounts ADDRSET ... </k>
  rule <k> #accessAccounts ADDR1:Account ADDR2:Account => #accessAccounts ADDR1 ~> #accessAccounts ADDR2 ... </k>
  rule <k> #accessAccounts ADDR:Account => . ... </k>
         <accessedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set SetItem(ADDR) </accessedAccounts>
  rule <k> #accessAccounts ADDRSET:Set => . ... </k>
         <accessedAccounts> TOUCHED_ACCOUNTS => TOUCHED_ACCOUNTS |Set ADDRSET </accessedAccounts>
  syntax Set  ::=
    "#computeValidJumpDests" "(" Bytes ")" [function, klabel(#computeValidJumpDests), memo, total]
  | "#computeValidJumpDests" "(" Bytes "," Int "," List ")" [function, klabel(#computeValidJumpDestsAux)]
  rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, .List)
  syntax Set  ::=
    "#computeValidJumpDestsWithinBound" "(" Bytes "," Int "," List ")" [function, klabel(#computeValidJumpDestsWithinBound)]
  rule #computeValidJumpDests(PGM, I, RESULT) => List2Set(RESULT) requires I >=Int lengthBytes(PGM)
  rule #computeValidJumpDests(PGM, I, RESULT) => #computeValidJumpDestsWithinBound(PGM, I, RESULT) requires I <Int lengthBytes(PGM)
  rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int 1, RESULT ListItem(I)) requires PGM [ I ] ==Int 91
  rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int #widthOpCode(PGM [ I ]), RESULT) requires notBool PGM [ I ] ==Int 91
  syntax Int  ::=
    "#widthOpCode" "(" Int ")" [function, klabel(#widthOpCode)]
  rule #widthOpCode(W) => W -Int 94 requires W >=Int 96 andBool W <=Int 127
  rule #widthOpCode(_) => 1  [owise]
  syntax KItem  ::=
    "#return" Int Int
  rule [return.exception]: <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #return _ _
          => #popCallStack ~> #popWorldState ~> 0 ~> #push
         ...
         </k>
         <output> _ => .Bytes </output>
  rule [return.revert]: <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #popWorldState
          ~> 0 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>
  rule [return.success]: <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #return RETSTART RETWIDTH
          => #popCallStack ~> #dropWorldState
          ~> 1 ~> #push ~> #refund GAVAIL ~> #setLocalMem RETSTART RETWIDTH OUT
         ...
         </k>
         <output> OUT </output>
         <gas> GAVAIL </gas>
  syntax InternalOp  ::=
    "#refund" Gas
  | "#setLocalMem" Int Int Bytes
  rule [refund]: <k> #refund G:Gas => . ... </k> <gas> GAVAIL => GAVAIL +Gas G </gas>
  rule <k> #setLocalMem START WIDTH WS => . ... </k>
         <localMem> LM => LM [ START := #range(WS, 0, minInt(WIDTH, lengthBytes(WS))) ] </localMem>
  syntax CallOp  ::=
    "CALL"
  rule [call]: <k> CALL _GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #checkCall ACCTFROM VALUE
          ~> #call ACCTFROM ACCTTO ACCTTO VALUE VALUE #range(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
  syntax CallOp  ::=
    "CALLCODE"
  rule [callcode]: <k> CALLCODE _GCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #checkCall ACCTFROM VALUE
          ~> #call ACCTFROM ACCTFROM ACCTTO VALUE VALUE #range(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
  syntax CallSixOp  ::=
    "DELEGATECALL"
  rule [delegatecall]: <k> DELEGATECALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #checkCall ACCTFROM 0
          ~> #call ACCTAPPFROM ACCTFROM ACCTTO 0 VALUE #range(LM, ARGSTART, ARGWIDTH) false
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <caller> ACCTAPPFROM </caller>
         <callValue> VALUE </callValue>
         <localMem> LM </localMem>
  syntax CallSixOp  ::=
    "STATICCALL"
  rule [staticcall]: <k> STATICCALL _GCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #checkCall ACCTFROM 0
          ~> #call ACCTFROM ACCTTO ACCTTO 0 0 #range(LM, ARGSTART, ARGWIDTH) true
          ~> #return RETSTART RETWIDTH
         ...
         </k>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
  syntax InternalOp  ::=
    "#create" Int Int Int Bytes
  | "#mkCreate" Int Int Int Bytes
  | "#incrementNonce" Int
  rule <k> #create ACCTFROM ACCTTO VALUE INITCODE
          => #incrementNonce ACCTFROM
          ~> #pushCallStack ~> #pushWorldState
          ~> #newAccount ACCTTO
          ~> #transferFunds ACCTFROM ACCTTO VALUE
          ~> #mkCreate ACCTFROM ACCTTO VALUE INITCODE
         ...
         </k>
  rule <k> #mkCreate ACCTFROM ACCTTO VALUE INITCODE
          => #touchAccounts ACCTFROM ACCTTO ~> #accessAccounts ACCTFROM ACCTTO ~> #loadProgram INITCODE ~> #initVM ~> #execute
         ...
         </k>
         <schedule> SCHED </schedule>
         <id> _ => ACCTTO </id>
         <gas> _ => GCALL </gas>
         <callGas> GCALL => 0 </callGas>
         <caller> _ => ACCTFROM </caller>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => .Bytes </callData>
         <callValue> _ => VALUE </callValue>
         <account>
           <acctID> ACCTTO </acctID>
           <nonce> NONCE => #if Gemptyisnonexistent << SCHED >> #then NONCE +Int 1 #else NONCE #fi </nonce>
           ...
         </account>
  rule <k> #incrementNonce ACCT => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE => NONCE +Int 1 </nonce>
           ...
         </account>
  syntax Bool  ::=
    "#isValidCode" "(" Bytes "," Schedule ")" [function, klabel(#isValidCode)]
  rule #isValidCode( OUT ,  SCHED) => Ghasrejectedfirstbyte << SCHED >> impliesBool OUT[0] =/=Int 239 requires lengthBytes(OUT) >Int 0
  rule #isValidCode(_OUT , _SCHED) => true                                                             [owise]
  syntax KItem  ::=
    "#codeDeposit" Int
  | "#mkCodeDeposit" Int
  | "#finishCodeDeposit" Int Bytes
  rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #codeDeposit _ => #popCallStack ~> #popWorldState ~> 0 ~> #push ... </k> <output> _ => .Bytes </output>
  rule <statusCode> EVMC_REVERT </statusCode>
         <k> #halt ~> #codeDeposit _ => #popCallStack ~> #popWorldState ~> #refund GAVAIL ~> 0 ~> #push ... </k>
         <gas> GAVAIL </gas>
  rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #codeDeposit ACCT => #mkCodeDeposit ACCT ... </k>
  rule <k> #mkCodeDeposit ACCT
          => Gcodedeposit < SCHED > *Int lengthBytes(OUT) ~> #deductGas
          ~> #finishCodeDeposit ACCT OUT
         ...
         </k>
         <schedule> SCHED </schedule>
         <output> OUT => .Bytes </output>
      requires lengthBytes(OUT) <=Int maxCodeSize < SCHED > andBool #isValidCode(OUT, SCHED)
  rule <k> #mkCodeDeposit _ACCT => #popCallStack ~> #popWorldState ~> 0 ~> #push ... </k>
         <schedule> SCHED </schedule>
         <output> OUT => .Bytes </output>
      requires notBool ( lengthBytes(OUT) <=Int maxCodeSize < SCHED > andBool #isValidCode(OUT, SCHED) )
  rule <k> #finishCodeDeposit ACCT OUT
          => #popCallStack ~> #dropWorldState
          ~> #refund GAVAIL ~> ACCT ~> #push
         ...
         </k>
         <gas> GAVAIL </gas>
         <account>
           <acctID> ACCT </acctID>
           <code> _ => OUT </code>
           ...
         </account>
  rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #finishCodeDeposit ACCT _
          => #popCallStack ~> #dropWorldState
          ~> #refund GAVAIL ~> ACCT ~> #push
         ...
         </k>
         <gas> GAVAIL </gas>
         <schedule> FRONTIER </schedule>
  rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #finishCodeDeposit _ _ => #popCallStack ~> #popWorldState ~> 0 ~> #push ... </k>
         <schedule> SCHED </schedule>
      requires SCHED =/=K FRONTIER
  syntax TernStackOp  ::=
    "CREATE"
  rule [create]: <k> CREATE VALUE MEMSTART MEMWIDTH
          => #accessAccounts #newAddr(ACCT, NONCE)
          ~> #checkCall ACCT VALUE
          ~> #create ACCT #newAddr(ACCT, NONCE) VALUE #range(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddr(ACCT, NONCE)
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
  syntax QuadStackOp  ::=
    "CREATE2"
  rule [create2]: <k> CREATE2 VALUE MEMSTART MEMWIDTH SALT
          => #accessAccounts #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH))
          ~> #checkCall ACCT VALUE
          ~> #create ACCT #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH)) VALUE #range(LM, MEMSTART, MEMWIDTH)
          ~> #codeDeposit #newAddr(ACCT, SALT, #range(LM, MEMSTART, MEMWIDTH))
         ...
         </k>
         <id> ACCT </id>
         <localMem> LM </localMem>
  syntax UnStackOp  ::=
    "SELFDESTRUCT"
  rule <k> SELFDESTRUCT ACCTTO => #touchAccounts ACCT ACCTTO ~> #transferFunds ACCT ACCTTO BALFROM ~> #end EVMC_SUCCESS ... </k>
         <id> ACCT </id>
         <selfDestruct> SDS => SDS |Set SetItem(ACCT) </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM </balance>
           ...
         </account>
         <output> _ => .Bytes </output>
      requires ACCT =/=Int ACCTTO
  rule <k> SELFDESTRUCT ACCT => #touchAccounts ACCT ~> #end EVMC_SUCCESS ... </k>
         <id> ACCT </id>
         <selfDestruct> SDS => SDS |Set SetItem(ACCT) </selfDestruct>
         <account>
           <acctID> ACCT </acctID>
           <balance> _ => 0 </balance>
           ...
         </account>
         <output> _ => .Bytes </output>
  syntax NullStackOp  ::=
    PrecompiledOp
  syntax PrecompiledOp  ::=
    "#precompiled" "(" Int ")" [function, klabel(#precompiled)]
  rule #precompiled(1) => ECREC
  rule #precompiled(2) => SHA256
  rule #precompiled(3) => RIP160
  rule #precompiled(4) => ID
  rule #precompiled(5) => MODEXP
  rule #precompiled(6) => ECADD
  rule #precompiled(7) => ECMUL
  rule #precompiled(8) => ECPAIRING
  rule #precompiled(9) => BLAKE2F
  syntax Set  ::=
    "#precompiledAccounts" "(" Schedule ")" [function, klabel(#precompiledAccounts), total]
  rule #precompiledAccounts(DEFAULT)           => SetItem(1) SetItem(2) SetItem(3) SetItem(4)
  rule #precompiledAccounts(FRONTIER)          => #precompiledAccounts(DEFAULT)
  rule #precompiledAccounts(HOMESTEAD)         => #precompiledAccounts(FRONTIER)
  rule #precompiledAccounts(TANGERINE_WHISTLE) => #precompiledAccounts(HOMESTEAD)
  rule #precompiledAccounts(SPURIOUS_DRAGON)   => #precompiledAccounts(TANGERINE_WHISTLE)
  rule #precompiledAccounts(BYZANTIUM)         => #precompiledAccounts(SPURIOUS_DRAGON) SetItem(5) SetItem(6) SetItem(7) SetItem(8)
  rule #precompiledAccounts(CONSTANTINOPLE)    => #precompiledAccounts(BYZANTIUM)
  rule #precompiledAccounts(PETERSBURG)        => #precompiledAccounts(CONSTANTINOPLE)
  rule #precompiledAccounts(ISTANBUL)          => #precompiledAccounts(PETERSBURG) SetItem(9)
  rule #precompiledAccounts(BERLIN)            => #precompiledAccounts(ISTANBUL)
  rule #precompiledAccounts(LONDON)            => #precompiledAccounts(BERLIN)
  rule #precompiledAccounts(MERGE)             => #precompiledAccounts(LONDON)
  syntax PrecompiledOp  ::=
    "ECREC"
  rule <k> ECREC => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #ecrec(#range(DATA, 0, 32), #range(DATA, 32, 32), #range(DATA, 64, 32), #range(DATA, 96, 32)) </output>
  syntax Bytes  ::=
    "#ecrec" "(" Bytes "," Bytes "," Bytes "," Bytes ")" [function, klabel(#ecrec), smtlib(ecrec)]
  | "#ecrec" "(" Account ")" [function, klabel(#ecrec)]
  rule [ecrec]: #ecrec(HASH, SIGV, SIGR, SIGS) => #ecrec(#sender(#unparseByteStack(HASH), #asWord(SIGV), #unparseByteStack(SIGR), #unparseByteStack(SIGS)))  [concrete]
  rule #ecrec(.Account) => .Bytes
  rule #ecrec(N:Int)    => #padToWidth(32, #asByteStack(N))
  syntax PrecompiledOp  ::=
    "SHA256"
  rule <k> SHA256 => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #parseHexBytes(Sha256(#unparseByteStack(DATA))) </output>
  syntax PrecompiledOp  ::=
    "RIP160"
  rule <k> RIP160 => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #padToWidth(32, #parseHexBytes(RipEmd160(#unparseByteStack(DATA)))) </output>
  syntax PrecompiledOp  ::=
    "ID"
  rule <k> ID => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => DATA </output>
  syntax PrecompiledOp  ::=
    "MODEXP"
  rule <k> MODEXP => #end EVMC_SUCCESS ... </k>
         <callData> DATA </callData>
         <output> _ => #modexp1(#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32)), #asWord(#range(DATA, 64, 32)), #range(DATA, 96, maxInt(0, lengthBytes(DATA) -Int 96))) </output>
  syntax Bytes  ::=
    "#modexp1" "(" Int "," Int "," Int "," Bytes ")" [function, klabel(#modexp1)]
  | "#modexp2" "(" Int "," Int "," Int "," Bytes ")" [function, klabel(#modexp2)]
  | "#modexp3" "(" Int "," Int "," Int "," Bytes ")" [function, klabel(#modexp3)]
  | "#modexp4" "(" Int "," Int "," Int ")" [function, klabel(#modexp4)]
  rule #modexp1(BASELEN, EXPLEN,   MODLEN, DATA) => #modexp2(#asInteger(#range(DATA, 0, BASELEN)), EXPLEN, MODLEN, #range(DATA, BASELEN, maxInt(0, lengthBytes(DATA) -Int BASELEN))) requires MODLEN =/=Int 0
  rule #modexp1(_,       _,        0,      _)    => .Bytes
  rule #modexp2(BASE,    EXPLEN,   MODLEN, DATA) => #modexp3(BASE, #asInteger(#range(DATA, 0, EXPLEN)), MODLEN, #range(DATA, EXPLEN, maxInt(0, lengthBytes(DATA) -Int EXPLEN)))
  rule #modexp3(BASE,    EXPONENT, MODLEN, DATA) => #padToWidth(MODLEN, #modexp4(BASE, EXPONENT, #asInteger(#range(DATA, 0, MODLEN))))
  rule #modexp4(BASE,    EXPONENT, MODULUS)      => #asByteStack(powmod(BASE, EXPONENT, MODULUS))
  syntax PrecompiledOp  ::=
    "ECADD"
  rule <k> ECADD => #ecadd((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), (#asWord(#range(DATA, 64, 32)), #asWord(#range(DATA, 96, 32)))) ... </k>
         <callData> DATA </callData>
  syntax InternalOp  ::=
    "#ecadd" "(" G1Point "," G1Point ")" [klabel(#ecadd)]
  rule <k> #ecadd(P1, P2) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(P1) orBool notBool isValidPoint(P2)
  rule <k> #ecadd(P1, P2) => #end EVMC_SUCCESS ... </k> <output> _ => #point(BN128Add(P1, P2)) </output>
      requires isValidPoint(P1) andBool isValidPoint(P2)
  syntax PrecompiledOp  ::=
    "ECMUL"
  rule <k> ECMUL => #ecmul((#asWord(#range(DATA, 0, 32)), #asWord(#range(DATA, 32, 32))), #asWord(#range(DATA, 64, 32))) ... </k>
         <callData> DATA </callData>
  syntax InternalOp  ::=
    "#ecmul" "(" G1Point "," Int ")" [klabel(#ecmul)]
  rule <k> #ecmul(P, _S) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(P)
  rule <k> #ecmul(P,  S) => #end EVMC_SUCCESS ... </k> <output> _ => #point(BN128Mul(P, S)) </output>
      requires isValidPoint(P)
  syntax Bytes  ::=
    "#point" "(" G1Point ")" [function, klabel(#point)]
  rule #point((X, Y)) => #padToWidth(32, #asByteStack(X)) +Bytes #padToWidth(32, #asByteStack(Y))
  syntax PrecompiledOp  ::=
    "ECPAIRING"
  rule <k> ECPAIRING => #ecpairing(.List, .List, 0, DATA, lengthBytes(DATA)) ... </k>
         <callData> DATA </callData>
      requires lengthBytes(DATA) modInt 192 ==Int 0
  rule <k> ECPAIRING => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> DATA </callData>
      requires lengthBytes(DATA) modInt 192 =/=Int 0
  syntax InternalOp  ::=
    "#ecpairing" "(" List "," List "," Int "," Bytes "," Int ")" [klabel(#ecpairing)]
  rule <k> (.K => #checkPoint) ~> #ecpairing((.List => ListItem((#asWord(#range(DATA, I, 32)), #asWord(#range(DATA, I +Int 32, 32))))) _, (.List => ListItem((#asWord(#range(DATA, I +Int 96, 32)) x #asWord(#range(DATA, I +Int 64, 32)) , #asWord(#range(DATA, I +Int 160, 32)) x #asWord(#range(DATA, I +Int 128, 32))))) _, I => I +Int 192, DATA, LEN) ... </k>
      requires I =/=Int LEN
  rule <k> #ecpairing(A, B, LEN, _, LEN) => #end EVMC_SUCCESS ... </k>
         <output> _ => #padToWidth(32, #asByteStack(bool2Word(BN128AtePairing(A, B)))) </output>
  syntax InternalOp  ::=
    "#checkPoint"
  rule <k> (#checkPoint => .) ~> #ecpairing(ListItem(AK::G1Point) _, ListItem(BK::G2Point) _, _, _, _) ... </k>
      requires isValidPoint(AK) andBool isValidPoint(BK)
  rule <k> #checkPoint ~> #ecpairing(ListItem(AK::G1Point) _, ListItem(BK::G2Point) _, _, _, _) => #end EVMC_PRECOMPILE_FAILURE ... </k>
      requires notBool isValidPoint(AK) orBool notBool isValidPoint(BK)
  syntax PrecompiledOp  ::=
    "BLAKE2F"
  rule <k> BLAKE2F => #end EVMC_SUCCESS ... </k>
         <output> _ => #parseByteStack( Blake2Compress( #unparseByteStack( DATA ) ) ) </output>
         <callData> DATA </callData>
      requires lengthBytes( DATA ) ==Int 213
       andBool DATA[212] <=Int 1
  rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> DATA </callData>
      requires lengthBytes( DATA ) ==Int 213
       andBool DATA[212] >Int 1
  rule <k> BLAKE2F => #end EVMC_PRECOMPILE_FAILURE ... </k>
         <callData> DATA </callData>
      requires lengthBytes( DATA ) =/=Int 213
  syntax InternalOp  ::=
    "#gas" "[" OpCode "," OpCode "]"
  rule <k> #gas [ OP , AOP ]
          => #memory [ OP , AOP ]
          ~> #gas [ AOP ]
          ~> #access [ OP , AOP ]
         ...
        </k>
  rule <k> #gas [ OP ] => #gasExec(SCHED, OP) ~> #deductGas ... </k>
         <schedule> SCHED </schedule>
  rule <k> #memory [ OP , AOP ] => #memory(AOP, MU) ~> #deductMemory ... </k>
         <memoryUsed> MU </memoryUsed>
      requires #usesMemory(OP)
  rule <k> #memory [ _ , _ ] => . ... </k>  [owise]
  syntax InternalOp  ::=
    "#gas" "[" OpCode "]"
  | "#deductGas"
  | "#deductMemoryGas"
  | "#memory" "[" OpCode "," OpCode "]"
  | "#deductMemory"
  rule <k> MU':Int ~> #deductMemory => (Cmem(SCHED, MU') -Int Cmem(SCHED, MU)) ~> #deductMemoryGas ... </k>
         <memoryUsed> MU => MU' </memoryUsed> <schedule> SCHED </schedule>
  rule <k> _G:Gas ~> (#deductMemoryGas => #deductGas)   ... </k>
  rule <k>  G:Gas ~> #deductGas => #end EVMC_OUT_OF_GAS ... </k> <gas> GAVAIL:Gas                  </gas> requires GAVAIL <Gas G
  rule <k>  G:Gas ~> #deductGas => .                    ... </k> <gas> GAVAIL:Gas => GAVAIL -Gas G </gas> requires G <=Gas GAVAIL
  syntax Bool  ::=
    "#inStorage" "(" Map "," Account "," Int ")" [function, klabel(#inStorage), total]
  | "#inStorageAux1" "(" KItem "," Int ")" [function, klabel(#inStorageAux1), total]
  | "#inStorageAux2" "(" Set "," Int ")" [function, klabel(#inStorageAux2), total]
  rule #inStorage(TS, ACCT, KEY) => #inStorageAux1(TS[ACCT], KEY) requires ACCT in_keys(TS)
  rule #inStorage(_, _, _)       => false                          [owise]
  rule #inStorageAux1(KEYS:Set, KEY) => #inStorageAux2(KEYS, KEY)
  rule #inStorageAux1(_, _)          => false                      [owise]
  rule #inStorageAux2(KEYS, KEY) => true  requires KEY in KEYS
  rule #inStorageAux2(_, _)      => false  [owise]
  syntax Int  ::=
    "#memory" "(" OpCode "," Int ")" [function, klabel(#memory), total]
  rule #memory ( MLOAD INDEX     , MU ) => #memoryUsageUpdate(MU, INDEX, 32)
  rule #memory ( MSTORE INDEX _  , MU ) => #memoryUsageUpdate(MU, INDEX, 32)
  rule #memory ( MSTORE8 INDEX _ , MU ) => #memoryUsageUpdate(MU, INDEX, 1)
  rule #memory ( SHA3 START WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( LOG(_) START WIDTH , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( CODECOPY START _ WIDTH       , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( EXTCODECOPY _ START _ WIDTH  , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( CALLDATACOPY START _ WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( RETURNDATACOPY START _ WIDTH , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( CREATE  _ START WIDTH   , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( CREATE2 _ START WIDTH _ , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( RETURN START WIDTH      , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( REVERT START WIDTH      , MU ) => #memoryUsageUpdate(MU, START, WIDTH)
  rule #memory ( _COP:CallOp     _ _ _ ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH)
  rule #memory ( _CSOP:CallSixOp _ _   ARGSTART ARGWIDTH RETSTART RETWIDTH , MU ) => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH)
  rule #memory ( _ , MU ) => MU  [owise]
  syntax Bool  ::=
    "#usesMemory" "(" OpCode ")" [function, klabel(#usesMemory), total]
  rule #usesMemory(_:LogOp)        => true
  rule #usesMemory(_:CallOp)       => true
  rule #usesMemory(_:CallSixOp)    => true
  rule #usesMemory(MLOAD)          => true
  rule #usesMemory(MSTORE)         => true
  rule #usesMemory(MSTORE8)        => true
  rule #usesMemory(SHA3)           => true
  rule #usesMemory(CODECOPY)       => true
  rule #usesMemory(EXTCODECOPY)    => true
  rule #usesMemory(CALLDATACOPY)   => true
  rule #usesMemory(RETURNDATACOPY) => true
  rule #usesMemory(CREATE)         => true
  rule #usesMemory(CREATE2)        => true
  rule #usesMemory(RETURN)         => true
  rule #usesMemory(REVERT)         => true
  rule #usesMemory(_)              => false  [owise]
  syntax Int  ::=
    "#memoryUsageUpdate" "(" Int "," Int "," Int ")" [function, klabel(#memoryUsageUpdate), total]
  rule #memoryUsageUpdate(MU,     _, WIDTH) => MU                                       requires notBool 0 <Int WIDTH  [concrete]
  rule #memoryUsageUpdate(MU, START, WIDTH) => maxInt(MU, (START +Int WIDTH) up/Int 32) requires         0 <Int WIDTH  [concrete]
  syntax Bool  ::=
    "#usesAccessList" "(" OpCode ")" [function, klabel(#usesAccessList), total]
  rule #usesAccessList(OP)     => true  requires isAddr1Op(OP)
  rule #usesAccessList(OP)     => true  requires isAddr2Op(OP)
  rule #usesAccessList(SLOAD)  => true
  rule #usesAccessList(SSTORE) => true
  rule #usesAccessList(_)      => false  [owise]
  syntax InternalOp  ::=
    "#access" "[" OpCode "," OpCode "]"
  rule <k> #access [ OP , AOP ] => #gasAccess(SCHED, AOP) ~> #deductGas ... </k>
         <schedule> SCHED </schedule>
      requires Ghasaccesslist << SCHED >> andBool #usesAccessList(OP)
  rule <k> #access [ _ , _ ] => . ... </k> <schedule> _ </schedule>  [owise]
  syntax InternalOp  ::=
    "#gasAccess" "(" Schedule "," OpCode ")" [klabel(#gasAccess)]
  rule <k> #gasAccess(SCHED, EXTCODESIZE ACCT)            => #accessAccounts ACCT ~> Caddraccess(SCHED, ACCT in ACCTS)                                           ... </k> <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasAccess(SCHED, EXTCODECOPY ACCT _ _ _)      => #accessAccounts ACCT ~> Caddraccess(SCHED, ACCT in ACCTS)                                           ... </k> <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasAccess(SCHED, EXTCODEHASH ACCT)            => #accessAccounts ACCT ~> Caddraccess(SCHED, ACCT in ACCTS)                                           ... </k> <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasAccess(SCHED, BALANCE ACCT)                => #accessAccounts ACCT ~> Caddraccess(SCHED, ACCT in ACCTS)                                           ... </k> <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasAccess(SCHED, SELFDESTRUCT ACCT)           => #accessAccounts ACCT ~> #if ACCT in ACCTS #then 0 #else Gcoldaccountaccess < SCHED > #fi            ... </k> <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasAccess(_    , CALL _ ACCT _ _ _ _ _)       => #accessAccounts ACCT ~> 0                                                                           ... </k>
  rule <k> #gasAccess(_    , CALLCODE _ ACCT _ _ _ _ _)   => #accessAccounts ACCT ~> 0                                                                           ... </k>
  rule <k> #gasAccess(_    , DELEGATECALL _ ACCT _ _ _ _) => #accessAccounts ACCT ~> 0                                                                           ... </k>
  rule <k> #gasAccess(_    , STATICCALL _ ACCT _ _ _ _)   => #accessAccounts ACCT ~> 0                                                                           ... </k>
  rule <k> #gasAccess(_    , SLOAD INDEX )                => #accessStorage ACCT INDEX ~> 0                                                                      ... </k> <id> ACCT </id>
  rule <k> #gasAccess(SCHED, SSTORE INDEX _)              => #accessStorage ACCT INDEX ~> #if #inStorage(TS, ACCT, INDEX) #then 0 #else Gcoldsload < SCHED > #fi ... </k> <id> ACCT </id> <accessedStorage> TS </accessedStorage>
  rule <k> #gasAccess(_    , _ )                          => 0                                                                                                  ... </k>  [owise]
  syntax InternalOp  ::=
    "#gasExec" "(" Schedule "," OpCode ")" [klabel(#gasExec)]
  rule <k> #gasExec(SCHED, SSTORE INDEX NEW) => Csstore(SCHED, NEW, #lookup(STORAGE, INDEX), #lookup(ORIGSTORAGE, INDEX)) ... </k>
         <id> ACCT </id>
         <gas> GAVAIL </gas>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           <origStorage> ORIGSTORAGE </origStorage>
           ...
         </account>
         <refund> R => R +Int Rsstore(SCHED, NEW, #lookup(STORAGE, INDEX), #lookup(ORIGSTORAGE, INDEX)) </refund>
      requires notBool Ghassstorestipend << SCHED >>
        orBool notBool GAVAIL <=Gas Gcallstipend < SCHED >
  rule <k> #gasExec(SCHED, SSTORE _ _ ) => #end EVMC_OUT_OF_GAS ... </k>
         <gas> GAVAIL </gas>
      requires Ghassstorestipend << SCHED >>
       andBool GAVAIL <=Gas Gcallstipend < SCHED >
  rule <k> #gasExec(SCHED, EXP _ 0)  => Gexp < SCHED > ... </k>
  rule <k> #gasExec(SCHED, EXP _ W1) => Gexp < SCHED > +Int (Gexpbyte < SCHED > *Int (1 +Int (log256Int(W1)))) ... </k> requires W1 =/=Int 0
  rule <k> #gasExec(SCHED, CALLDATACOPY    _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
  rule <k> #gasExec(SCHED, RETURNDATACOPY  _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
  rule <k> #gasExec(SCHED, CODECOPY        _ _ WIDTH) => Gverylow < SCHED > +Int (Gcopy < SCHED > *Int (WIDTH up/Int 32)) ... </k>
  rule <k> #gasExec(SCHED, LOG(N) _ WIDTH) => (Glog < SCHED > +Int (Glogdata < SCHED > *Int WIDTH) +Int (N *Int Glogtopic < SCHED >)) ... </k>
  rule <k> #gasExec(SCHED, CALL GCAP ACCTTO VALUE _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, VALUE, ACCTTO in ACCTS) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, VALUE, ACCTTO in ACCTS)
         ...
         </k>
         <gas> GAVAIL </gas>
         <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasExec(SCHED, CALLCODE GCAP ACCTTO VALUE _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTFROM), GCAP, GAVAIL, VALUE, ACCTTO in ACCTS) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTFROM), GCAP, GAVAIL, VALUE, ACCTTO in ACCTS)
         ...
         </k>
         <id> ACCTFROM </id>
         <gas> GAVAIL </gas>
         <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasExec(SCHED, DELEGATECALL GCAP ACCTTO _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTFROM), GCAP, GAVAIL, 0, ACCTTO in ACCTS) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTFROM), GCAP, GAVAIL, 0, ACCTTO in ACCTS)
         ...
         </k>
         <id> ACCTFROM </id>
         <gas> GAVAIL </gas>
         <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasExec(SCHED, STATICCALL GCAP ACCTTO _ _ _ _)
          => Ccallgas(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, 0, ACCTTO in ACCTS) ~> #allocateCallGas
          ~> Ccall(SCHED, #accountNonexistent(ACCTTO), GCAP, GAVAIL, 0, ACCTTO in ACCTS)
         ...
         </k>
         <gas> GAVAIL </gas>
         <accessedAccounts> ACCTS </accessedAccounts>
  rule <k> #gasExec(SCHED, SELFDESTRUCT ACCTTO) => Cselfdestruct(SCHED, #accountNonexistent(ACCTTO), BAL) ... </k>
         <id> ACCTFROM </id>
         <selfDestruct> SDS </selfDestruct>
         <refund> RF => #if ACCTFROM in SDS #then RF #else RF +Word Rselfdestruct < SCHED > #fi </refund>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL </balance>
           ...
         </account>
  rule <k> #gasExec(SCHED, CREATE _ _ _)
          => Gcreate < SCHED > ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>
  rule <k> #gasExec(SCHED, CREATE2 _ _ WIDTH _)
          => Gcreate < SCHED > +Int Gsha3word < SCHED > *Int (WIDTH up/Int 32) ~> #deductGas
          ~> #allocateCreateGas ~> 0
         ...
         </k>
  rule <k> #gasExec(SCHED, SHA3 _ WIDTH) => Gsha3 < SCHED > +Int (Gsha3word < SCHED > *Int (WIDTH up/Int 32)) ... </k>
  rule <k> #gasExec(SCHED, JUMPDEST)    => Gjumpdest < SCHED >                        ... </k>
  rule <k> #gasExec(SCHED, SLOAD INDEX) => Csload(SCHED, #inStorage(TS, ACCT, INDEX)) ... </k>
         <id> ACCT </id>
         <accessedStorage> TS </accessedStorage>
  rule <k> #gasExec(SCHED, STOP)       => Gzero < SCHED > ... </k>
  rule <k> #gasExec(SCHED, RETURN _ _) => Gzero < SCHED > ... </k>
  rule <k> #gasExec(SCHED, REVERT _ _) => Gzero < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ADDRESS)        => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ORIGIN)         => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CALLER)         => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CALLVALUE)      => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CALLDATASIZE)   => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, RETURNDATASIZE) => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CODESIZE)       => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, GASPRICE)       => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, COINBASE)       => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, TIMESTAMP)      => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, NUMBER)         => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, DIFFICULTY)     => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, PREVRANDAO)     => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, GASLIMIT)       => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, BASEFEE)        => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, POP _)          => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, PC)             => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MSIZE)          => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, GAS)            => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CHAINID)        => Gbase < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ADD _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SUB _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, NOT _)          => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, LT _ _)         => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, GT _ _)         => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SLT _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SGT _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, EQ _ _)         => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ISZERO _)       => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, AND _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, EVMOR _ _)      => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, XOR _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, BYTE _ _)       => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SHL _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SHR _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SAR _ _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, CALLDATALOAD _) => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MLOAD _)        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MSTORE _ _)     => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MSTORE8 _ _)    => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, PUSH(_))        => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, DUP(_) _)       => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SWAP(_) _)      => Gverylow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MUL _ _)        => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, DIV _ _)        => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SDIV _ _)       => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MOD _ _)        => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SMOD _ _)       => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SIGNEXTEND _ _) => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, SELFBALANCE)    => Glow < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ADDMOD _ _ _) => Gmid < SCHED > ... </k>
  rule <k> #gasExec(SCHED, MULMOD _ _ _) => Gmid < SCHED > ... </k>
  rule <k> #gasExec(SCHED, JUMP _) => Gmid < SCHED > ... </k>
  rule <k> #gasExec(SCHED, JUMPI _ _) => Ghigh < SCHED > ... </k>
  rule <k> #gasExec(SCHED, EXTCODECOPY _ _ _ WIDTH) => Cextcodecopy(SCHED, WIDTH) ... </k>
  rule <k> #gasExec(SCHED, EXTCODESIZE _)           => Cextcodesize(SCHED)        ... </k>
  rule <k> #gasExec(SCHED, BALANCE _)               => Cbalance(SCHED)            ... </k>
  rule <k> #gasExec(SCHED, EXTCODEHASH _)           => Cextcodehash(SCHED)        ... </k>
  rule <k> #gasExec(SCHED, BLOCKHASH _)             => Gblockhash < SCHED >       ... </k>
  rule <k> #gasExec(_, ECREC)  => 3000 ... </k>
  rule <k> #gasExec(_, SHA256) =>  60 +Int  12 *Int (lengthBytes(DATA) up/Int 32) ... </k> <callData> DATA </callData>
  rule <k> #gasExec(_, RIP160) => 600 +Int 120 *Int (lengthBytes(DATA) up/Int 32) ... </k> <callData> DATA </callData>
  rule <k> #gasExec(_, ID)     =>  15 +Int   3 *Int (lengthBytes(DATA) up/Int 32) ... </k> <callData> DATA </callData>
  rule <k> #gasExec(SCHED, MODEXP) => Cmodexp(SCHED, DATA, #asWord(#range(DATA, 0, 32) ), #asWord(#range(DATA, 32, 32)), #asWord(#range(DATA, 64, 32))) ... </k>
         <callData> DATA </callData>
  rule <k> #gasExec(SCHED, ECADD)     => Gecadd < SCHED>  ... </k>
  rule <k> #gasExec(SCHED, ECMUL)     => Gecmul < SCHED > ... </k>
  rule <k> #gasExec(SCHED, ECPAIRING) => Gecpairconst < SCHED > +Int (lengthBytes(DATA) /Int 192) *Int Gecpaircoeff < SCHED > ... </k> <callData> DATA </callData>
  rule <k> #gasExec(SCHED, BLAKE2F)   => Gfround < SCHED > *Int #asWord(#range(DATA, 0, 4) ) ... </k> <callData> DATA </callData>
  syntax InternalOp  ::=
    "#allocateCallGas"
  rule <k> GCALL:Gas ~> #allocateCallGas => . ... </k>
         <callGas> _ => GCALL </callGas>
  syntax InternalOp  ::=
    "#allocateCreateGas"
  rule <schedule> SCHED </schedule>
         <k> #allocateCreateGas => . ... </k>
         <gas>     GAVAIL => #if Gstaticcalldepth << SCHED >> #then 0      #else GAVAIL /Gas 64      #fi </gas>
         <callGas> _      => #if Gstaticcalldepth << SCHED >> #then GAVAIL #else #allBut64th(GAVAIL) #fi </callGas>
       [preserves-definedness]
  syntax Exp  ::=
    Int
  | Gas
  syntax KResult  ::=
    Int
  syntax Exp  ::=
    "Ccall" "(" Schedule "," BExp "," Gas "," Gas "," Int "," Bool ")" [klabel(Ccall), strict(2)]
  | "Ccallgas" "(" Schedule "," BExp "," Gas "," Gas "," Int "," Bool ")" [klabel(Ccallgas), strict(2)]
  | "Cselfdestruct" "(" Schedule "," BExp "," Int ")" [klabel(Cselfdestruct), strict(2)]
  rule <k> Ccall(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM)
          => Cextra(SCHED, ISEMPTY, VALUE, ISWARM) +Gas Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM)) ... </k>
  rule <k> Ccallgas(SCHED, ISEMPTY:Bool, GCAP, GAVAIL, VALUE, ISWARM)
          => Cgascap(SCHED, GCAP, GAVAIL, Cextra(SCHED, ISEMPTY, VALUE, ISWARM)) +Gas #if VALUE ==Int 0 #then 0 #else Gcallstipend < SCHED > #fi ... </k>
  rule <k> Cselfdestruct(SCHED, ISEMPTY:Bool, BAL)
          => Gselfdestruct < SCHED > +Int Cnew(SCHED, ISEMPTY andBool Gselfdestructnewaccount << SCHED >>, BAL) ... </k>
  syntax BExp  ::=
    Bool
  syntax KResult  ::=
    Bool
  syntax BExp  ::=
    "#accountNonexistent" "(" Int ")" [klabel(#accountNonexistent)]
  rule <k> #accountNonexistent(ACCT) => #accountEmpty(CODE, NONCE, BAL) andBool Gemptyisnonexistent << SCHED >> ... </k>
         <schedule> SCHED </schedule>
         <account>
           <acctID>  ACCT  </acctID>
           <balance> BAL   </balance>
           <nonce>   NONCE </nonce>
           <code>    CODE  </code>
           ...
         </account>
  rule <k> #accountNonexistent(_) => true ... </k>  [owise]
  syntax OpCode  ::=
    "#dasmOpCode" "(" Int "," Schedule ")" [function, klabel(#dasmOpCode), memo, total]
  rule #dasmOpCode(   0,     _ ) => STOP
  rule #dasmOpCode(   1,     _ ) => ADD
  rule #dasmOpCode(   2,     _ ) => MUL
  rule #dasmOpCode(   3,     _ ) => SUB
  rule #dasmOpCode(   4,     _ ) => DIV
  rule #dasmOpCode(   5,     _ ) => SDIV
  rule #dasmOpCode(   6,     _ ) => MOD
  rule #dasmOpCode(   7,     _ ) => SMOD
  rule #dasmOpCode(   8,     _ ) => ADDMOD
  rule #dasmOpCode(   9,     _ ) => MULMOD
  rule #dasmOpCode(  10,     _ ) => EXP
  rule #dasmOpCode(  11,     _ ) => SIGNEXTEND
  rule #dasmOpCode(  16,     _ ) => LT
  rule #dasmOpCode(  17,     _ ) => GT
  rule #dasmOpCode(  18,     _ ) => SLT
  rule #dasmOpCode(  19,     _ ) => SGT
  rule #dasmOpCode(  20,     _ ) => EQ
  rule #dasmOpCode(  21,     _ ) => ISZERO
  rule #dasmOpCode(  22,     _ ) => AND
  rule #dasmOpCode(  23,     _ ) => EVMOR
  rule #dasmOpCode(  24,     _ ) => XOR
  rule #dasmOpCode(  25,     _ ) => NOT
  rule #dasmOpCode(  26,     _ ) => BYTE
  rule #dasmOpCode(  27, SCHED ) => SHL requires Ghasshift << SCHED >>
  rule #dasmOpCode(  28, SCHED ) => SHR requires Ghasshift << SCHED >>
  rule #dasmOpCode(  29, SCHED ) => SAR requires Ghasshift << SCHED >>
  rule #dasmOpCode(  32,     _ ) => SHA3
  rule #dasmOpCode(  48,     _ ) => ADDRESS
  rule #dasmOpCode(  49,     _ ) => BALANCE
  rule #dasmOpCode(  50,     _ ) => ORIGIN
  rule #dasmOpCode(  51,     _ ) => CALLER
  rule #dasmOpCode(  52,     _ ) => CALLVALUE
  rule #dasmOpCode(  53,     _ ) => CALLDATALOAD
  rule #dasmOpCode(  54,     _ ) => CALLDATASIZE
  rule #dasmOpCode(  55,     _ ) => CALLDATACOPY
  rule #dasmOpCode(  56,     _ ) => CODESIZE
  rule #dasmOpCode(  57,     _ ) => CODECOPY
  rule #dasmOpCode(  58,     _ ) => GASPRICE
  rule #dasmOpCode(  59,     _ ) => EXTCODESIZE
  rule #dasmOpCode(  60,     _ ) => EXTCODECOPY
  rule #dasmOpCode(  61, SCHED ) => RETURNDATASIZE requires Ghasreturndata  << SCHED >>
  rule #dasmOpCode(  62, SCHED ) => RETURNDATACOPY requires Ghasreturndata  << SCHED >>
  rule #dasmOpCode(  63, SCHED ) => EXTCODEHASH    requires Ghasextcodehash << SCHED >>
  rule #dasmOpCode(  64,     _ ) => BLOCKHASH
  rule #dasmOpCode(  65,     _ ) => COINBASE
  rule #dasmOpCode(  66,     _ ) => TIMESTAMP
  rule #dasmOpCode(  67,     _ ) => NUMBER
  rule #dasmOpCode(  68, SCHED ) => PREVRANDAO  requires         Ghasprevrandao << SCHED >>
  rule #dasmOpCode(  68, SCHED ) => DIFFICULTY  requires notBool Ghasprevrandao << SCHED >>
  rule #dasmOpCode(  69,     _ ) => GASLIMIT
  rule #dasmOpCode(  70, SCHED ) => CHAINID     requires Ghaschainid     << SCHED >>
  rule #dasmOpCode(  71, SCHED ) => SELFBALANCE requires Ghasselfbalance << SCHED >>
  rule #dasmOpCode(  72, SCHED ) => BASEFEE     requires Ghasbasefee     << SCHED >>
  rule #dasmOpCode(  80,     _ ) => POP
  rule #dasmOpCode(  81,     _ ) => MLOAD
  rule #dasmOpCode(  82,     _ ) => MSTORE
  rule #dasmOpCode(  83,     _ ) => MSTORE8
  rule #dasmOpCode(  84,     _ ) => SLOAD
  rule #dasmOpCode(  85,     _ ) => SSTORE
  rule #dasmOpCode(  86,     _ ) => JUMP
  rule #dasmOpCode(  87,     _ ) => JUMPI
  rule #dasmOpCode(  88,     _ ) => PC
  rule #dasmOpCode(  89,     _ ) => MSIZE
  rule #dasmOpCode(  90,     _ ) => GAS
  rule #dasmOpCode(  91,     _ ) => JUMPDEST
  rule #dasmOpCode(  96,     _ ) => PUSH(1)
  rule #dasmOpCode(  97,     _ ) => PUSH(2)
  rule #dasmOpCode(  98,     _ ) => PUSH(3)
  rule #dasmOpCode(  99,     _ ) => PUSH(4)
  rule #dasmOpCode( 100,     _ ) => PUSH(5)
  rule #dasmOpCode( 101,     _ ) => PUSH(6)
  rule #dasmOpCode( 102,     _ ) => PUSH(7)
  rule #dasmOpCode( 103,     _ ) => PUSH(8)
  rule #dasmOpCode( 104,     _ ) => PUSH(9)
  rule #dasmOpCode( 105,     _ ) => PUSH(10)
  rule #dasmOpCode( 106,     _ ) => PUSH(11)
  rule #dasmOpCode( 107,     _ ) => PUSH(12)
  rule #dasmOpCode( 108,     _ ) => PUSH(13)
  rule #dasmOpCode( 109,     _ ) => PUSH(14)
  rule #dasmOpCode( 110,     _ ) => PUSH(15)
  rule #dasmOpCode( 111,     _ ) => PUSH(16)
  rule #dasmOpCode( 112,     _ ) => PUSH(17)
  rule #dasmOpCode( 113,     _ ) => PUSH(18)
  rule #dasmOpCode( 114,     _ ) => PUSH(19)
  rule #dasmOpCode( 115,     _ ) => PUSH(20)
  rule #dasmOpCode( 116,     _ ) => PUSH(21)
  rule #dasmOpCode( 117,     _ ) => PUSH(22)
  rule #dasmOpCode( 118,     _ ) => PUSH(23)
  rule #dasmOpCode( 119,     _ ) => PUSH(24)
  rule #dasmOpCode( 120,     _ ) => PUSH(25)
  rule #dasmOpCode( 121,     _ ) => PUSH(26)
  rule #dasmOpCode( 122,     _ ) => PUSH(27)
  rule #dasmOpCode( 123,     _ ) => PUSH(28)
  rule #dasmOpCode( 124,     _ ) => PUSH(29)
  rule #dasmOpCode( 125,     _ ) => PUSH(30)
  rule #dasmOpCode( 126,     _ ) => PUSH(31)
  rule #dasmOpCode( 127,     _ ) => PUSH(32)
  rule #dasmOpCode( 128,     _ ) => DUP(1)
  rule #dasmOpCode( 129,     _ ) => DUP(2)
  rule #dasmOpCode( 130,     _ ) => DUP(3)
  rule #dasmOpCode( 131,     _ ) => DUP(4)
  rule #dasmOpCode( 132,     _ ) => DUP(5)
  rule #dasmOpCode( 133,     _ ) => DUP(6)
  rule #dasmOpCode( 134,     _ ) => DUP(7)
  rule #dasmOpCode( 135,     _ ) => DUP(8)
  rule #dasmOpCode( 136,     _ ) => DUP(9)
  rule #dasmOpCode( 137,     _ ) => DUP(10)
  rule #dasmOpCode( 138,     _ ) => DUP(11)
  rule #dasmOpCode( 139,     _ ) => DUP(12)
  rule #dasmOpCode( 140,     _ ) => DUP(13)
  rule #dasmOpCode( 141,     _ ) => DUP(14)
  rule #dasmOpCode( 142,     _ ) => DUP(15)
  rule #dasmOpCode( 143,     _ ) => DUP(16)
  rule #dasmOpCode( 144,     _ ) => SWAP(1)
  rule #dasmOpCode( 145,     _ ) => SWAP(2)
  rule #dasmOpCode( 146,     _ ) => SWAP(3)
  rule #dasmOpCode( 147,     _ ) => SWAP(4)
  rule #dasmOpCode( 148,     _ ) => SWAP(5)
  rule #dasmOpCode( 149,     _ ) => SWAP(6)
  rule #dasmOpCode( 150,     _ ) => SWAP(7)
  rule #dasmOpCode( 151,     _ ) => SWAP(8)
  rule #dasmOpCode( 152,     _ ) => SWAP(9)
  rule #dasmOpCode( 153,     _ ) => SWAP(10)
  rule #dasmOpCode( 154,     _ ) => SWAP(11)
  rule #dasmOpCode( 155,     _ ) => SWAP(12)
  rule #dasmOpCode( 156,     _ ) => SWAP(13)
  rule #dasmOpCode( 157,     _ ) => SWAP(14)
  rule #dasmOpCode( 158,     _ ) => SWAP(15)
  rule #dasmOpCode( 159,     _ ) => SWAP(16)
  rule #dasmOpCode( 160,     _ ) => LOG(0)
  rule #dasmOpCode( 161,     _ ) => LOG(1)
  rule #dasmOpCode( 162,     _ ) => LOG(2)
  rule #dasmOpCode( 163,     _ ) => LOG(3)
  rule #dasmOpCode( 164,     _ ) => LOG(4)
  rule #dasmOpCode( 240,     _ ) => CREATE
  rule #dasmOpCode( 241,     _ ) => CALL
  rule #dasmOpCode( 242,     _ ) => CALLCODE
  rule #dasmOpCode( 243,     _ ) => RETURN
  rule #dasmOpCode( 244, SCHED ) => DELEGATECALL requires SCHED =/=K FRONTIER
  rule #dasmOpCode( 245, SCHED ) => CREATE2      requires Ghascreate2    << SCHED >>
  rule #dasmOpCode( 250, SCHED ) => STATICCALL   requires Ghasstaticcall << SCHED >>
  rule #dasmOpCode( 253, SCHED ) => REVERT       requires Ghasrevert     << SCHED >>
  rule #dasmOpCode( 254,     _ ) => INVALID
  rule #dasmOpCode( 255,     _ ) => SELFDESTRUCT
  rule #dasmOpCode(   W,     _ ) => UNDEFINED(W)  [owise]
endmodule

module INT-SIMPLIFICATION
  imports public INT-SIMPLIFICATION-HASKELL
endmodule

module INT-SIMPLIFICATION-HASKELL [kore, symbolic]
  imports public INT-SIMPLIFICATION-COMMON
  rule A +Int B => B +Int A  [concrete(A), simplification(40), symbolic(B)]
  rule A +Int (B +Int C) => (A +Int B) +Int C  [simplification(40), symbolic(A, B)]
  rule A +Int (B -Int C) => (A +Int B) -Int C  [simplification(40), symbolic(A, B)]
  rule A -Int (B +Int C) => (A -Int B) -Int C  [simplification(40), symbolic(A, B)]
  rule A -Int (B -Int C) => (A -Int B) +Int C  [simplification(40), symbolic(A, B)]
  rule A +Int (B -Int C) => (A -Int C) +Int B  [concrete(B), simplification(40), symbolic(A, C)]
  rule A -Int (B -Int C) => (A +Int C) -Int B  [concrete(B), simplification(40), symbolic(A, C)]
  rule (A +Int B) +Int C => (A +Int C) +Int B  [concrete(B), simplification(40), symbolic(C)]
  rule (A +Int B) -Int C => (A -Int C) +Int B  [concrete(B), simplification(40), symbolic(C)]
  rule (A -Int B) +Int C => (A +Int C) -Int B  [concrete(B), simplification(40), symbolic(C)]
  rule (A -Int B) -Int C => (A -Int C) -Int B  [concrete(B), simplification(40), symbolic(C)]
  rule (A +Int B) +Int C => A +Int (B +Int C)  [concrete(B, C), simplification(40), symbolic(A)]
  rule (A +Int B) -Int C => A +Int (B -Int C)  [concrete(B, C), simplification(40), symbolic(A)]
  rule (A -Int B) +Int C => A +Int (C -Int B)  [concrete(B, C), simplification(40), symbolic(A)]
  rule (A -Int B) -Int C => A -Int (B +Int C)  [concrete(B, C), simplification(40), symbolic(A)]
  rule A +Int B  <Int C        => A         <Int C -Int B  [concrete(B), simplification(40)]
  rule A         <Int B +Int C => A -Int C  <Int B         [concrete(A, C), simplification(40)]
  rule A        <=Int B +Int C => A -Int C <=Int B         [concrete(A, C), simplification(40)]
  rule A -Int B  <Int C        => A -Int C  <Int B         [concrete(A, C), simplification(40)]
  rule A        <=Int B -Int C => C        <=Int B -Int A  [concrete(A, B), simplification(40)]
endmodule

module INT-SIMPLIFICATION-COMMON
  imports public INT
  imports public BOOL
  imports public EVM-TYPES
  rule A -Int A => 0  [simplification]
  rule A -Int 0 => A  [simplification]
  rule 0 +Int A => A  [simplification]
  rule A +Int 0 => A  [simplification]
  rule (A -Int  B) +Int B  => A  [simplification]
  rule A -Int (A  -Int B) => B  [simplification]
  rule A +Int (B  -Int A) => B  [simplification]
  rule (A +Int  B) -Int A  => B  [simplification]
  rule (A +Int B) +Int (C  -Int A) => B +Int C  [simplification]
  rule (A +Int B) -Int (A  +Int C) => B -Int C  [simplification]
  rule (A +Int B) -Int (C  +Int A) => B -Int C  [simplification]
  rule (A +Int B) +Int (C  -Int B) => A +Int C  [simplification]
  rule ((A -Int B) -Int  C) +Int B  => A -Int C  [simplification]
  rule (A +Int  B  +Int C)  -Int (A  +Int D) =>  B +Int (C  -Int D)  [simplification]
  rule (C +Int (A  -Int D)) +Int (B  -Int A) =>  C +Int (B  -Int D)  [simplification]
  rule (((A -Int  B) -Int C)  -Int  D) +Int B  => (A -Int  C) -Int D   [simplification]
  rule 1 *Int A => A  [simplification]
  rule A *Int 1 => A  [simplification]
  rule 0 *Int _ => 0  [simplification]
  rule _ *Int 0 => 0  [simplification]
  rule (A *Int C) +Int (B *Int C) => (A +Int B) *Int C  [simplification]
  rule (A *Int C) -Int (B *Int C) => (A -Int B) *Int C  [simplification]
  rule (E *Int A) +Int B +Int C +Int D +Int (F *Int A) => ((E +Int F) *Int A) +Int B +Int C +Int D  [simplification]
  rule A /Int 1 => A   [simplification]
  rule (A *Int B) /Int A => B requires A =/=Int 0  [simplification]
  rule ((A *Int B) /Int C) /Int B => A /Int C requires B =/=Int 0  [simplification]
  rule (A /Int 32) *Int 32 => A requires A modInt 32 ==Int 0  [simplification]
  rule (A *Int B) /Int C <=Int D => true requires 0 <=Int A andBool 0 <=Int B andBool 0 <Int C andBool A <=Int D andBool B <=Int C  [simplification]
  rule A modInt B => A requires 0 <=Int A andBool A <Int B  [simplification]
  rule [minint-left]: minInt(A, B) => A requires A <=Int B  [simplification]
  rule [minint-right]: minInt(A, B) => B requires B <=Int A  [simplification]
  rule [minint-lt]: minInt(A, B)  <Int C => A  <Int C  orBool B  <Int C  [simplification]
  rule [minint-leq]: minInt(A, B) <=Int C => A <=Int C  orBool B <=Int C  [simplification]
  rule [minint-gt]: A  <Int minInt(B, C) => A  <Int B andBool A  <Int C  [simplification]
  rule [minint-geq]: A <=Int minInt(B, C) => A <=Int B andBool A <=Int C  [simplification]
  rule [minInt-factor-left]: minInt ( A:Int +Int B:Int, A:Int +Int C:Int ) => A +Int minInt ( B, C )  [simplification]
  rule [minInt-factor-right]: minInt ( A:Int +Int B:Int, C:Int +Int B:Int ) => minInt ( A, C ) +Int B  [simplification]
  rule [maxint-left]: maxInt(A:Int, B:Int) => B requires A <=Int B  [simplification]
  rule [maxint-right]: maxInt(A:Int, B:Int) => A requires B <=Int A  [simplification]
  rule [maxint-lt]: maxInt(A:Int, B:Int)  <Int C:Int => A  <Int C andBool B  <Int C  [simplification]
  rule [maxint-leq]: maxInt(A:Int, B:Int) <=Int C:Int => A <=Int C andBool B <=Int C  [simplification]
  rule [maxint-gt]: A:Int  <Int maxInt(B:Int, C:Int) => A  <Int B  orBool A  <Int C  [simplification]
  rule [maxint-geq]: A:Int <=Int maxInt(B:Int, C:Int) => A <=Int B  orBool A <=Int C  [simplification]
  rule [maxInt-factor-left]: maxInt ( A:Int +Int B:Int, A:Int +Int C:Int ) => A +Int maxInt ( B, C )  [simplification]
  rule [maxInt-factor-right]: maxInt ( A:Int +Int B:Int, C:Int +Int B:Int ) => maxInt ( A, C ) +Int B  [simplification]
  rule A +Int B <Int A => false requires 0 <=Int B  [simplification]
  rule A +Int B <Int B => false requires 0 <=Int A  [simplification]
  rule A <Int A -Int B => false requires 0 <=Int B  [simplification]
  rule 0 <Int 1 <<Int A => true requires 0 <=Int A  [simplification]
  rule A  >Int B  => B  <Int A  [simplification]
  rule A >=Int B  => B <=Int A  [simplification]
  rule notBool (A  <Int B) => B <=Int A  [simplification]
  rule notBool (A <=Int B) => B  <Int A  [simplification]
  rule 0 <=Int A *Int B => true requires 0 <=Int A andBool 0 <=Int B  [simplification]
  rule A -Int B +Int C <=Int D => false requires D <Int A -Int B andBool 0 <=Int C  [simplification]
  rule [upInt-lt-true]: ((X up/Int Y) *Int Y) <Int Z => true
      requires X +Int Y <=Int Z andBool 0 <Int Y
       [simplification]
  rule [upInt-lt-false]: ((X up/Int Y) *Int Y) <Int Z => false
      requires Z <=Int X andBool 0 <Int Y
       [simplification]
  rule [upInt-refl-leq]: ((X up/Int Y) *Int Y) <=Int X => X modInt Y ==Int 0
      requires 0 <Int Y
       [simplification]
  rule [upInt-refl-gt]: X <Int ((X up/Int Y) *Int Y) => X modInt Y =/=Int 0
      requires 0 <Int Y
       [simplification]
  rule [upInt-refl-geq]: X <=Int ((X up/Int Y) *Int Y) => true
      requires 0 <Int Y
       [simplification]
  rule [upInt-ref-eq]: X ==Int ((X up/Int Y) *Int Y) => X modInt Y ==Int 0
      requires 0 <Int Y
       [comm, simplification]
  rule [upInt-refl-neq]: X =/=Int ((X up/Int Y) *Int Y) => X modInt Y =/=Int 0
      requires 0 <Int Y
       [comm, simplification]
endmodule

module EVM-OPTIMIZATIONS-LEMMAS [kore, symbolic]
  imports public EVM
  rule #sizeWordStack(WS           , N) => #sizeWordStack(WS, 0) +Int N requires N =/=Int 0                 [simplification]
  rule #sizeWordStack(WS [ I := _ ], N) => #sizeWordStack(WS, N)        requires I <Int #sizeWordStack(WS)  [simplification]
  rule 0 <=Int #sizeWordStack(_ , 0)    => true                                                             [simplification]
  rule #sizeWordStack(_ , 0) <Int N     => false                        requires N <=Int 0                  [simplification]
endmodule

module EVM-OPTIMIZATIONS [kore]
  imports public EVM
  imports public EVM-OPTIMIZATIONS-LEMMAS
  imports public INT-SIMPLIFICATION
  rule <kevm>
       <k>
         ( #next[ PUSH(N) ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <program>
               PGM
             </program>
             <wordStack>
               ( WS => #asWord( #range(PGM, PCOUNT +Int 1, N) ) : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( ( PCOUNT +Int N ) +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( #asWord( #range(PGM, PCOUNT +Int 1, N) ) : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ DUP(N) ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( WS => WS [ ( N +Int -1 ) ] : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires #stackNeeded(DUP(N)) <=Int #sizeWordStack(WS)
   andBool ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( WS [ ( N +Int -1 ) ] : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ SWAP(N) ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : WS => WS [ ( N +Int -1 ) ] : ( WS [ ( N +Int -1 ) := W0 ] ) )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires #stackNeeded(SWAP(N)) <=Int #sizeWordStack(W0 : WS)
   andBool ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( WS [ ( N +Int -1 ) ] : ( WS [ ( N +Int -1 ) := W0 ] ) ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ ADD ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : W1 : WS => chop( ( W0 +Int W1 ) ) : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( chop( ( W0 +Int W1 ) ) : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ SUB ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : W1 : WS => chop( ( W0 -Int W1 ) ) : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( chop( ( W0 -Int W1 ) ) : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ AND ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : W1 : WS => W0 &Int W1 : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( W0 &Int W1 : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ LT ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : W1 : WS => bool2Word( W0 <Int W1 ) : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( bool2Word( W0 <Int W1 ) : WS ) <=Int 1024 )
     [priority(40)]
  rule <kevm>
       <k>
         ( #next[ GT ] => . ) ...
       </k>
       <schedule>
         SCHED
       </schedule>
       <ethereum>
         <evm>
           <callState>
             <wordStack>
               ( W0 : W1 : WS => bool2Word( W1 <Int W0 ) : WS )
             </wordStack>
             <pc>
               ( PCOUNT => ( PCOUNT +Int 1 ) )
             </pc>
             <gas>
               ( GAVAIL => ( GAVAIL -Gas Gverylow < SCHED > ) )
             </gas>
             ...
           </callState>
           ...
         </evm>
         ...
       </ethereum>
       ...
     </kevm>
  requires ( Gverylow < SCHED > <=Gas GAVAIL )
   andBool ( #sizeWordStack( bool2Word( W1 <Int W0 ) : WS ) <=Int 1024 )
     [priority(40)]
endmodule

module EVM-ASSEMBLY
  imports public EVM
  syntax OpCode  ::=
    "PUSH" "(" Int "," Int ")" [klabel(PUSHAsm)]
  syntax OpCodes  ::=
    ".OpCodes"
  | OpCode ";" OpCodes
  syntax OpCodes  ::=
    "#revOps" "(" OpCodes ")" [function, klabel(#revOps)]
  | "#revOpsAux" "(" OpCodes "," OpCodes ")" [function, klabel(#revOpsAux)]
  rule #revOps(OPS) => #revOpsAux(OPS, .OpCodes)
  rule #revOpsAux( .OpCodes , OPS' ) => OPS'
  rule #revOpsAux( OP ; OPS , OPS' ) => #revOpsAux( OPS , OP ; OPS' )
  syntax Bytes  ::=
    "#asmOpCodes" "(" OpCodes ")" [function, klabel(#asmOpCodes)]
  syntax Bytes  ::=
    "#asmOpCodes" "(" OpCodes "," StringBuffer ")" [function, klabel(#asmOpCodesAux)]
  rule #asmOpCodes( OPS ) => #asmOpCodes(OPS, .StringBuffer)
  rule #asmOpCodes( PUSH(N, W) ; OCS, SB ) => #asmOpCodes(OCS, (SB +String chrChar(#asmOpCode(PUSH(N)))) +String Bytes2String(Int2Bytes(N, W, BE)))
  rule #asmOpCodes( OP ; OCS, SB ) => #asmOpCodes(OCS, SB +String chrChar(#asmOpCode(OP)))  [owise]
  rule #asmOpCodes( .OpCodes, SB ) => String2Bytes(StringBuffer2String(SB))
  syntax Int  ::=
    "#asmOpCode" "(" OpCode ")" [function, klabel(#asmOpCode)]
  rule #asmOpCode( STOP           ) =>   0
  rule #asmOpCode( ADD            ) =>   1
  rule #asmOpCode( MUL            ) =>   2
  rule #asmOpCode( SUB            ) =>   3
  rule #asmOpCode( DIV            ) =>   4
  rule #asmOpCode( SDIV           ) =>   5
  rule #asmOpCode( MOD            ) =>   6
  rule #asmOpCode( SMOD           ) =>   7
  rule #asmOpCode( ADDMOD         ) =>   8
  rule #asmOpCode( MULMOD         ) =>   9
  rule #asmOpCode( EXP            ) =>  10
  rule #asmOpCode( SIGNEXTEND     ) =>  11
  rule #asmOpCode( LT             ) =>  16
  rule #asmOpCode( GT             ) =>  17
  rule #asmOpCode( SLT            ) =>  18
  rule #asmOpCode( SGT            ) =>  19
  rule #asmOpCode( EQ             ) =>  20
  rule #asmOpCode( ISZERO         ) =>  21
  rule #asmOpCode( AND            ) =>  22
  rule #asmOpCode( EVMOR          ) =>  23
  rule #asmOpCode( XOR            ) =>  24
  rule #asmOpCode( NOT            ) =>  25
  rule #asmOpCode( BYTE           ) =>  26
  rule #asmOpCode( SHL            ) =>  27
  rule #asmOpCode( SHR            ) =>  28
  rule #asmOpCode( SAR            ) =>  29
  rule #asmOpCode( SHA3           ) =>  32
  rule #asmOpCode( ADDRESS        ) =>  48
  rule #asmOpCode( BALANCE        ) =>  49
  rule #asmOpCode( ORIGIN         ) =>  50
  rule #asmOpCode( CALLER         ) =>  51
  rule #asmOpCode( CALLVALUE      ) =>  52
  rule #asmOpCode( CALLDATALOAD   ) =>  53
  rule #asmOpCode( CALLDATASIZE   ) =>  54
  rule #asmOpCode( CALLDATACOPY   ) =>  55
  rule #asmOpCode( CODESIZE       ) =>  56
  rule #asmOpCode( CODECOPY       ) =>  57
  rule #asmOpCode( GASPRICE       ) =>  58
  rule #asmOpCode( EXTCODESIZE    ) =>  59
  rule #asmOpCode( EXTCODECOPY    ) =>  60
  rule #asmOpCode( RETURNDATASIZE ) =>  61
  rule #asmOpCode( RETURNDATACOPY ) =>  62
  rule #asmOpCode( EXTCODEHASH    ) =>  63
  rule #asmOpCode( BLOCKHASH      ) =>  64
  rule #asmOpCode( COINBASE       ) =>  65
  rule #asmOpCode( TIMESTAMP      ) =>  66
  rule #asmOpCode( NUMBER         ) =>  67
  rule #asmOpCode( DIFFICULTY     ) =>  68
  rule #asmOpCode( PREVRANDAO     ) =>  68
  rule #asmOpCode( GASLIMIT       ) =>  69
  rule #asmOpCode( CHAINID        ) =>  70
  rule #asmOpCode( SELFBALANCE    ) =>  71
  rule #asmOpCode( POP            ) =>  80
  rule #asmOpCode( MLOAD          ) =>  81
  rule #asmOpCode( MSTORE         ) =>  82
  rule #asmOpCode( MSTORE8        ) =>  83
  rule #asmOpCode( SLOAD          ) =>  84
  rule #asmOpCode( SSTORE         ) =>  85
  rule #asmOpCode( JUMP           ) =>  86
  rule #asmOpCode( JUMPI          ) =>  87
  rule #asmOpCode( PC             ) =>  88
  rule #asmOpCode( MSIZE          ) =>  89
  rule #asmOpCode( GAS            ) =>  90
  rule #asmOpCode( JUMPDEST       ) =>  91
  rule #asmOpCode( PUSH(1)        ) =>  96
  rule #asmOpCode( PUSH(2)        ) =>  97
  rule #asmOpCode( PUSH(3)        ) =>  98
  rule #asmOpCode( PUSH(4)        ) =>  99
  rule #asmOpCode( PUSH(5)        ) => 100
  rule #asmOpCode( PUSH(6)        ) => 101
  rule #asmOpCode( PUSH(7)        ) => 102
  rule #asmOpCode( PUSH(8)        ) => 103
  rule #asmOpCode( PUSH(9)        ) => 104
  rule #asmOpCode( PUSH(10)       ) => 105
  rule #asmOpCode( PUSH(11)       ) => 106
  rule #asmOpCode( PUSH(12)       ) => 107
  rule #asmOpCode( PUSH(13)       ) => 108
  rule #asmOpCode( PUSH(14)       ) => 109
  rule #asmOpCode( PUSH(15)       ) => 110
  rule #asmOpCode( PUSH(16)       ) => 111
  rule #asmOpCode( PUSH(17)       ) => 112
  rule #asmOpCode( PUSH(18)       ) => 113
  rule #asmOpCode( PUSH(19)       ) => 114
  rule #asmOpCode( PUSH(20)       ) => 115
  rule #asmOpCode( PUSH(21)       ) => 116
  rule #asmOpCode( PUSH(22)       ) => 117
  rule #asmOpCode( PUSH(23)       ) => 118
  rule #asmOpCode( PUSH(24)       ) => 119
  rule #asmOpCode( PUSH(25)       ) => 120
  rule #asmOpCode( PUSH(26)       ) => 121
  rule #asmOpCode( PUSH(27)       ) => 122
  rule #asmOpCode( PUSH(28)       ) => 123
  rule #asmOpCode( PUSH(29)       ) => 124
  rule #asmOpCode( PUSH(30)       ) => 125
  rule #asmOpCode( PUSH(31)       ) => 126
  rule #asmOpCode( PUSH(32)       ) => 127
  rule #asmOpCode( DUP(1)         ) => 128
  rule #asmOpCode( DUP(2)         ) => 129
  rule #asmOpCode( DUP(3)         ) => 130
  rule #asmOpCode( DUP(4)         ) => 131
  rule #asmOpCode( DUP(5)         ) => 132
  rule #asmOpCode( DUP(6)         ) => 133
  rule #asmOpCode( DUP(7)         ) => 134
  rule #asmOpCode( DUP(8)         ) => 135
  rule #asmOpCode( DUP(9)         ) => 136
  rule #asmOpCode( DUP(10)        ) => 137
  rule #asmOpCode( DUP(11)        ) => 138
  rule #asmOpCode( DUP(12)        ) => 139
  rule #asmOpCode( DUP(13)        ) => 140
  rule #asmOpCode( DUP(14)        ) => 141
  rule #asmOpCode( DUP(15)        ) => 142
  rule #asmOpCode( DUP(16)        ) => 143
  rule #asmOpCode( SWAP(1)        ) => 144
  rule #asmOpCode( SWAP(2)        ) => 145
  rule #asmOpCode( SWAP(3)        ) => 146
  rule #asmOpCode( SWAP(4)        ) => 147
  rule #asmOpCode( SWAP(5)        ) => 148
  rule #asmOpCode( SWAP(6)        ) => 149
  rule #asmOpCode( SWAP(7)        ) => 150
  rule #asmOpCode( SWAP(8)        ) => 151
  rule #asmOpCode( SWAP(9)        ) => 152
  rule #asmOpCode( SWAP(10)       ) => 153
  rule #asmOpCode( SWAP(11)       ) => 154
  rule #asmOpCode( SWAP(12)       ) => 155
  rule #asmOpCode( SWAP(13)       ) => 156
  rule #asmOpCode( SWAP(14)       ) => 157
  rule #asmOpCode( SWAP(15)       ) => 158
  rule #asmOpCode( SWAP(16)       ) => 159
  rule #asmOpCode( LOG(0)         ) => 160
  rule #asmOpCode( LOG(1)         ) => 161
  rule #asmOpCode( LOG(2)         ) => 162
  rule #asmOpCode( LOG(3)         ) => 163
  rule #asmOpCode( LOG(4)         ) => 164
  rule #asmOpCode( CREATE         ) => 240
  rule #asmOpCode( CALL           ) => 241
  rule #asmOpCode( CALLCODE       ) => 242
  rule #asmOpCode( RETURN         ) => 243
  rule #asmOpCode( DELEGATECALL   ) => 244
  rule #asmOpCode( CREATE2        ) => 245
  rule #asmOpCode( STATICCALL     ) => 250
  rule #asmOpCode( REVERT         ) => 253
  rule #asmOpCode( INVALID        ) => 254
  rule #asmOpCode( SELFDESTRUCT   ) => 255
  rule #asmOpCode( UNDEFINED(W)   ) =>   W
endmodule

module STATE-UTILS
  imports public EVM
  imports public EVM-ASSEMBLY
  syntax JSON  ::=
    Bytes
  | OpCodes
  | Map
  | SubstateLogEntry
  | Account
  syntax EthereumCommand  ::=
    "clear"
  rule <k> clear => clearTX ~> clearBLOCK ~> clearNETWORK ... </k>
  syntax EthereumCommand  ::=
    "clearTX"
  rule <k> clearTX => . ... </k>
         <output>           _ => .Bytes     </output>
         <memoryUsed>       _ => 0          </memoryUsed>
         <callDepth>        _ => 0          </callDepth>
         <callStack>        _ => .List      </callStack>
         <program>          _ => .Bytes     </program>
         <jumpDests>        _ => .Set       </jumpDests>
         <id>               _ => .Account   </id>
         <caller>           _ => .Account   </caller>
         <callData>         _ => .Bytes     </callData>
         <callValue>        _ => 0          </callValue>
         <wordStack>        _ => .WordStack </wordStack>
         <localMem>         _ => .Bytes     </localMem>
         <pc>               _ => 0          </pc>
         <gas>              _ => 0          </gas>
         <callGas>          _ => 0          </callGas>
         <selfDestruct>     _ => .Set       </selfDestruct>
         <log>              _ => .List      </log>
         <refund>           _ => 0          </refund>
         <gasPrice>         _ => 0          </gasPrice>
         <origin>           _ => .Account   </origin>
         <touchedAccounts>  _ => .Set       </touchedAccounts>
         <accessedAccounts> _ => .Set       </accessedAccounts>
  syntax EthereumCommand  ::=
    "clearBLOCK"
  rule <k> clearBLOCK => . ... </k>
         <previousHash>      _ => 0          </previousHash>
         <ommersHash>        _ => 0          </ommersHash>
         <coinbase>          _ => 0          </coinbase>
         <stateRoot>         _ => 0          </stateRoot>
         <transactionsRoot>  _ => 0          </transactionsRoot>
         <receiptsRoot>      _ => 0          </receiptsRoot>
         <logsBloom>         _ => .Bytes     </logsBloom>
         <difficulty>        _ => 0          </difficulty>
         <number>            _ => 0          </number>
         <gasLimit>          _ => 0          </gasLimit>
         <gasUsed>           _ => 0          </gasUsed>
         <timestamp>         _ => 0          </timestamp>
         <extraData>         _ => .Bytes     </extraData>
         <mixHash>           _ => 0          </mixHash>
         <blockNonce>        _ => 0          </blockNonce>
         <ommerBlockHeaders> _ => [ .JSONs ] </ommerBlockHeaders>
         <blockhashes>       _ => .List      </blockhashes>
         <baseFee>           _ => 0          </baseFee>
  syntax EthereumCommand  ::=
    "clearNETWORK"
  rule <k> clearNETWORK => . ... </k>
         <statusCode>     _ => .StatusCode </statusCode>
         <accounts>       _ => .Bag        </accounts>
         <messages>       _ => .Bag        </messages>
         <schedule>       _ => DEFAULT     </schedule>
  syntax EthereumCommand  ::=
    "mkAcct" Int
  rule <k> mkAcct ACCT => #newAccount ACCT ... </k>
  syntax EthereumCommand  ::=
    "load" JSON
  rule <k> load _DATA : { .JSONs }             => .                                                   ... </k>
  rule <k> load  DATA : { KEY : VALUE , REST } => load DATA : { KEY : VALUE } ~> load DATA : { REST } ... </k>
      requires REST =/=K .JSONs andBool DATA =/=String "transaction"
  rule <k> load _DATA : [ .JSONs ]          => .                                            ... </k>
  rule <k> load  DATA : [ { TEST } , REST ] => load DATA : { TEST } ~> load DATA : [ REST ] ... </k>
  rule <k> load "pre" : { (ACCTID:String) : ACCT } => mkAcct #parseAddr(ACCTID) ~> loadAccount #parseAddr(ACCTID) ACCT ... </k>
  syntax EthereumCommand  ::=
    "loadAccount" Int JSON
  rule <k> loadAccount _ { .JSONs } => . ... </k>
  rule <k> loadAccount ACCT { "balance" : (BAL:Int), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <balance> _ => BAL </balance> ... </account>
  rule <k> loadAccount ACCT { "code" : (CODE:Bytes), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <code> _ => CODE </code> ... </account>
  rule <k> loadAccount ACCT { "nonce" : (NONCE:Int), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <nonce> _ => NONCE </nonce> ... </account>
  rule <k> loadAccount ACCT { "storage" : (STORAGE:Map), REST => REST } ... </k>
         <account> <acctID> ACCT </acctID> <origStorage> _ => STORAGE </origStorage> <storage> _ => STORAGE </storage> ... </account>
  rule <k> load "env" : { KEY : ((VAL:String) => #parseWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentTimestamp") SetItem("currentGasLimit") SetItem("currentNumber") SetItem("currentDifficulty") SetItem("currentBaseFee"))
  rule <k> load "env" : { KEY : ((VAL:String) => #parseHexWord(VAL)) } ... </k>
      requires KEY in (SetItem("currentCoinbase") SetItem("previousHash"))
  rule <k> load "env" : { "currentCoinbase"   : (CB:Int)     } => . ... </k> <coinbase>     _ => CB     </coinbase>
  rule <k> load "env" : { "currentDifficulty" : (DIFF:Int)   } => . ... </k> <difficulty>   _ => DIFF   </difficulty>
  rule <k> load "env" : { "currentGasLimit"   : (GLIMIT:Int) } => . ... </k> <gasLimit>     _ => GLIMIT </gasLimit>
  rule <k> load "env" : { "currentNumber"     : (NUM:Int)    } => . ... </k> <number>       _ => NUM    </number>
  rule <k> load "env" : { "previousHash"      : (HASH:Int)   } => . ... </k> <previousHash> _ => HASH   </previousHash>
  rule <k> load "env" : { "currentTimestamp"  : (TS:Int)     } => . ... </k> <timestamp>    _ => TS     </timestamp>
  rule <k> load "env" : { "currentBaseFee"    : (BF:Int)     } => . ... </k> <baseFee>      _ => BF     </baseFee>
  syntax KItem  ::=
    "loadCallState" JSON
  rule <k> loadCallState { "data" : ( DATA:String => #parseByteStack( DATA ) ), _REST } ... </k>
  rule <k> loadCallState { "code" : CODE:Bytes, REST } => #loadProgram CODE ~> loadCallState { REST } ... </k>
  rule <k> loadCallState { "gas"      : GLIMIT:Int, REST => REST } ... </k> <gas>       _ => GLIMIT </gas>
  rule <k> loadCallState { "gasPrice" : GPRICE:Int, REST => REST } ... </k> <gasPrice>  _ => GPRICE </gasPrice>
  rule <k> loadCallState { "value"    : VALUE:Int , REST => REST } ... </k> <callValue> _ => VALUE  </callValue>
  rule <k> loadCallState { "data"     : DATA:Bytes, REST => REST } ... </k> <callData>  _ => DATA   </callData>
  rule <k> loadCallState { .JSONs } => . ... </k>
  rule <k> load "network" : SCHEDSTRING => . ... </k>
         <schedule> _ => #asScheduleString(SCHEDSTRING) </schedule>
  syntax Schedule  ::=
    "#asScheduleString" "(" String ")" [function, klabel(#asScheduleString)]
  rule #asScheduleString("Frontier")          => FRONTIER
  rule #asScheduleString("Homestead")         => HOMESTEAD
  rule #asScheduleString("EIP150")            => TANGERINE_WHISTLE
  rule #asScheduleString("EIP158")            => SPURIOUS_DRAGON
  rule #asScheduleString("Byzantium")         => BYZANTIUM
  rule #asScheduleString("Constantinople")    => CONSTANTINOPLE
  rule #asScheduleString("ConstantinopleFix") => PETERSBURG
  rule #asScheduleString("Istanbul")          => ISTANBUL
  rule #asScheduleString("Berlin")            => BERLIN
  rule #asScheduleString("London")            => LONDON
  rule #asScheduleString("Merge")             => MERGE
  rule <k> load "rlp"        : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
  rule <k> load "genesisRLP" : (VAL:String => #rlpDecode(#unparseByteStack(#parseByteStack(VAL)))) ... </k>
  rule <k> load "rlp" : [ [ HP , HO , HC , HR , HT , HE , HB , HD , HI , HL , HG , HS , HX , HM , HN , .JSONs ] , BT , BU , .JSONs ]
          => load "transaction" : BT
         ...
         </k>
         <previousHash>      _ => #asWord(#parseByteStackRaw(HP)) </previousHash>
         <ommersHash>        _ => #asWord(#parseByteStackRaw(HO)) </ommersHash>
         <coinbase>          _ => #asWord(#parseByteStackRaw(HC)) </coinbase>
         <stateRoot>         _ => #asWord(#parseByteStackRaw(HR)) </stateRoot>
         <transactionsRoot>  _ => #asWord(#parseByteStackRaw(HT)) </transactionsRoot>
         <receiptsRoot>      _ => #asWord(#parseByteStackRaw(HE)) </receiptsRoot>
         <logsBloom>         _ => #parseByteStackRaw(HB)          </logsBloom>
         <difficulty>        _ => #asWord(#parseByteStackRaw(HD)) </difficulty>
         <number>            _ => #asWord(#parseByteStackRaw(HI)) </number>
         <gasLimit>          _ => #asWord(#parseByteStackRaw(HL)) </gasLimit>
         <gasUsed>           _ => #asWord(#parseByteStackRaw(HG)) </gasUsed>
         <timestamp>         _ => #asWord(#parseByteStackRaw(HS)) </timestamp>
         <extraData>         _ => #parseByteStackRaw(HX)          </extraData>
         <mixHash>           _ => #asWord(#parseByteStackRaw(HM)) </mixHash>
         <blockNonce>        _ => #asWord(#parseByteStackRaw(HN)) </blockNonce>
         <ommerBlockHeaders> _ => BU                              </ommerBlockHeaders>
  rule <k> load "rlp" : [ [ HP , HO , HC , HR , HT , HE , HB , HD , HI , HL , HG , HS , HX , HM , HN , HF , .JSONs ] , BT , BU , .JSONs ]
          => load "transaction" : BT
         ...
         </k>
         <previousHash>      _ => #asWord(#parseByteStackRaw(HP)) </previousHash>
         <ommersHash>        _ => #asWord(#parseByteStackRaw(HO)) </ommersHash>
         <coinbase>          _ => #asWord(#parseByteStackRaw(HC)) </coinbase>
         <stateRoot>         _ => #asWord(#parseByteStackRaw(HR)) </stateRoot>
         <transactionsRoot>  _ => #asWord(#parseByteStackRaw(HT)) </transactionsRoot>
         <receiptsRoot>      _ => #asWord(#parseByteStackRaw(HE)) </receiptsRoot>
         <logsBloom>         _ => #parseByteStackRaw(HB)          </logsBloom>
         <difficulty>        _ => #asWord(#parseByteStackRaw(HD)) </difficulty>
         <number>            _ => #asWord(#parseByteStackRaw(HI)) </number>
         <gasLimit>          _ => #asWord(#parseByteStackRaw(HL)) </gasLimit>
         <gasUsed>           _ => #asWord(#parseByteStackRaw(HG)) </gasUsed>
         <timestamp>         _ => #asWord(#parseByteStackRaw(HS)) </timestamp>
         <extraData>         _ => #parseByteStackRaw(HX)          </extraData>
         <mixHash>           _ => #asWord(#parseByteStackRaw(HM)) </mixHash>
         <blockNonce>        _ => #asWord(#parseByteStackRaw(HN)) </blockNonce>
         <baseFee>           _ => #asWord(#parseByteStackRaw(HF)) </baseFee>
         <ommerBlockHeaders> _ => BU                              </ommerBlockHeaders>
  rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:String, HB, HD, HI, HL, HG, HS, HX, HM, HN, .JSONs ], _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)) ListItem(#asWord(#parseByteStackRaw(HP))) ... </blockhashes>
  rule <k> load "genesisRLP": [ [ HP, HO, HC, HR, HT, HE:String, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF, .JSONs ], _, _, .JSONs ] => .K ... </k>
         <blockhashes> .List => ListItem(#blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF)) ListItem(#asWord(#parseByteStackRaw(HP))) ... </blockhashes>
  syntax EthereumCommand  ::=
    "mkTX" Int
  rule <k> mkTX TXID => . ... </k>
         <chainID> CID </chainID>
         <txOrder>   ... (.List => ListItem(TXID)) </txOrder>
         <txPending> ... (.List => ListItem(TXID)) </txPending>
         <messages>
            ( .Bag
           => <message>
                <msgID>      TXID:Int </msgID>
                <txGasPrice> 20000000000   </txGasPrice>
                <txGasLimit> 90000         </txGasLimit>
                <txChainID>  CID           </txChainID>
                ...
              </message>
            )
          ...
          </messages>
  rule <k> load "transaction" : [ (T => [#rlpDecodeTransaction(#parseByteStackRaw(T))]) , _ ] ... </k>
  rule <k> load "transaction" : [ [ TN , TP , TG , TT , TV , TI , TW , TR , TS ] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"  : TI   ,   "gasLimit" : TG   ,   "gasPrice"             : TP
                                 , "nonce" : TN   ,   "r"        : TR   ,   "s"                    : TS
                                 , "to"    : TT   ,   "v"        : TW   ,   "value"                : TV
                                 , "type"  : #dasmTxPrefix(Legacy)      ,   "maxPriorityFeePerGas" : TP
                                 , "maxFeePerGas": TP                   , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
          </k>
  rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TG, TT, TV, TI, TA, TY , TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"       : TI   ,   "gasLimit" : TG   ,   "gasPrice"  : TP
                                 , "nonce"      : TN   ,   "r"        : TR   ,   "s"         : TS
                                 , "to"         : TT   ,   "v"        : TY   ,   "value"     : TV
                                 , "accessList" : TA   ,   "type"     : TYPE ,   "chainID"   : TC
                                 , "maxPriorityFeePerGas" : TP               , "maxFeePerGas": TP
                                 , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(#parseByteStackRaw(TYPE)) ==Int #dasmTxPrefix(AccessList)
  rule <k> load "transaction" : [ [TYPE , [TC, TN, TP, TF, TG, TT, TV, TI, TA, TY , TR, TS ]] , REST ]
          => mkTX !ID:Int
          ~> loadTransaction !ID { "data"         : TI   ,   "gasLimit" : TG   ,   "maxPriorityFeePerGas" : TP
                                 , "nonce"        : TN   ,   "r"        : TR   ,   "s"                    : TS
                                 , "to"           : TT   ,   "v"        : TY   ,   "value"                : TV
                                 , "accessList"   : TA   ,   "type"     : TYPE ,   "chainID"              : TC
                                 , "maxFeePerGas" : TF   , .JSONs
                                 }
          ~> load "transaction" : [ REST ]
          ...
         </k>
    requires #asWord(#parseByteStackRaw(TYPE)) ==Int #dasmTxPrefix(DynamicFee)
  syntax EthereumCommand  ::=
    "loadTransaction" Int JSON
  rule <k> loadTransaction _ { .JSONs } => . ... </k>
  rule <k> loadTransaction TXID { GLIMIT : TG:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txGasLimit> _ => TG </txGasLimit> ... </message>
      requires GLIMIT in (SetItem("gas") SetItem("gasLimit"))
  rule <k> loadTransaction TXID { "gasPrice" : TP:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txGasPrice> _ => TP </txGasPrice> ... </message>
  rule <k> loadTransaction TXID { "nonce" : TN:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txNonce> _ => TN </txNonce> ... </message>
  rule <k> loadTransaction TXID { "value" : TV:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <value> _ => TV </value> ... </message>
  rule <k> loadTransaction TXID { "to" : TT:Account, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <to> _ => TT </to> ... </message>
  rule <k> loadTransaction TXID { "data" : TI:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <data> _ => TI </data> ... </message>
  rule <k> loadTransaction TXID { "v" : TW:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigV> _ => TW </sigV> ... </message>
  rule <k> loadTransaction TXID { "r" : TR:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigR> _ => TR </sigR> ... </message>
  rule <k> loadTransaction TXID { "s" : TS:Bytes, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <sigS> _ => TS </sigS> ... </message>
  rule <k> loadTransaction TXID { "type" : T:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txType> _ => #asmTxPrefix(T) </txType> ... </message>
  rule <k> loadTransaction TXID { "chainID" : TC:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txChainID> _ => TC </txChainID> ... </message>
  rule <k> loadTransaction TXID { "accessList" : [TA:JSONs], REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txAccess> _ => [TA] </txAccess> ... </message>
  rule <k> loadTransaction TXID { "maxPriorityFeePerGas" : TP:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txPriorityFee> _ => TP </txPriorityFee> ... </message>
  rule <k> loadTransaction TXID { "maxFeePerGas" : TF:Int, REST => REST } ... </k>
         <message> <msgID> TXID </msgID> <txMaxFee> _ => TF </txMaxFee> ... </message>
  syntax TxData  ::=
    "#getTxData" "(" Int ")" [function, klabel(#getTxData)]
  rule [[ #getTxData( TXID ) => LegacyTxData(TN, TP, TG, TT, TV, DATA) ]]
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <sigV>       TW   </sigV>
           <data>       DATA </data>
           <txType> Legacy </txType>
           ...
         </message>
      requires TW ==Int 0 orBool TW ==Int 1 orBool TW ==Int 27 orBool TW ==Int 28
  rule [[ #getTxData( TXID ) => LegacyProtectedTxData(TN, TP, TG, TT, TV, DATA, CID) ]]
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <sigV>       TW   </sigV>
           <data>       DATA </data>
           <txChainID>  CID  </txChainID>
           <txType> Legacy </txType>
           ...
         </message>
      requires notBool (TW ==Int 0 orBool TW ==Int 1 orBool TW ==Int 27 orBool TW ==Int 28)
  rule [[ #getTxData( TXID ) => AccessListTxData(TN, TP, TG, TT, TV, DATA, CID, TA) ]]
         <message>
           <msgID>      TXID </msgID>
           <txNonce>    TN   </txNonce>
           <txGasPrice> TP   </txGasPrice>
           <txGasLimit> TG   </txGasLimit>
           <to>         TT   </to>
           <value>      TV   </value>
           <data>       DATA </data>
           <txChainID>  CID  </txChainID>
           <txAccess>   TA   </txAccess>
           <txType> AccessList </txType>
           ...
         </message>
  rule [[ #getTxData( TXID ) => DynamicFeeTxData(TN, TPF, TM, TG, TT, TV, DATA, CID, TA) ]]
         <message>
           <msgID>         TXID </msgID>
           <txNonce>       TN   </txNonce>
           <txGasLimit>    TG   </txGasLimit>
           <to>            TT   </to>
           <value>         TV   </value>
           <data>          DATA </data>
           <txChainID>     CID  </txChainID>
           <txAccess>      TA   </txAccess>
           <txPriorityFee> TPF  </txPriorityFee>
           <txMaxFee>      TM   </txMaxFee>
           <txType> DynamicFee </txType>
           ...
         </message>
  syntax Int  ::=
    "#effectiveGasPrice" "(" Int ")" [function, klabel(#effectiveGasPrice)]
  rule [[ #effectiveGasPrice( TXID )
         => #if ( notBool Ghasbasefee << SCHED >> )
                orBool TXTYPE ==K Legacy
                orBool TXTYPE ==K AccessList
              #then GPRICE
              #else BFEE +Int minInt(TPF, TM -Int BFEE)
            #fi
         ]]
         <schedule> SCHED </schedule>
         <baseFee> BFEE </baseFee>
         <message>
           <msgID>         TXID   </msgID>
           <txGasPrice>    GPRICE </txGasPrice>
           <txType>        TXTYPE </txType>
           <txPriorityFee> TPF    </txPriorityFee>
           <txMaxFee>      TM     </txMaxFee>
           ...
         </message>
  syntax BlockIdentifier  ::=
    Int
  | "LATEST"
  | "PENDING"
  | "EARLIEST"
  syntax BlockIdentifier  ::=
    "#parseBlockIdentifier" "(" JSON ")" [function, klabel(#parseBlockIdentifier)]
  rule #parseBlockIdentifier(BLOCKNUM:Int) => BLOCKNUM
  rule #parseBlockIdentifier("pending")    => PENDING
  rule #parseBlockIdentifier("latest")     => LATEST
  rule #parseBlockIdentifier("earliest")   => EARLIEST
  rule #parseBlockIdentifier(BLOCKNUM)     => #parseWord(BLOCKNUM)  [owise]
endmodule

module ETHEREUM-SIMULATION
  imports public EVM
  imports public EVM-OPTIMIZATIONS
  imports public EVM-ASSEMBLY
  imports public STATE-UTILS
  syntax EthereumSimulation  ::=
    ".EthereumSimulation"
  | EthereumCommand EthereumSimulation
  rule <k> .EthereumSimulation                        => .          ... </k>
  rule <k> ETC                 .EthereumSimulation    => ETC        ... </k>
  rule <k> ETC                 ETS:EthereumSimulation => ETC ~> ETS ... </k> requires ETS =/=K .EthereumSimulation
  rule <k> #halt ~> ETC ETS:EthereumSimulation => #halt ~> ETC ~> ETS ... </k>
  syntax EthereumSimulation  ::=
    JSON
  rule <k> JSONINPUT:JSON => run JSONINPUT success .EthereumSimulation </k>
  syntax JSON  ::=
    Bytes
  | OpCodes
  | Map
  | SubstateLogEntry
  | Account
  | TxType
  syntax EthereumCommand  ::=
    "start"
  rule <mode> NORMAL  </mode> <k> start => #execute ... </k>
  rule <mode> VMTESTS </mode> <k> start => #execute ... </k>
  syntax EthereumCommand  ::=
    "flush"
  rule <mode> EXECMODE </mode> <statusCode> EVMC_SUCCESS            </statusCode> <k> #halt ~> flush => #finalizeTx(EXECMODE ==K VMTESTS)          ... </k>
  rule <mode> EXECMODE </mode> <statusCode> _:ExceptionalStatusCode </statusCode> <k> #halt ~> flush => #finalizeTx(EXECMODE ==K VMTESTS) ~> #halt ... </k>
  syntax EthereumCommand  ::=
    "startTx"
  rule <k> startTx => #finalizeBlock ... </k>
         <txPending> .List </txPending>
  rule <k> startTx => loadTx( #sender( #getTxData(TXID), TW, TR, TS ) ) ... </k>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <message>
           <msgID>      TXID </msgID>
           <sigV>       TW   </sigV>
           <sigR>       TR   </sigR>
           <sigS>       TS   </sigS>
           ...
         </message>
  syntax EthereumCommand  ::=
    "loadTx" "(" Account ")" [klabel(loadTx)]
  rule <k> loadTx(ACCTFROM)
          => #accessAccounts ACCTFROM #newAddr(ACCTFROM, NONCE) #precompiledAccounts(SCHED)
          ~> #loadAccessList(TA)
          ~> #create ACCTFROM #newAddr(ACCTFROM, NONCE) VALUE CODE
          ~> #finishTx ~> #finalizeTx(false) ~> startTx
         ...
         </k>
         <schedule> SCHED </schedule>
         <gasPrice> _ => #effectiveGasPrice(TXID) </gasPrice>
         <callGas> _ => GLIMIT -Int G0(SCHED, CODE, true) </callGas>
         <origin> _ => ACCTFROM </origin>
         <callDepth> _ => -1 </callDepth>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <coinbase> MINER </coinbase>
         <message>
           <msgID>      TXID     </msgID>
           <txGasLimit> GLIMIT   </txGasLimit>
           <to>         .Account </to>
           <value>      VALUE    </value>
           <data>       CODE     </data>
           <txAccess>   TA       </txAccess>
           ...
         </message>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL => BAL -Int (GLIMIT *Int #effectiveGasPrice(TXID)) </balance>
           <nonce> NONCE </nonce>
           ...
         </account>
         <accessedAccounts> _ => .Set </accessedAccounts>
         <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>
  rule <k> loadTx(ACCTFROM)
          => #accessAccounts ACCTFROM ACCTTO #precompiledAccounts(SCHED)
          ~> #loadAccessList(TA)
          ~> #call ACCTFROM ACCTTO ACCTTO VALUE VALUE DATA false
          ~> #finishTx ~> #finalizeTx(false) ~> startTx
         ...
         </k>
         <schedule> SCHED </schedule>
         <gasPrice> _ => #effectiveGasPrice(TXID) </gasPrice>
         <callGas> _ => GLIMIT -Int G0(SCHED, DATA, false) </callGas>
         <origin> _ => ACCTFROM </origin>
         <callDepth> _ => -1 </callDepth>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <coinbase> MINER </coinbase>
         <message>
           <msgID>      TXID   </msgID>
           <txGasLimit> GLIMIT </txGasLimit>
           <to>         ACCTTO </to>
           <value>      VALUE  </value>
           <data>       DATA   </data>
           <txAccess>   TA     </txAccess>
           ...
         </message>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL => BAL -Int (GLIMIT *Int #effectiveGasPrice(TXID)) </balance>
           <nonce> NONCE => NONCE +Int 1 </nonce>
           ...
         </account>
         <accessedAccounts> _ => .Set </accessedAccounts>
         <touchedAccounts> _ => SetItem(MINER) </touchedAccounts>
      requires ACCTTO =/=K .Account
  syntax EthereumCommand  ::=
    "#finishTx"
  rule <statusCode> _:ExceptionalStatusCode </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState                   ... </k>
  rule <statusCode> EVMC_REVERT             </statusCode> <k> #halt ~> #finishTx => #popCallStack ~> #popWorldState ~> #refund GAVAIL ... </k> <gas> GAVAIL </gas>
  rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #finishTx => #mkCodeDeposit ACCT ... </k>
         <id> ACCT </id>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <message>
           <msgID> TXID     </msgID>
           <to>    .Account </to>
           ...
         </message>
  rule <statusCode> EVMC_SUCCESS </statusCode>
         <k> #halt ~> #finishTx => #popCallStack ~> #dropWorldState ~> #refund GAVAIL ... </k>
         <gas> GAVAIL </gas>
         <txPending> ListItem(TXID:Int) ... </txPending>
         <message>
           <msgID> TXID </msgID>
           <to>    TT   </to>
           ...
         </message>
      requires TT =/=K .Account
  syntax EthereumCommand  ::=
    "#loadAccessList" "(" JSON ")" [klabel(#loadAccessList)]
  | "#loadAccessListAux" "(" Account "," List ")" [klabel(#loadAccessListAux)]
  rule <k> #loadAccessList ([ .JSONs ]) => . ... </k>
         <schedule> SCHED </schedule>
      requires Ghasaccesslist << SCHED >>
  rule <k> #loadAccessList ([ _ ]) => . ... </k>
         <schedule> SCHED </schedule>
      requires notBool Ghasaccesslist << SCHED >>
  rule <k> #loadAccessList ([[ACCT, [STRG:JSONs]], REST])
          => #loadAccessListAux (#asAccount(#parseByteStackRaw(ACCT)), #parseAccessListStorageKeys([STRG]))
          ~> #loadAccessList ([REST])
         ...
         </k>
         <schedule> SCHED </schedule>
      requires Ghasaccesslist << SCHED >>
  rule <k> #loadAccessListAux (ACCT, (ListItem(STRGK) STRGKS))
          => #accessStorage ACCT STRGK:Int
          ~> #loadAccessListAux (ACCT, STRGKS)
         ...
         </k>
         <schedule> SCHED </schedule>
         <callGas> GLIMIT => GLIMIT -Int Gaccessliststoragekey < SCHED > </callGas>
  rule <k> #loadAccessListAux (ACCT, .List) => #accessAccounts ACCT ... </k>
         <schedule> SCHED </schedule>
         <callGas> GLIMIT => GLIMIT -Int Gaccesslistaddress < SCHED > </callGas>
  syntax Mode  ::=
    "SUCCESS"
  syntax EthereumCommand  ::=
    "exception"
  | "status" StatusCode
  rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> exception => . ... </k>
  rule <k> status SC => . ... </k> <statusCode> SC </statusCode>
  syntax EthereumCommand  ::=
    "failure" String
  | "success"
  rule <k> success => . ... </k>
         <exit-code> _ => 0 </exit-code>
         <mode> _ => SUCCESS </mode>
  rule <k>          failure _ => . ... </k>
  rule <k> #halt ~> failure _ => . ... </k>
  syntax EthereumCommand  ::=
    "run" JSON
  rule <k> run { .JSONs } => . ... </k>
  rule <k> run { TESTID : { TEST:JSONs } , TESTS }
          => run ( TESTID : { qsortJSONs(TEST) } )
          ~> #if #hasPost?( { TEST } ) #then .K #else exception #fi
          ~> clear
          ~> run { TESTS }
         ...
         </k>
  syntax Bool  ::=
    "#hasPost?" "(" JSON ")" [function]
  rule #hasPost? ({ .JSONs }) => false
  rule #hasPost? ({ (KEY:String) : _ , REST }) => (KEY in #postKeys) orBool #hasPost? ({ REST })
  syntax Set  ::=
    "#loadKeys" [function]
  rule #loadKeys => ( SetItem("env") SetItem("pre") SetItem("rlp") SetItem("network") SetItem("genesisRLP") )
  rule <k> run  TESTID : { KEY : (VAL:JSON) , REST } => load KEY : VAL ~> run TESTID : { REST } ... </k>
      requires KEY in #loadKeys
  rule <k> run _TESTID : { "blocks" : [ { KEY : VAL , REST1 => REST1 }, .JSONs ] , ( REST2 => KEY : VAL , REST2 ) } ... </k>
  rule <k> run  TESTID : { "blocks" : [ { .JSONs }, .JSONs ] , REST } => run TESTID : { REST }                      ... </k>
  syntax Set  ::=
    "#execKeys" [function]
  rule #execKeys => ( SetItem("exec") SetItem("lastblockhash") )
  rule <k> run  TESTID : { KEY : (VAL:JSON) , NEXT , REST } => run TESTID : { NEXT , KEY : VAL , REST } ... </k>
      requires KEY in #execKeys
  rule <k> run _TESTID : { "exec" : (EXEC:JSON) } => loadCallState EXEC ~> start ~> flush ... </k>
  rule <k> run _TESTID : { "lastblockhash" : (_:String) } => #startBlock ~> startTx    ... </k>
  rule <k> load "exec" : J => loadCallState J ... </k>
  rule <k> loadCallState { "caller" : (ACCTFROM:Int), REST => REST } ... </k> <caller> _ => ACCTFROM </caller>
  rule <k> loadCallState { "origin" : (ORIG:Int), REST => REST }     ... </k> <origin> _ => ORIG     </origin>
  rule <k> loadCallState { "address" : (ACCTTO:Int), REST => REST }  ... </k> <id>     _ => ACCTTO   </id>
  rule <k> loadCallState { "code" : (CODE:OpCodes), REST } => #loadProgram #asmOpCodes(CODE) ~> loadCallState { REST } ... </k>
  rule <k> loadCallState { KEY : ((VAL:String) => #parseWord(VAL)), _ } ... </k>
      requires KEY in (SetItem("gas") SetItem("gasPrice") SetItem("value"))
  rule <k> loadCallState { KEY : ((VAL:String) => #parseHexWord(VAL)), _ } ... </k>
      requires KEY in (SetItem("address") SetItem("caller") SetItem("origin"))
  rule <k> loadCallState { "code" : ((CODE:String) => #parseByteStack(CODE)), _ } ... </k>
  syntax Set  ::=
    "#postKeys" [function]
  | "#allPostKeys" [function]
  | "#checkKeys" [function]
  rule #postKeys    => ( SetItem("post") SetItem("postState") SetItem("postStateHash") )
  rule #allPostKeys => ( #postKeys SetItem("expect") SetItem("export") SetItem("expet") )
  rule #checkKeys   => ( #allPostKeys SetItem("logs") SetItem("out") SetItem("gas")
                           SetItem("blockHeader") SetItem("transactions") SetItem("uncleHeaders") SetItem("genesisBlockHeader")
                         )
  rule <k> run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { "post" : VAL } ... </k> requires KEY in #allPostKeys
  rule <k> run TESTID : { KEY : (VAL:JSON) , REST } => run TESTID : { REST } ~> check TESTID : { KEY    : VAL } ... </k> requires KEY in #checkKeys andBool notBool KEY in #allPostKeys
  syntax Set  ::=
    "#discardKeys" [function]
  rule #discardKeys => ( SetItem("//") SetItem("_info") SetItem("callcreates") SetItem("sealEngine") SetItem("transactionSequence") SetItem("chainname") )
  rule <k> run TESTID : { KEY : _ , REST } => run TESTID : { REST } ... </k> requires KEY in #discardKeys
  rule <k> load "account" : { ACCTID : ACCT } => loadAccount ACCTID ACCT ... </k>
  rule <k> loadAccount _ { "balance" : ((VAL:String)      => #parseWord(VAL)),        _ } ... </k>
  rule <k> loadAccount _ { "nonce"   : ((VAL:String)      => #parseWord(VAL)),        _ } ... </k>
  rule <k> loadAccount _ { "code"    : ((CODE:String)     => #parseByteStack(CODE)),  _ } ... </k>
  rule <k> loadAccount _ { "storage" : ({ STORAGE:JSONs } => #parseMap({ STORAGE })), _ } ... </k>
  rule <k> loadTransaction _ { "type"                 : (TT:String => #asWord(#parseByteStackRaw(TT))), _         } ... </k>
  rule <k> loadTransaction _ { "chainID"              : (TC:String => #asWord(#parseByteStackRaw(TC))), _         } ... </k>
  rule <k> loadTransaction _ { "gasLimit"             : (TG:String => #asWord(#parseByteStackRaw(TG))), _         } ... </k>
  rule <k> loadTransaction _ { "gasPrice"             : (TP:String => #asWord(#parseByteStackRaw(TP))), _         } ... </k>
  rule <k> loadTransaction _ { "nonce"                : (TN:String => #asWord(#parseByteStackRaw(TN))), _         } ... </k>
  rule <k> loadTransaction _ { "v"                    : (TW:String => #asWord(#parseByteStackRaw(TW))), _         } ... </k>
  rule <k> loadTransaction _ { "value"                : (TV:String => #asWord(#parseByteStackRaw(TV))), _         } ... </k>
  rule <k> loadTransaction _ { "to"                   : (TT:String => #asAccount(#parseByteStackRaw(TT))), _      } ... </k>
  rule <k> loadTransaction _ { "data"                 : (TI:String => #parseByteStackRaw(TI)), _                  } ... </k>
  rule <k> loadTransaction _ { "r"                    : (TR:String => #padToWidth(32, #parseByteStackRaw(TR))), _ } ... </k>
  rule <k> loadTransaction _ { "s"                    : (TS:String => #padToWidth(32, #parseByteStackRaw(TS))), _ } ... </k>
  rule <k> loadTransaction _ { "maxPriorityFeePerGas" : (V:String  => #asWord(#parseByteStackRaw(V))), _          } ... </k>
  rule <k> loadTransaction _ { "maxFeePerGas"         : (V:String  => #asWord(#parseByteStackRaw(V))), _          } ... </k>
  syntax EthereumCommand  ::=
    "check" JSON
  rule <k> #halt ~> check J:JSON => check J ~> #halt ... </k>
  rule <k> check DATA : { .JSONs } => . ... </k> requires DATA =/=String "transactions"
  rule <k> check DATA : [ .JSONs ] => . ... </k> requires DATA =/=String "ommerHeaders"
  rule <k> check DATA : { (KEY:String) : VALUE , REST } => check DATA : { KEY : VALUE } ~> check DATA : { REST } ... </k>
      requires REST =/=K .JSONs andBool notBool DATA in (SetItem("callcreates") SetItem("transactions"))
  rule <k> check DATA : [ { TEST } , REST ] => check DATA : { TEST } ~> check DATA : [ REST ] ... </k>
      requires DATA =/=String "transactions"
  rule <k> check (KEY:String) : { JS:JSONs => qsortJSONs(JS) } ... </k>
      requires KEY in (SetItem("callcreates")) andBool notBool sortedJSONs(JS)
  rule <k> check TESTID : { "post" : (POST:String) } => check "blockHeader" : {  "stateRoot" : #parseWord(POST) } ~> failure TESTID ... </k>
  rule <k> check TESTID : { "post" : { POST } } => check "account" : { POST } ~> failure TESTID ... </k>
  rule <k> check "account" : { ACCTID:Int : { KEY : VALUE , REST } } => check "account" : { ACCTID : { KEY : VALUE } } ~> check "account" : { ACCTID : { REST } } ... </k>
      requires REST =/=K .JSONs
  rule <k> check "account" : { ((ACCTID:String) => #parseAddr(ACCTID)) : _ACCT }                             ... </k>
  rule <k> check "account" : { (_ACCT:Int) : { "balance" : ((VAL:String)      => #parseWord(VAL)) } }        ... </k>
  rule <k> check "account" : { (_ACCT:Int) : { "nonce"   : ((VAL:String)      => #parseWord(VAL)) } }        ... </k>
  rule <k> check "account" : { (_ACCT:Int) : { "code"    : ((CODE:String)     => #parseByteStack(CODE)) } }  ... </k>
  rule <k> check "account" : { (_ACCT:Int) : { "storage" : ({ STORAGE:JSONs } => #parseMap({ STORAGE })) } } ... </k>
  rule <mode> EXECMODE </mode>
         <k> check "account" : { ACCT : { "balance" : (BAL:Int) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires EXECMODE =/=K VMTESTS
  rule <mode> VMTESTS </mode>
         <k> check "account" : { _ACCT : { "balance" : (_:Int) } } => . ... </k>
  rule <k> check "account" : {  ACCT : { "nonce" : (NONCE:Int) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
  rule <k> check "account" : { ACCT : { "storage" : (STORAGE:Map) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <storage> ACCTSTORAGE </storage>
           ...
         </account>
      requires #removeZeros(ACCTSTORAGE) ==K STORAGE
  rule <k> check "account" : { ACCT : { "code" : (CODE:Bytes) } } => . ... </k>
         <account>
           <acctID> ACCT </acctID>
           <code> CODE </code>
           ...
         </account>
  syntax Map  ::=
    "#removeZeros" "(" Map ")" [function, klabel(#removeZeros)]
  | "#removeZeros" "(" List "," Map ")" [function, klabel(#removeZerosAux)]
  rule #removeZeros( M )                                   => #removeZeros(Set2List(keys(M)), M)
  rule #removeZeros( .List, .Map )                         => .Map
  rule #removeZeros( ListItem(KEY) L, KEY |-> 0 REST )     => #removeZeros(L, REST)
  rule #removeZeros( ListItem(KEY) L, KEY |-> VALUE REST ) => KEY |-> VALUE #removeZeros(L, REST) requires VALUE =/=K 0
  rule <k> check TESTID : { "out" : OUT } => check "out" : OUT ~> failure TESTID ... </k>
  rule <k> check "out" : ((OUT:String) => #parseByteStack(OUT)) ... </k>
  rule <k> check "out" : OUT => . ... </k> <output> OUT </output>
  rule <k> check TESTID : { "logs" : LOGS } => check "logs" : LOGS ~> failure TESTID ... </k>
  rule <k> check "logs" : HASH:String => . ... </k> <log> SL </log> requires #parseHexBytes(Keccak256(#rlpEncodeLogs(SL))) ==K #parseByteStack(HASH)
  rule <k> check TESTID : { "gas" : GLEFT } => check "gas" : GLEFT ~> failure TESTID ... </k>
  rule <k> check "gas" : ((GLEFT:String) => #parseWord(GLEFT)) ... </k>
  rule <k> check "gas" : GLEFT => . ... </k> <gas> GLEFT </gas>
  rule check TESTID : { "blockHeader" : BLOCKHEADER } => check "blockHeader" : BLOCKHEADER ~> failure TESTID
  rule <k> check "blockHeader" : { KEY : VALUE , REST } => check "blockHeader" : { KEY : VALUE } ~> check "blockHeader" : { REST } ... </k>
      requires REST =/=K .JSONs
  rule <k> check "blockHeader" : { _KEY : (VALUE:String => #parseByteStack(VALUE)) } ... </k>
  rule <k> check "blockHeader" : {  KEY : (VALUE:Bytes => #asWord(VALUE)) } ... </k>
      requires KEY in ( SetItem("coinbase") SetItem("difficulty") SetItem("gasLimit") SetItem("gasUsed")
                        SetItem("mixHash") SetItem("nonce") SetItem("number") SetItem("parentHash")
                        SetItem("receiptTrie") SetItem("stateRoot") SetItem("timestamp")
                        SetItem("transactionsTrie") SetItem("uncleHash") SetItem("baseFeePerGas")
                      )
  rule <k> check "blockHeader" : { "bloom"            : VALUE } => . ... </k> <logsBloom>        VALUE </logsBloom>
  rule <k> check "blockHeader" : { "coinbase"         : VALUE } => . ... </k> <coinbase>         VALUE </coinbase>
  rule <k> check "blockHeader" : { "difficulty"       : VALUE } => . ... </k> <difficulty>       VALUE </difficulty>
  rule <k> check "blockHeader" : { "extraData"        : VALUE } => . ... </k> <extraData>        VALUE </extraData>
  rule <k> check "blockHeader" : { "gasLimit"         : VALUE } => . ... </k> <gasLimit>         VALUE </gasLimit>
  rule <k> check "blockHeader" : { "gasUsed"          : VALUE } => . ... </k> <gasUsed>          VALUE </gasUsed>
  rule <k> check "blockHeader" : { "mixHash"          : VALUE } => . ... </k> <mixHash>          VALUE </mixHash>
  rule <k> check "blockHeader" : { "nonce"            : VALUE } => . ... </k> <blockNonce>       VALUE </blockNonce>
  rule <k> check "blockHeader" : { "number"           : VALUE } => . ... </k> <number>           VALUE </number>
  rule <k> check "blockHeader" : { "parentHash"       : VALUE } => . ... </k> <previousHash>     VALUE </previousHash>
  rule <k> check "blockHeader" : { "receiptTrie"      : VALUE } => . ... </k> <receiptsRoot>     VALUE </receiptsRoot>
  rule <k> check "blockHeader" : { "stateRoot"        : VALUE } => . ... </k> <stateRoot>        VALUE </stateRoot>
  rule <k> check "blockHeader" : { "timestamp"        : VALUE } => . ... </k> <timestamp>        VALUE </timestamp>
  rule <k> check "blockHeader" : { "transactionsTrie" : VALUE } => . ... </k> <transactionsRoot> VALUE </transactionsRoot>
  rule <k> check "blockHeader" : { "uncleHash"        : VALUE } => . ... </k> <ommersHash>       VALUE </ommersHash>
  rule <k> check "blockHeader" : { "baseFeePerGas"    : VALUE } => . ... </k> <baseFee>          VALUE </baseFee>
  rule <k> check "blockHeader" : { "hash": HASH:Bytes } => . ...</k>
         <previousHash>     HP </previousHash>
         <ommersHash>       HO </ommersHash>
         <coinbase>         HC </coinbase>
         <stateRoot>        HR </stateRoot>
         <transactionsRoot> HT </transactionsRoot>
         <receiptsRoot>     HE </receiptsRoot>
         <logsBloom>        HB </logsBloom>
         <difficulty>       HD </difficulty>
         <number>           HI </number>
         <gasLimit>         HL </gasLimit>
         <gasUsed>          HG </gasUsed>
         <timestamp>        HS </timestamp>
         <extraData>        HX </extraData>
         <mixHash>          HM </mixHash>
         <blockNonce>       HN </blockNonce>
         <baseFee>          HF </baseFee>
      requires #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN)     ==Int #asWord(HASH)
        orBool #blockHeaderHash(HP, HO, HC, HR, HT, HE, HB, HD, HI, HL, HG, HS, HX, HM, HN, HF) ==Int #asWord(HASH)
  rule check TESTID : { "genesisBlockHeader" : BLOCKHEADER } => check "genesisBlockHeader" : BLOCKHEADER ~> failure TESTID
  rule <k> check "genesisBlockHeader" : { KEY : VALUE , REST } => check "genesisBlockHeader" : { KEY : VALUE } ~> check "genesisBlockHeader" : { REST } ... </k>
      requires REST =/=K .JSONs
  rule <k> check "genesisBlockHeader" : { KEY : _ } => .K ... </k> requires KEY =/=String "hash"
  rule <k> check "genesisBlockHeader" : { "hash": (HASH:String => #asWord(#parseByteStack(HASH))) } ... </k>
  rule <k> check "genesisBlockHeader" : { "hash": HASH } => . ... </k>
         <blockhashes> ... ListItem(HASH) ListItem(_) </blockhashes>
  rule <k> check TESTID : { "transactions" : TRANSACTIONS } => check "transactions" : TRANSACTIONS ~> failure TESTID ... </k>
  rule <k> check "transactions" : [ .JSONs ] => . ... </k> <txOrder> .List                    </txOrder>
  rule <k> check "transactions" : { .JSONs } => . ... </k> <txOrder> ListItem(_) => .List ... </txOrder>
  rule <k> check "transactions" : [ TRANSACTION , REST ] => check "transactions" : TRANSACTION   ~> check "transactions" : [ REST ] ... </k>
  rule <k> check "transactions" : { KEY : VALUE , REST } => check "transactions" : (KEY : VALUE) ~> check "transactions" : { REST } ... </k>
  rule <k> check "transactions" : ("sender" : (VALUE:Bytes  => #asAccount(VALUE)))      ... </k>
  rule <k> check "transactions" : (_KEY     : (VALUE:String => #parseByteStack(VALUE))) ... </k>
  rule <k> check "transactions" : ("to"     : (VALUE:Bytes  => #asAccount(VALUE)))      ... </k>
  rule <k> check "transactions" : ( KEY     : (VALUE:Bytes  => #padToWidth(32, VALUE))) ... </k> requires KEY in (SetItem("r") SetItem("s")) andBool lengthBytes(VALUE) <Int 32
  rule <k> check "transactions" : ( KEY     : (VALUE:Bytes  => #asWord(VALUE)))         ... </k> requires KEY in (SetItem("gasLimit") SetItem("gasPrice") SetItem("nonce") SetItem("v") SetItem("value") SetItem("chainId") SetItem("type") SetItem("maxFeePerGas") SetItem("maxPriorityFeePerGas"))
  rule <k> check "transactions" : ("type"   : (VALUE:Int    => #asmTxPrefix(VALUE)))    ... </k>
  rule <k> check "transactions" : "accessList" : [ ACCESSLIST , REST ] => check "transactions" : "accessList" : ACCESSLIST  ~> check "transactions" : "accessList" : [ REST ] ... </k>
  rule <k> check "transactions" : "accessList" : { "address" : V1 , "storageKeys": V2 , .JSONs } => check "transactions" : "accessList" : "address" : #parseHexWord(V1) : "storageKeys" : V2  ... </k>
  rule <k> check "transactions" : "accessList" : "address" : ADDR : "storageKeys" : [ KEY , REST ] => check "transactions" : "accessList" : "address" : ADDR : "storageKeys" : #parseHexWord(KEY) ~> check "transactions" : "accessList" : "address" : ADDR : "storageKeys" : [ REST ] ... </k>
  rule <k> check "transactions" : "accessList" : "address" : _    : "storageKeys" : [ .JSONs ] => . ... </k>
  rule <k> check "transactions" : "accessList" : [ .JSONs ] => . ... </k>
  rule <k> check "transactions" : "accessList" : "address" : ADDR : "storageKeys" : KEY        => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txAccess> TA </txAccess> ... </message> requires isInAccessList(ADDR, KEY, TA)
  rule <k> check "transactions" : ("data"                 : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <data>          VALUE </data>           ... </message>
  rule <k> check "transactions" : ("gasLimit"             : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txGasLimit>    VALUE </txGasLimit>     ... </message>
  rule <k> check "transactions" : ("gasPrice"             : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txGasPrice>    VALUE </txGasPrice>     ... </message>
  rule <k> check "transactions" : ("nonce"                : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txNonce>       VALUE </txNonce>        ... </message>
  rule <k> check "transactions" : ("r"                    : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigR>          VALUE </sigR>           ... </message>
  rule <k> check "transactions" : ("s"                    : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigS>          VALUE </sigS>           ... </message>
  rule <k> check "transactions" : ("to"                   : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <to>            VALUE </to>             ... </message>
  rule <k> check "transactions" : ("v"                    : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigV>          VALUE </sigV>           ... </message>
  rule <k> check "transactions" : ("value"                : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <value>         VALUE </value>          ... </message>
  rule <k> check "transactions" : ("chainId"              : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txChainID>     VALUE </txChainID>      ... </message>
  rule <k> check "transactions" : ("type"                 : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txType>        VALUE </txType>         ... </message>
  rule <k> check "transactions" : ("maxFeePerGas"         : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txMaxFee>      VALUE </txMaxFee>       ... </message>
  rule <k> check "transactions" : ("maxPriorityFeePerGas" : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <txPriorityFee> VALUE </txPriorityFee>  ... </message>
  rule <k> check "transactions" : ("sender"               : VALUE) => . ... </k> <txOrder> ListItem(TXID) ... </txOrder> <message> <msgID> TXID </msgID> <sigV> TW </sigV> <sigR> TR </sigR> <sigS> TS </sigS> ... </message> requires  #sender( #getTxData(TXID), TW, TR, TS ) ==K VALUE
  syntax Bool  ::=
    "isInAccessListStorage" "(" Int "," JSON ")" [function, klabel(isInAccessListStorage)]
  | "isInAccessList" "(" Account "," Int "," JSON ")" [function, klabel(isInAccessList)]
  rule isInAccessList(_   , _  , [.JSONs                     ]) => false
  rule isInAccessList(ADDR, KEY, [[ACCT, [STRG:JSONs]],  REST]) => #if   ADDR ==K #asAccount(#parseByteStackRaw(ACCT))
                                                                     #then isInAccessListStorage (KEY, [STRG]) orBool isInAccessList(ADDR, KEY, [REST])
                                                                     #else isInAccessList(ADDR, KEY, [REST]) #fi
  rule isInAccessListStorage(_  , [.JSONs    ]) => false
  rule isInAccessListStorage(KEY, [SKEY, REST]) => #if   KEY ==Int #asWord(#parseByteStackRaw(SKEY))
                                                     #then true
                                                     #else isInAccessListStorage(KEY, [REST]) #fi
  rule <k> check TESTID : { "uncleHeaders" : OMMERS } => check "ommerHeaders" : OMMERS ~> failure TESTID ... </k>
  rule <k> check "ommerHeaders" : [ .JSONs ] => . ... </k> <ommerBlockHeaders> [ .JSONs ] </ommerBlockHeaders>
endmodule

