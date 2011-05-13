rew run-with-ic(main5,

 's8(.List{K}) |-> Val32 0(.List{K})
 'sp(.List{K}) |-> Val32 0(.List{K})
 'v0(.List{K}) |-> Val32 syint32(.List{K})
 'v1(.List{K}) |-> Val32 2(.List{K})
 'zero(.List{K}) |-> Val32 0(.List{K}),

Val32 0(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 2(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 4(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 6(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 8(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K})),

Val32 0(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 2(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 4(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 6(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 8(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
) .
 
search run-with-ic(main5,

 's8(.List{K}) |-> Val32 0(.List{K})
 'sp(.List{K}) |-> Val32 0(.List{K})
 'v0(.List{K}) |-> Val32 syint32(.List{K})
 'v1(.List{K}) |-> Val32 2(.List{K})
 'zero(.List{K}) |-> Val32 0(.List{K}),

Val32 0(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 2(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 4(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 6(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K}))
Val32 8(.List{K}) |-> 'iwrap`(_`,_`)(Val32 0(.List{K}),, 'nop`;(.List{K})),

Val32 0(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 2(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 4(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 6(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
Val32 8(.List{K}) |-> 'dwrap`(_`,_`)(Val32 0(.List{K}),, Val32 0(.List{K}))
				     ) =>* < T > < k > 'last(.List{K}) </ k > B:Bag </ T > .

quit

eof



rew run-with-ic(main1,
 'ra(.List{K}) |-> Int 0(.List{K}) 
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 0(.List{K})
 'v1(.List{K}) |-> Int 0(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),

Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K})),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))

) . 

rew run-with-ic(main5,
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 1(.List{K})
 'v1(.List{K}) |-> Int 2(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K})),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
) . 

rew run-with-ic(main1,
 'ra(.List{K}) |-> Int 0(.List{K}) 
--- 'a0(.List{K}) |-> Int 0(.List{K}) 
--- 'a1(.List{K}) |-> Int 0(.List{K}) 
--- 'a2(.List{K}) |-> Int 0(.List{K}) 
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 0(.List{K})
 'v1(.List{K}) |-> Int 0(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K})),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
) . 

rew run-with-ic(main2,
 'ra(.List{K}) |-> Int 0(.List{K}) 
 'a0(.List{K}) |-> Int 0(.List{K}) 
 'a1(.List{K}) |-> Int 0(.List{K}) 
 'a2(.List{K}) |-> Int 0(.List{K}) 
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 0(.List{K})
 'v1(.List{K}) |-> Int 0(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K})),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
) . 

rew run-with-ic(main3,
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 0(.List{K})
 'v1(.List{K}) |-> Int 0(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 1040(.List{K}),,'addu_`,_`,_;('v0(
    .List{K}),,'v0(.List{K}),,'v1(.List{K})))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int
    1032(.List{K}),,'lw_`,_`(_`);('v0(.List{K}),,Int 16(.List{K}),,'s8(.List{K})))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 1028(.List{K}),,'sw_`,_`(_`);('v0(.List{
    K}),,Int 20(.List{K}),,'s8(.List{K}))),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
) . 

eof

rew run-with-ic(main4,
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 0(.List{K})
 'v1(.List{K}) |-> Int 0(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 1040(.List{K}),,'addu_`,_`,_;('v0(
    .List{K}),,'v0(.List{K}),,'v1(.List{K})))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int
    1032(.List{K}),,'lw_`,_`(_`);('v0(.List{K}),,Int 16(.List{K}),,'s8(.List{K})))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 1028(.List{K}),,'sw_`,_`(_`);('v0(.List{
    K}),,Int 20(.List{K}),,'s8(.List{K})))
) . 

rew run-with-ic(main5,
 's8(.List{K}) |-> Int 0(.List{K})
 'sp(.List{K}) |-> Int 0(.List{K})
 'v0(.List{K}) |-> Int 1(.List{K})
 'v1(.List{K}) |-> Int 2(.List{K})
 'zero(.List{K}) |-> Int 0(.List{K}),
Int 0(.List{K}) |-> 'iwrap`(_`,_`)(Int 1040(.List{K}),,'addu_`,_`,_;('v0(
    .List{K}),,'v0(.List{K}),,'v1(.List{K})))
Int 2(.List{K}) |-> 'iwrap`(_`,_`)(Int
    1032(.List{K}),,'lw_`,_`(_`);('v0(.List{K}),,Int 16(.List{K}),,'s8(.List{K})))
Int 4(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 6(.List{K}) |-> 'iwrap`(_`,_`)(Int 0(.List{K}),, 'nop`;(.List{K}))
Int 8(.List{K}) |-> 'iwrap`(_`,_`)(Int 1028(.List{K}),,'sw_`,_`(_`);('v0(.List{
    K}),,Int 20(.List{K}),,'s8(.List{K}))),

Int 0(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 2(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 4(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 6(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
Int 8(.List{K}) |-> 'dwrap`(_`,_`)(Int 0(.List{K}),, Int 0(.List{K}))
) . 
