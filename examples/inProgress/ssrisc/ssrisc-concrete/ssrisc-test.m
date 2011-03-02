rew run-with-ic(main5,

 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 1(.List{K})
 'v1(.List{K}) |-> Int32 2(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),

Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K})),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
) .


rew run-with-ic(main1,
 'ra(.List{K}) |-> Int32 0(.List{K}) 
 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 0(.List{K})
 'v1(.List{K}) |-> Int32 0(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),

Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K})),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))

) . 
				
rew run-with-ic(main1,
 'ra(.List{K}) |-> Int32 0(.List{K}) 
--- 'a0(.List{K}) |-> Int32 0(.List{K}) 
--- 'a1(.List{K}) |-> Int32 0(.List{K}) 
--- 'a2(.List{K}) |-> Int32 0(.List{K}) 
 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 0(.List{K})
 'v1(.List{K}) |-> Int32 0(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),
Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K})),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
) . 


rew run-with-ic(main2,
 'ra(.List{K}) |-> Int32 0(.List{K}) 
 'a0(.List{K}) |-> Int32 0(.List{K}) 
 'a1(.List{K}) |-> Int32 0(.List{K}) 
 'a2(.List{K}) |-> Int32 0(.List{K}) 
 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 0(.List{K})
 'v1(.List{K}) |-> Int32 0(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),
Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K})),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
) . 


rew run-with-ic(main3,
 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 0(.List{K})
 'v1(.List{K}) |-> Int32 0(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),
Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 1040(.List{K}),,'addu_`,_`,_;('v0(
    .List{K}),,'v0(.List{K}),,'v1(.List{K})))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32
    1032(.List{K}),,'lw_`,_`(_`);('v0(.List{K}),,Int32 16(.List{K}),,'s8(.List{K})))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 1028(.List{K}),,'sw_`,_`(_`);('v0(.List{
    K}),,Int32 20(.List{K}),,'s8(.List{K}))),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
) . 
			 
									 
rew run-with-ic(main4,
 's8(.List{K}) |-> Int32 0(.List{K})
 'sp(.List{K}) |-> Int32 0(.List{K})
 'v0(.List{K}) |-> Int32 0(.List{K})
 'v1(.List{K}) |-> Int32 0(.List{K})
 'zero(.List{K}) |-> Int32 0(.List{K}),
Int32 0(.List{K}) |-> 'iwrap`(_`,_`)(Int32 1040(.List{K}),,'addu_`,_`,_;('v0(
    .List{K}),,'v0(.List{K}),,'v1(.List{K})))
Int32 2(.List{K}) |-> 'iwrap`(_`,_`)(Int32
    1032(.List{K}),,'lw_`,_`(_`);('v0(.List{K}),,Int32 16(.List{K}),,'s8(.List{K})))
Int32 4(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 6(.List{K}) |-> 'iwrap`(_`,_`)(Int32 0(.List{K}),, 'nop`;(.List{K}))
Int32 8(.List{K}) |-> 'iwrap`(_`,_`)(Int32 1028(.List{K}),,'sw_`,_`(_`);('v0(.List{
    K}),,Int32 20(.List{K}),,'s8(.List{K}))),

Int32 0(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 2(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 4(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 6(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))
Int32 8(.List{K}) |-> 'dwrap`(_`,_`)(Int32 0(.List{K}),, Int32 0(.List{K}))

) . 

quit
