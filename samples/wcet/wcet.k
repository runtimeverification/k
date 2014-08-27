// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*!
\title{Low-Level Program Verification using Matching Logic Reachability}
\author{Dwight Guth, Andrei \c{S}tef\u{a}nescu, and Grigore Ro\c{s}u}
\organization{University of Illinois at Urbana-Champaign}
*/

module WCET-SYNTAX

  syntax BInst ::= BOpCode Register "," Exp "," Exp [klabel('binst), strict(3, 4)]
  syntax BOpCode ::= "add" | "sub" | "mul" | "div" | "or" | "and"
  syntax Exp ::= Register
               | "#" Int
  syntax Register ::= "r" Int
  /*@ These productions define the basic pieces of B-Type instructions in the language. The
  language is a 3-register language, so each instruction has two sources and one target.

  The language has two indexing modes: an integer may signify the contents of a numbered register,
  or it may be an immediate value. We use strictness to evaluate the arguments of an instruction
  to their final value.*/

  syntax UInst ::= UOpCode Register "," Exp [klabel('uinst), strict(3)]
  syntax UOpCode ::= "not"
  /*@ Here we define the first U-Type instruction: not. Instead of taking two sources and one
  target, it takes one source and one target.*/

  syntax MInst ::= MOpCode Exp "," Exp [klabel('minst), strict(2, 3)]
  syntax UOpCode ::= "load"
  syntax MOpCode ::= "store"
  /*@ In addition to basic arithmetic and bitwise-logical operations, our language supports load
  and store operations to index memory dynamically. Load evaluates a memory location into a
  register; store evaluates a memory location and a value and puts the value into memory.*/

  syntax JInst ::= JOpCode Id [klabel('jinst)]
  syntax JOpCode ::= "jmp"
  /*@ The \texttt{jmp} instruction takes a labelled code block and unconditionally jumps to that
  location.*/

  syntax BrInst ::= BrOpCode Id "," Exp "," Exp [klabel('brinst), strict(3, 4)]
  syntax BrOpCode ::= "beq" | "bne" | "blt" | "ble"
  /*@ The language also supports conditional jump instructions. Each of these instructions
  evaluates two integers and either jumps or does not jump based on the result of an arithmetic
  comparison.*/

  syntax NInst ::= NOpCode
  syntax NOpCode ::= "halt"
  /*@ The halt instruction terminates code execution immediately, no matter what instructions
  follow it.*/

  syntax SInst ::= SOpCode Exp [klabel('sinst), strict(2)]
  syntax SOpCode ::= "sleep"
  /*@ The sleep instruction takes an argument specifying a length of time in cycles, and sleeps
  the processor until the time has elapsed.*/

  syntax RInst ::= ROpCode Register "," Id [klabel('rinst)]
  syntax ROpCode ::= "read"

  syntax WInst ::= WOpCode Id "," Exp [klabel('winst), strict(3)]
  syntax WOpCode ::= "write"

  syntax RWInst ::= RWOpCode Register "," Id "," Exp [klabel('rwinst), strict(4)]
  syntax RWOpCode ::= "rw"
  /*@ These three instructions perform I/O operations on an asynchronous I/O buffer. This named
  buffer can be written to at any time by the environment the program is running in (simulated as
  a configuration parameter). The read instruction reads the value of the buffer, the write
  instruction writes the value of the buffer, and the rw instruction atomically first reads, then
  writes to the buffer. The purpose of the rw instruction is to prevent a race that can occur if
  the program reads a value, then resets the value of the buffer, but another value is written in
  between.*/

  syntax BrOpCode ::= "int"
  syntax NOpCode ::= "rfi"
  /*@ Finally, we support periodic timer interrupts. The \texttt{int} instruction schedules an
  interrupt, which fires periodically until the program is terminated. The \texttt{rfi} instruction
  returns from an interrupt. */

  syntax UOpCode ::= "li"
  syntax BrOpCode ::= "bgt" | "bge"
  rule li R:Register , E:Exp => or R , E , #0 [macro]

  rule bgt X:Id , E:Exp , E2:Exp => blt X , E2 , E [macro]
  rule bge X:Id , E:Exp , E2:Exp => ble X , E2 , E [macro]
  /*@ We also define a couple convenience instructions as macros. The li instruction loads either
  an immediate or the contents of a register into anothe register. The bgt and bge instructions
  complete our set of conditional jump instructions.*/

  syntax Id ::= "main"
  //@ "main" is a special program label denoting the entry point of the program.

  syntax Insts ::= Inst | Inst Insts
  syntax Block ::= Id ":" Insts
  syntax Blocks ::= Block | Block Blocks
  /*@ A program consists of a list of labelled code blocks each containing a sequence of
  instructions.*/

  syntax Inst ::= BInst | UInst | MInst | JInst | BrInst | NInst | SInst | RInst | WInst | RWInst
  syntax OpCode ::= BOpCode | UOpCode | MOpCode | JOpCode | BrOpCode | NOpCode | SOpCode | ROpCode | WOpCode | RWOpCode
endmodule

module WCET
  imports WCET-SYNTAX

  configuration
    <T>
      <k> load($PGM:K) ~> jumpTo(main) </k>
      <pgm> .Map </pgm>
      <br/>
      <mem> .Map </mem>
      <reg> .Map </reg>
      <timing> $TIMING:Map </timing>
      <br/>
      <wcet> 0 </wcet>
      <input> $INPUT:List </input>
      <status> $INITIAL:Map </status>
      <br/>
      <timers> .List </timers>
      <priority> 0 </priority>
      <stack> .List </stack>
      <br/>
      <interrupts> .Set </interrupts>
    </T>
  /*@ This configuration declaration specifies the initial configuration of the program by means
  of several variables that are initialized by the tool after being specified by the user on the
  command line. This initial configuration performs preprocessing on the program to load it into
  the \texttt{pgm} cell and then jumps to the entry point, labelled \texttt{main}.*/

  syntax KResult ::= Int
  syntax Exp ::= Int

  syntax Map ::= Map "<-" Map [function]
  rule M1 <- (K1:K |-> K2:K M2:Map) => M1[K1 <- K2] <- M2
  rule M1 <- .Map => M1

  //@ The values of the language are integers once an immediate or register index is evaluated.

  syntax KItem ::= load(K)
                 | jumpTo(Id)
  /*@ Here we define additional auxiliary operators. load takes a program and puts it in the
  \texttt{pgm} cell for use by jump instructions later on. jumpTo takes an identifier and jumps
  immediately to  it. We define this instruction because we want to use it in places where using
  the \texttt{jmp} instruction directly in our semantics is unsuitable because the \texttt{jmp}
  instruction increments the \texttt{wcet} cell.*/

  rule <k> I:Inst Is:Insts => I ~> Is ...</k>
  //@ Here we define sequential composition. A block of instructions is executed one at a time.

  rule load(B:Block Bs:Blocks) => load(B) ~> load(Bs)
  rule <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... .Map => X |-> (Is) ...</pgm>
  /*@ Note here that the \texttt{pgm} cell is only loaded with the contents of the current block.
  We will see the significance of this momentarily.*/

  rule <k> jumpTo(X) ~> _ => K </k>
       <pgm>... X:Id |-> K:K ...</pgm>
  /*@ Here we take the contents of the \texttt{pgm} cell and replace the entire \texttt{k} cell
  with it. Because the pgm cell does not include all subseqent blocks, a program does not fall
  through from one block to the next. In order to continue executing, the block must end with a
  jump instruction to specify the next block.*/

  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
  //@ Register lookup looks up the numbered register in the \texttt{reg} cell.

  rule # I:Int => I
  //@ And an immediate evaluates to its own declared value.

  rule <k> add r I:Int , I2:Int , I3:Int => time(add) ...</k>
       <reg> R:Map => R[I2 +Int I3 <- I] </reg>
  rule <k> sub r I:Int , I2:Int , I3:Int => time(sub) ...</k>
       <reg> R:Map => R[I2 -Int I3 <- I] </reg>
  rule <k> mul r I:Int , I2:Int , I3:Int => time(mul) ...</k>
       <reg> R:Map => R[I2 *Int I3 <- I] </reg>
  rule <k> div r I:Int , I2:Int , I3:Int => time(div) ...</k>
       <reg> R:Map => R[I2 /Int I3 <- I] </reg>
  rule <k> or r I:Int , I2:Int , I3:Int => time(or) ...</k>
       <reg> R:Map => R[I2 |Int I3 <- I] </reg>
  rule <k> and r I:Int , I2:Int , I3:Int => time(and) ...</k>
       <reg> R:Map => R[I2 &Int I3 <- I] </reg>
  rule <k> not r I:Int , I2:Int => time(not) ...</k>
       <reg> R:Map => R[~Int I2 <- I] </reg>
  /*@ The first instructions of the language are defined above. Once the arguments are evaluated,
  the arithmetic operation is performed and the result is stored in the target register. Then the
  time of the instruction is made to elapse. The auxiliary operation \texttt{time} elapses time
  according to the specified length of the instruction in question.*/

  rule <k> load r I:Int , I2:Int => time(load) ...</k>
       <mem>... I2 |-> I3:Int ...</mem>
       <reg> R:Map => R[I3 <- I] </reg>
  /*@ The \texttt{mem} cell contains memory. An integer location in memory is evaluated, indexed in
  memory, and the value found there is put in a register.*/

  rule <k> store I:Int , I2:Int => time(store) ...</k>
       <mem> M:Map => M[I2 <- I] </mem>
  /*@ \texttt{store} evaluates two arguments. The first expresses the location in memory to write
  to, and the second expresses the value to write there. Once evaluated, we update the \texttt{mem}
  cell with the value in memory.*/

  rule jmp X:Id => time(jmp) ~> jumpTo(X)
  /*@ The main semantics of \texttt{jmp} are the jumpTo opereration. The instruction takes time,
  however.*/

  rule <k> beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X)  ...</k>
  rule <k> bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X) ...</k>
  rule <k> blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X) ...</k>
  rule <k> ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X) ...</k>

  syntax KItem ::= branch(Bool, Id)
  rule branch(true, X:Id) => jumpTo(X)
  rule branch(false, _) => .
  /*@ Conditional jump evaluates a boolean condition. If the condition is true, we jump to the
  target. If it is false, we fall through to the next instruction.*/

  rule halt ~> _ => time(halt)
  /*@ \texttt{halt} removes the entire \texttt{k} cell, effectively ending execution (once it is
  finished executing).*/

  rule sleep I:Int => waitFor(I)
  //@ The auxiliary operation \texttt{waitFor} elapses a specified length of time.

  rule <k> read r I:Int , X:Id => time(read) ...</k>
       <status>... X |-> I2:Int ...</status>
       <reg> Reg:Map => Reg[I2 <- I] </reg>
  /*@ An I/O read looks up the current value of the data in the \texttt{status} cell, then
  writes it to a register.*/

  rule <k> write X:Id , I:Int => time(write) ...</k>
       <status> Status:Map => Status[I <- X] </status>
  //@ \texttt{write} evaluates a value, then writes it to the \texttt{status} cell.

  rule <k> rw r I:Int , X:Id , I3:Int => time(rw) ...</k>
       <status>... X |-> (I2:Int => I3) ...</status>
       <reg> Reg:Map => Reg[I2 <- I] </reg>
  //@ \texttt{rw} simply combines these two instructions together.

  syntax KItem ::= (Id, Int, Int)
  rule <k> int X:Id , I:Int , I2:Int => time(int) ...</k>
       <timers>... .List => ListItem((X, I +Int Time, I2)) </timers>
       <wcet> Time:Int </wcet>
  /*@ \texttt{int} schedules an interrupt $I$ cycles after executing, to execute periodically every
  $I2$ cycles thereafter. The \texttt{timers} cell stores the currently activated interrupts in a
  list of tuples.*/

  syntax KItem ::= (K, Int)
  rule <k> rfi ~> _ => time(rfi) ~> K </k>
       <stack> ListItem((K:K, Priority:Int)) => .List ...</stack>
       <priority> _ => Priority </priority>
  /*@ To return from an interrupt, we restore the previously executing code from the \texttt{stack}
  cell, which also contains the previously-executing priority to restore to the \texttt{priority}
  cell.  Interrupts are assigned numeric priority in the order they are scheduled by the program,
  and can interrupt only code running at a lower priority. Recall the program begins executing at
  priority 0.*/

  syntax KItem ::= time(OpCode)
  rule <k> time(O:OpCode) => waitFor(I) ...</k>
       <timing>... O |-> I:Int ...</timing>
  /*@ For modularity, we allow the time each instruction executes for to be specified dynamically
  in the \texttt{timing} cell.*/

  syntax KItem ::= waitFor(Int)
  rule <k> waitFor(I:Int) => updateStatus(I2) ~> updateTimers(L) ~> interrupt(L, size(L)) ...</k>
       <br/>
       <wcet> I2:Int => I2 +Int I </wcet>
       <timers> L:List => .List </timers>
  /*@ The \texttt{wcet} cell stores the length of time the program has already been running for, in
  total. When time passes, two types of asynchronous events can occur. The first is a write on an
  I/O line, provided in advance in the \texttt{input} cell. The second is the firing of a timer
  interrupt.*/

  syntax KItem ::= updateStatus(Int)
  syntax KItem ::= (Int, Map) [klabel('status)]
  rule <k> updateStatus(Start:Int) ...</k>
       <input> ListItem((I2:Int, M:Map)) => .List ...</input>
       <wcet> I:Int </wcet>
       <status> Status:Map => Status <- M </status> when I >=Int I2 andBool I2 >=Int Start
  rule <k> updateStatus(Start:Int) => . ...</k>
       <input> ListItem((I2:Int, _:Map)) ...</input>
       <wcet> I:Int </wcet> when notBool(I >=Int I2 andBool I >=Int Start)
  rule <k> updateStatus(_) => . ...</k>
       <input> .List </input>
  /*@ Essentially, updateStatus processes every input event between time $Start$ and time $I$.
  Each event contains a map of associated I/O writes, which is merged with the status cell. Events
  ocurring before or after the time window of the instruction are ignored.*/

  syntax KItem ::= updateTimers(List)
  rule <k> updateTimers((ListItem((X:Id, Expires:Int, Interval:Int)) => .List) _) ...</k>
       <br/>
       <wcet> I:Int </wcet>
       <timers>... .List => ListItem((X, Expires, Interval)) </timers> when I <Int Expires orBool Interval ==Int 0
  rule <k> updateTimers(ListItem((X:Id, (Expires:Int => Expires +Int Interval), Interval:Int)) _) ...</k>
       <br/>
       <wcet> I:Int </wcet>
       <interrupts>... .Set => SetItem(X) </interrupts> when I >=Int Expires andBool Interval =/=Int 0
  rule updateTimers(.List) => .
  /*@ Essentially, updateTimers updates the \texttt{interrupts} cell with all the interrupts that
  have been triggered by the previous instruction. When an interrupt is triggered, the tuple
  containing info on the interrupt is updated with a new expiration time.*/

  syntax KItem ::= interrupt(List, Int)
  rule <k> interrupt((ListItem((X:Id, _, _)) => .List) _, (N:Int => N -Int 1)) ...</k>
       <br/>
       <interrupts> S:Set </interrupts>
       <priority> Priority:Int </priority> when notBool(X in S) orBool N <=Int Priority
  rule <k> interrupt(ListItem((X:Id, _, _)) _, N:Int) ~> K:K => jumpTo(X) </k>
       <priority> Priority:Int => N </priority>
       <br/>
       <interrupts> S:Set => S -Set SetItem(X) </interrupts>
       <stack> .List => ListItem((K, Priority)) ...</stack> when N >Int Priority andBool X in S
  rule <k> interrupt(.List, _) => . ...</k>
  /*@ Essentially, interrupt fires exactly one pending interrupt, removing it from the
  \texttt{interrupts} cell. This only occurs if there is a pending interrupt to fire and its
  priority is higher than the current priority of the process, however. When an interrupt is fired,
  we jump to the label specified by the \texttt{int} instruction and begin executing with the
  new priority. Note that the priority of an interrupt is simply the number of interrupts that
  were scheduled after the interrupt in question. Thus if we schedule 5 interrupts, the first has
  priority 5, the second has priority 4, etc. User code has priority 0. Once an interrupt reaches
  an \texttt{rfi} instruction, this process will repeat again and another interrupt will fire.
  Only once all interrupts have been fired will normal code resume. Thus, like a real assembly
  language, we can starve low-priority code by firing too many high-priority interrupts.*/

  // hack for parsing the ids below in the specifications
  syntax Id ::= Token{"data"}
endmodule
