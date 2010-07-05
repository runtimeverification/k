kmod THREADS is including K + PL-NAT
  configuration <thread*> 
                  <k> .K </k> <holds> .Map </holds>
                </thread*>
                <busy> .Set </busy>
  syntax K ::= spawn K       [prec 90]
             | acquire K     [strict]
             | release K     [strict]
             | rendezvous K  [strict]
             | Nat
  syntax KResult ::= .thread [latex "\cdot_{\scriptstyle\it thread}"]

  rule [spawn-thread] : <thread_> <k>spawn S:K 
                                  => .thread<_/k> <_/thread>
                        (. => <thread_> <k>S</k> <_/thread>)

  rule [end-thread] : (<thread_> <k>V:KResult</k> <holds>Holds:Map</holds>        
                       <_/thread> => .) <busy>Busy:Set 
                                           => Busy -Set keys(Holds)</busy>
  rule [free-acquire] : <k>acquire V 
                        => .thread<_/k> <holds_>. 
                                          => V|->0<_/holds> 
       <busy>Busy (.
                => SetItem(V))</busy>
    if notBool(V in Busy)
  rule [reentrant-acquire] : <k>acquire V 
                             => .thread<_/k> <holds_>V|->(N:Nat 
                                                    => sNat N)<_/holds>
  rule [reentrant-release] : <k>release V 
                             => .thread<_/k> <holds_>V|->(sNat N 
                                                    => N)<_/holds>
  rule [release] : <k>release V 
                   => .thread<_/k> <holds_>(V|->0 
                                      => .)<_/holds> 
       <busy_>(SetItem(V)
            => .)<_/busy>
  rule [rendezvous] : <k>rendezvous V 
                      => .thread<_/k> <k>rendezvous V 
                                   => .thread<_/k>  
endkm
