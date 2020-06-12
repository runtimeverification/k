`set_balance` spec
==================

State Model
-----------

```k

module SET-BALANCE
    imports INT
    imports DOMAINS
    imports COLLECTIONS

    configuration
      <set-balance>
        <k> $ACTION:Action </k>
        <now> 0 </now>
        <events> .List </events>
        <return-value> .Result </return-value>
        <call-stack> .List </call-stack>
        <existentialDeposit> 0 </existentialDeposit>
        <creationFee> 0 </creationFee>
        <transferFee> 0 </transferFee>
        <totalIssuance> 0 </totalIssuance>
        <accounts>
          <account multiplicity="*" type="Map">
            <accountID> .AccountId:AccountId </accountID>
            <freeBalance> 0 </freeBalance>
            <reservedBalance> 0 </reservedBalance>
            <vestingBalance> 0 </vestingBalance>
            <startingBlock> 0 </startingBlock>
            <perBlock> 0 </perBlock>
            <nonce> .Nonce </nonce>
            <locks> .Set </locks>
          </account>
        </accounts>
      </set-balance>
```

Data
----

- An `AccountId` is an `Int`.
- An `Origin` is an `AccountId`, `Root`, or `None`.
- A `Nonce` is an optional `Int`.
- An `Event` records some happenning.

```k
    syntax AccountId ::= ".AccountId" | Int
 // ---------------------------------------

    syntax Origin ::= AccountId | ".Root" | ".None"
 // -----------------------------------------------

    syntax Nonce ::= ".Nonce" | Int
 // -------------------------------

    syntax Event ::= DustEvent ( Int )
 // ----------------------------------
```

Some predicates which help specifying behavior:

-   `#inWidth`: Specify that a given number is in some bitwidth.

```k
    syntax Bool ::= #inWidth(Int, Int) [function, functional]
 // ---------------------------------------------------------
    rule #inWidth(N, M) => 0 <=Int M andBool M <Int (2 ^Int N)
```

Results
-------

A `Result` is the return value of an execution step.

-   `AccountKilled` indicates that the free balance goes below the existential threshold.
-   `Updated` indicates that an account was updated successfully.

```k
    syntax Result ::= ".Result" | "AccountKilled" | "Updated"
 // ---------------------------------------------------------
```

Public Getters
--------------

### `total_balance`

Retrieves the total balance of an account.  This includes both the free and
reserved balances.

```k
    syntax Int ::= "total_balance" "(" AccountId ")" [function, functional]
 // -----------------------------------------------------------------------
    rule total_balance(WHO) => free_balance(WHO) +Int reserved_balance(WHO)
```

### `free_balance`

Gets the free balance of an account.

Other than when this module is executing, this will never be strictly between
`EXISTENTIAL_DEPOSIT` and zero.

```k
    syntax Int ::= "free_balance" "(" AccountId ")" [function, functional]
 // ----------------------------------------------------------------------
    rule    free_balance(_)   => 0 [owise]
    rule [[ free_balance(WHO) => FREE_BALANCE ]]
         <account>
           <accountID> WHO </accountID>
           <freeBalance> FREE_BALANCE </freeBalance>
           ...
         </account>
```

### `reserved_balance`

Gets the reserved balance of an account.

Other than when this module is executing, this will never be strictly between
`EXISTENTIAL_DEPOSIT` and zero.

```k
    syntax Int ::= "reserved_balance" "(" AccountId ")" [function, functional]
 // --------------------------------------------------------------------------
    rule    reserved_balance(_)   => 0 [owise]
    rule [[ reserved_balance(WHO) => FREE_BALANCE ]]
         <account>
           <accountID> WHO </accountID>
           <reservedBalance> FREE_BALANCE </reservedBalance>
           ...
         </account>
```

### `can_slash`

Determines if an account’s free balance is over the value provided.  This is
often used to determine if an account has enough balance to cover a potential
slash, hence the name.

```k
    syntax Bool ::= "can_slash" "(" AccountId "," Int ")" [function, functional]
 // ----------------------------------------------------------------------------
    rule    can_slash(_, _)        => false
    rule [[ can_slash(WHO, AMOUNT) => FREE_BALANCE >=Int AMOUNT ]]
         <account>
           <accountID> WHO </accountID>
           <freeBalance> FREE_BALANCE </freeBalance>
           ...
         </account>
```

### `total_issuance`

Retrieves the total outstanding amount of currency outstanding.  This will
always be equal to the sum of all free and reserved balances in all active
accounts, except when the balances module is executing.

```k
    syntax Int ::= "total_issuance" [function, functional]
 // ------------------------------------------------------
    rule [[ total_issuance => TOTAL_ISSUANCE ]]
         <totalIssuance> TOTAL_ISSUANCE </totalIssuance>
```

### `issue`

Issues currency, creating an imbalance.

This is not specified, since these semantics do not include the concept of an
imbalance.  Without the concept of destructors and move semantics, it would be
almost impossible to use correctly.

### `burn`

Burns currency.

This is not part of the semantics for the same reason `burn` is not.

Actions and Results
-------------------

An `Action` is an execution step (or the result of an execution step).
An `EntryAction` is an `Action` that can be invoked externally.
A `Result` is considered an `Action`, as is an `EntryAction`.

```k
    syntax Action ::= Result | EntryAction
 // --------------------------------------
```

### `account_exists`

```k
    syntax Bool ::= "account_exists" "(" AccountId ")" [function, functional]
 // -------------------------------------------------------------------------
    rule    account_exists(_)   => false [owise]
    rule [[ account_exists(WHO) => true ]]
         <account> <accountID> WHO </accountID> ... </account>
```

### `create_account`

```k
    syntax Action ::= "create_account" "(" AccountId ")"
 // ----------------------------------------------------
    rule <k> create_account(WHO) => . ... </k>
         <accounts> ( .Bag => <account> <accountID> WHO </accountID> ... </account> ) ... </accounts>
```

### `set_free_balance`

-   Updates an accounts balance if the new balance is above the existential threshold.
-   Kills the account if the balance goes below the existential threshold and the reserved balance is non-zero.
-   Reaps the account if the balance goes below the existential threshold and the reserved balance is zero.

```k
    syntax Action ::= "set_free_balance" "(" AccountId "," Int ")"
 // --------------------------------------------------------------
    rule <k> (. => create_account(WHO)) ~> set_free_balance(WHO, _) ... </k>
      requires notBool account_exists(WHO)

    rule [free-account-updated]:
         <k> set_free_balance(WHO, BALANCE) => . ... </k>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <account>
           <accountID> WHO </accountID>
           <freeBalance> _ => BALANCE </freeBalance>
           ...
         </account>
      requires EXISTENTIAL_DEPOSIT <=Int BALANCE

    rule [free-account-killed]:
         <k> set_free_balance(WHO, BALANCE) => . ... </k>
         <events> ... (.List => ListItem(DustEvent(FREE_BALANCE))) </events>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int BALANCE </totalIssuance>
         <account>
           <accountID> WHO </accountID>
           <nonce> _ => .Nonce </nonce>
           <freeBalance> FREE_BALANCE => 0 </freeBalance>
           <reservedBalance> RESERVED_BALANCE </reservedBalance>
           ...
         </account>
      requires BALANCE <Int EXISTENTIAL_DEPOSIT
       andBool 0 <Int RESERVED_BALANCE

    rule [free-account-reaped]:
         <k> set_free_balance(WHO, BALANCE) => . ... </k>
         <events> ... (.List => ListItem(DustEvent(FREE_BALANCE))) </events>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int BALANCE </totalIssuance>
         <accounts>
           ( <account>
               <accountID> WHO </accountID>
               <freeBalance> FREE_BALANCE </freeBalance>
               <reservedBalance> 0 </reservedBalance>
               ...
             </account>
          => .Bag
           )
           ...
         </accounts>
      requires BALANCE <Int EXISTENTIAL_DEPOSIT
```

### `set_reserved_balance`

-   Updates an accounts balance if the new balance is above the existential threshold.
-   Kills the account if the balance goes below the existential threshold and the free balance is non-zero.
-   Reaps the account if the balance goes below the existential threshold and the free balance is zero.

```k
    syntax Action ::= "set_reserved_balance" "(" AccountId "," Int ")"
 // ------------------------------------------------------------------
    rule <k> (. => create_account(WHO)) ~> set_reserved_balance(WHO, _) ... </k>
      requires notBool account_exists(WHO)

    rule [reserved-account-updated]:
         <k> set_reserved_balance(WHO, BALANCE) => . ... </k>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <account>
           <accountID> WHO </accountID>
           <reservedBalance> _ => BALANCE </reservedBalance>
           ...
         </account>
      requires EXISTENTIAL_DEPOSIT <=Int BALANCE

    rule [reserved-account-killed]:
         <k> set_reserved_balance(WHO, BALANCE) => . ... </k>
         <events> ... (.List => ListItem(DustEvent(RESERVED_BALANCE))) </events>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int BALANCE </totalIssuance>
         <account>
           <accountID> WHO </accountID>
           <nonce> _ => .Nonce </nonce>
           <freeBalance> FREE_BALANCE  </freeBalance>
           <reservedBalance> RESERVED_BALANCE => 0 </reservedBalance>
           ...
         </account>
      requires BALANCE <Int EXISTENTIAL_DEPOSIT
       andBool 0 <Int FREE_BALANCE

    rule [reserved-account-reaped]:
         <k> set_reserved_balance(WHO, BALANCE) => . ... </k>
         <events> ... (.List => ListItem(DustEvent(RESERVED_BALANCE))) </events>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int BALANCE </totalIssuance>
         <accounts>
           ( <account>
               <accountID> WHO </accountID>
               <freeBalance> 0 </freeBalance>
               <reservedBalance> RESERVED_BALANCE </reservedBalance>
               ...
             </account>
          => .Bag
           )
           ...
         </accounts>
      requires BALANCE <Int EXISTENTIAL_DEPOSIT
```

### `set_balance`

* Sets the new free balance
* Creates suitible imbalances (both positive and negative).
* Calls `set_free_balance` with the new free balance.
* Calls `set_reserved_balance` with the new reserved balance.

```k
    syntax EntryAction ::= "set_balance" "(" AccountId "," AccountId "," Int "," Int ")"
 // ------------------------------------------------------------------------------------
    rule [balance-set]:
        <k> set_balance(_, WHO, FREE_BALANCE, RESERVED_BALANCE)
         => set_balance_free(WHO, FREE_BALANCE)
         ~> set_balance_reserved(WHO, RESERVED_BALANCE)
        ...
        </k>
```

Helpers for calling `set_free_balance` and `set_reserved_balance`.

* Sets the new free balance
* Emits an imbalance event
* Helper function for `set_balance`

```k
    syntax Action ::= "set_balance_free"     "(" AccountId "," Int ")"
    syntax Action ::= "set_balance_reserved" "(" AccountId "," Int ")"
 // ------------------------------------------------------------------
    rule [balance-set-free]:
         <k> set_balance_free(WHO, FREE_BALANCE') => set_free_balance(WHO, FREE_BALANCE') ... </k>
         <totalIssuance> ISSUANCE => ISSUANCE +Int (FREE_BALANCE' -Int free_balance(WHO)) </totalIssuance>
      requires #inWidth(96, ISSUANCE +Int (FREE_BALANCE' -Int free_balance(WHO)))

    rule [balance-set-reserved]:
         <k> set_balance_reserved(WHO, RESERVED_BALANCE') => set_reserved_balance(WHO, RESERVED_BALANCE') ... </k>
         <totalIssuance> ISSUANCE => ISSUANCE +Int (RESERVED_BALANCE' -Int reserved_balance(WHO)) </totalIssuance>
      requires #inWidth(96, ISSUANCE +Int (RESERVED_BALANCE' -Int reserved_balance(WHO)))
```

### `transfer_raw`

Transfer some liquid free balance to another account.

`transfer` will set the `FreeBalance` of the sender and receiver.
It will decrease the total issuance of the system by the `TransferFee`.
If the sender's account is below the existential deposit as a result
of the transfer, the account will be reaped.

The dispatch origin for this call must be `Signed` by the transactor.

```k
    syntax ExistenceRequirement ::= "AllowDeath"
                                  | "KeepAlive"

    syntax EntryAction ::= transfer(Origin, AccountId, Int)
                         | "transfer_keep_alive" "(" Origin "," AccountId "," Int ")"
 // ---------------------------------------------------------------------------------

    syntax Action ::= rawTransfer(AccountId, AccountId, Int, ExistenceRequirement)
 // ------------------------------------------------------------------------------
    rule [transfer-to-raw]:
         <k> transfer(ORIGIN:AccountId, DESTINATION, AMOUNT)
          => rawTransfer(ORIGIN, DESTINATION, AMOUNT, AllowDeath)
         ...
         </k>

    rule [transfer-keep-alive]:
         <k> transfer_keep_alive(ORIGIN:AccountId, DESTINATION, AMOUNT)
          => rawTransfer(ORIGIN, DESTINATION, AMOUNT, KeepAlive)
         ...
         </k>

    rule <k> (. => create_account(DESTINATION)) ~> rawTransfer(ORIGIN, DESTINATION, _, _) ... </k>
      requires         account_exists(ORIGIN)
       andBool notBool account_exists(DESTINATION)

    rule [transfer-self]:
         <k> rawTransfer(ORIGIN:AccountId, ORIGIN, _, _) => . ... </k>
      requires account_exists(ORIGIN)

    rule [transfer-existing-account]:
         <k> rawTransfer(ORIGIN, DESTINATION, AMOUNT, EXISTENCE_REQUIREMENT)
          => set_free_balance(ORIGIN, SOURCE_BALANCE -Int AMOUNT -Int FEE)
          ~> set_free_balance(DESTINATION, DESTINATION_BALANCE +Int AMOUNT)
         ...
         </k>
         <totalIssuance> ISSUANCE => ISSUANCE -Int FEE </totalIssuance>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <transferFee> FEE </transferFee>
         <accounts>
           <account>
             <accountID> ORIGIN </accountID>
             <freeBalance> SOURCE_BALANCE </freeBalance>
             ...
           </account>
           <account>
             <accountID> DESTINATION </accountID>
             <freeBalance> DESTINATION_BALANCE </freeBalance>
             ...
           </account>
         </accounts>
      requires ORIGIN =/=K DESTINATION
       andBool DESTINATION_BALANCE >Int 0
       andBool SOURCE_BALANCE >=Int (AMOUNT +Int FEE)
       andBool ensure_can_withdraw(ORIGIN, Transfer, SOURCE_BALANCE -Int AMOUNT -Int FEE)
       andBool (EXISTENCE_REQUIREMENT ==K AllowDeath orBool SOURCE_BALANCE -Int AMOUNT -Int FEE >Int EXISTENTIAL_DEPOSIT)

    rule [transfer-create-account]:
         <k> rawTransfer(ORIGIN:AccountId, DESTINATION, AMOUNT, EXISTENCE_REQUIREMENT)
          => set_free_balance(ORIGIN, SOURCE_BALANCE -Int AMOUNT -Int CREATION_FEE)
          ~> set_free_balance(DESTINATION, AMOUNT)
         ...
         </k>
         <totalIssuance> ISSUANCE => ISSUANCE -Int CREATION_FEE </totalIssuance>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
         <creationFee> CREATION_FEE </creationFee>
         <accounts>
           <account>
             <accountID> ORIGIN </accountID>
             <freeBalance> SOURCE_BALANCE </freeBalance>
             ...
           </account>
           <account>
             <accountID> DESTINATION </accountID>
             <freeBalance> 0 </freeBalance>
             <reservedBalance> 0 </reservedBalance>
             ...
           </account>
           ...
         </accounts>
      requires ORIGIN =/=K DESTINATION
       andBool SOURCE_BALANCE >=Int (AMOUNT +Int CREATION_FEE)
       andBool EXISTENTIAL_DEPOSIT <=Int AMOUNT
       andBool ensure_can_withdraw(ORIGIN, Transfer, SOURCE_BALANCE -Int AMOUNT -Int CREATION_FEE)
       andBool (EXISTENCE_REQUIREMENT ==K AllowDeath orBool SOURCE_BALANCE -Int AMOUNT -Int CREATION_FEE >=Int EXISTENTIAL_DEPOSIT)
```

### `force_transfer`

Force a transfer from any account to any other account.  This can only be done by root.

```k
    syntax EntryAction ::= "force_transfer" "(" Origin "," AccountId "," AccountId "," Int ")"
 // ------------------------------------------------------------------------------------------
    rule [force-transfer]:
         <k> force_transfer(.Root, SOURCE, DESTINATION, AMOUNT) => transfer(SOURCE, DESTINATION, AMOUNT) ... </k>
```

### `withdraw`

Withdraw funds from an account.

```k
    syntax EntryAction ::= withdraw(AccountId, Int, WithdrawReason, ExistenceRequirement)
 // -------------------------------------------------------------------------------------
    rule [withdraw]: // K really needs where clauses
         <k> withdraw(WHO, AMOUNT, REASON, EXISTENCE_REQUIREMENT)
          => withdrawInner(WHO, AMOUNT, AMOUNT -Int free_balance(WHO), REASON, EXISTENCE_REQUIREMENT)
         ...
         </k>

    syntax Action ::= withdrawInner(AccountId, Int, Int, WithdrawReason, ExistenceRequirement)
 // ------------------------------------------------------------------------------------------
    rule [withdrawInner]:
         <k> withdrawInner(WHO, AMOUNT, NEW_BALANCE, REASON, EXISTENCE_REQUIREMENT)
          => set_free_balance(WHO, NEW_BALANCE)
         ...
         </k>
         <totalIssuance> ISSUANCE => ISSUANCE -Int AMOUNT </totalIssuance>
         <existentialDeposit> EXISTENTIAL_DEPOSIT </existentialDeposit>
      requires NEW_BALANCE >=Int 0
       andBool ensure_can_withdraw(WHO, REASON, NEW_BALANCE)
       andBool (EXISTENCE_REQUIREMENT ==K AllowDeath orBool NEW_BALANCE >=Int EXISTENTIAL_DEPOSIT)
```

Call Frames
-----------

Function call and return.

```k
    syntax CallFrame ::= frame(continuation: K)
    syntax Action ::= call   ( Action )
                    | return ( Result )
 // -----------------------------------
    rule [call]:
         <k> call(Action) ~> CONT => Action </k>
         <call-stack> .List => ListItem(frame(CONT)) ... </call-stack>

    rule [return]:
         <k> return(R) ~> _ => CONT </k>
         <return-value> _ => R </return-value>
         <call-stack> ListItem(frame(CONT)) => .List ... </call-stack>

    rule [return-unit]:
         <k> . => CONT </k>
         <return-value> _ => .Result </return-value>
         <call-stack> ListItem(frame(CONT)) => .List ... </call-stack>
```

Ensure that a given amount can be withdrawn from an account.

**FIXME**: we do not account for multiple withdrawl reasons, due to K’s
lacking polymorphism.

```k
    syntax WithdrawReason ::= "TransactionPayment"
                            | "Transfer"
                            | "Reserve"
                            | "Fee"
                            | "Tip"
 // -------------------------------


    syntax Bool ::= "ensure_can_withdraw" "(" AccountId "," WithdrawReason "," Int ")" [function, functional]
 // ---------------------------------------------------------------------------------------------------------
    rule ensure_can_withdraw(_, _, _) => true [owise]

    rule [[ ensure_can_withdraw(WHO, Transfer #Or Reserve, BALANCE) => false ]]
         <account>
           <accountID> WHO </accountID>
           <vestingBalance> VESTING_BALANCE </vestingBalance>
           ...
         </account>
      requires VESTING_BALANCE <Int BALANCE

    rule [[ ensure_can_withdraw(WHO, REASON, BALANCE) => false ]]
         <now> NOW </now>
         <account>
           <accountID> WHO </accountID>
           <locks> ACCOUNT_LOCKS </locks>
           ...
         </account>
      requires activeLocks(ACCOUNT_LOCKS, NOW, REASON, BALANCE)

    syntax LockID ::= "Election"
                    | "Staking"
                    | "Democracy"
                    | "Phragmen"
 // ----------------------------

    syntax AccountLock ::= lock ( id: LockID, until: Int, amount: Int, reasons: Set )
 // ---------------------------------------------------------------------------------

    syntax Bool ::= activeLock (AccountLock, Int, WithdrawReason, Int      ) [function]
                  | activeLocks(Set,         Int, WithdrawReason, Int      ) [function]
                  | activeLocks(List,        Int, WithdrawReason, Int, Bool) [function, klabel(activeLocksAux)]
 // -----------------------------------------------------------------------------------------------------------
    rule activeLock(AL, NOW, REASON, BALANCE) => NOW <Int until(AL) andBool BALANCE <Int amount(AL) andBool REASON in reasons(AL)

    rule activeLocks(ALS, NOW, REASON, BALANCE) => activeLocks(Set2List(ALS), NOW, REASON, BALANCE, false)

    rule activeLocks(.List, _, _, _, RESULT) => RESULT
    rule activeLocks((ListItem(AL) => .List) _, NOW, REASON, BALANCE, RESULT => RESULT orBool activeLock(AL, NOW, REASON, BALANCE))
```

Slashing and repatriation of reserved balances
----------------------------------------------

The first of these is also used by `slash`.

* `slash_reserved`
* `repatriate_reserved`

```k
    syntax Action ::= "slash_reserved" "(" AccountId "," Int ")"
 // ------------------------------------------------------------
    rule [slash-reserved]:
         <k> slash_reserved(ACCOUNT, AMOUNT)
          => set_reserved_balance(ACCOUNT, maxInt(0, RESERVED_BALANCE -Int AMOUNT))
         ...
         </k>
         <accounts>
           <account>
             <accountID> ACCOUNT </accountID>
             <reservedBalance> RESERVED_BALANCE </reservedBalance>
             ...
           </account>
         </accounts>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int minInt(RESERVED_BALANCE, AMOUNT) </totalIssuance>

    syntax Action ::= "repatriate_reserved" "(" AccountId "," AccountId "," Int ")"
 // -------------------------------------------------------------------------------
    rule [repatriate-reserved]:
         <k> repatriate_reserved(SLASHED, BENEFICIARY, AMOUNT)
          => set_free_balance(BENEFICIARY, BENEFICIARY_FREE_BALANCE +Int minInt(SLASHED_RESERVED_BALANCE, AMOUNT))
          ~> set_reserved_balance(SLASHED, SLASHED_RESERVED_BALANCE -Int minInt(SLASHED_RESERVED_BALANCE, AMOUNT))
         ...
         </k>
         <accounts>
           <account>
             <accountID> SLASHED </accountID>
             <reservedBalance> SLASHED_RESERVED_BALANCE </reservedBalance>
             ...
           </account>
           <account>
             <accountID> BENEFICIARY </accountID>
             <reservedBalance> BENEFICIARY_RESERVED_BALANCE </reservedBalance>
             <freeBalance> BENEFICIARY_FREE_BALANCE </freeBalance>
             ...
           </account>
         </accounts>
      requires BENEFICIARY_FREE_BALANCE +Int BENEFICIARY_RESERVED_BALANCE >Int 0
       andBool SLASHED =/=K BENEFICIARY

    rule [repatriate-reserved-same-account]:
         <k> repatriate_reserved(SLASHED, SLASHED, AMOUNT) => unreserve(SLASHED, AMOUNT) ... </k>
```

### Slashing

Used to punish a node for violating the protocol.

```k
    syntax EntryAction ::= slash ( AccountId , Int )
 // ------------------------------------------------
    rule [slash]:
         <k> slash(ACCOUNT, AMOUNT) => set_free_balance(ACCOUNT, FREE_BALANCE -Int AMOUNT) ... </k>
         <accounts>
           <account>
             <accountID> ACCOUNT </accountID>
             <freeBalance> FREE_BALANCE </freeBalance>
             ...
           </account>
         </accounts>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int AMOUNT </totalIssuance>
      requires FREE_BALANCE >=Int AMOUNT

    rule [slash-empty-free]:
         <k> slash(ACCOUNT, AMOUNT)
          => set_free_balance(ACCOUNT, 0)
          ~> slash_reserved(ACCOUNT, AMOUNT -Int FREE_BALANCE)
         ...
         </k>
         <accounts>
           <account>
             <accountID> ACCOUNT </accountID>
             <freeBalance> FREE_BALANCE </freeBalance>
             ...
           </account>
         </accounts>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE -Int FREE_BALANCE </totalIssuance>
      requires FREE_BALANCE <Int AMOUNT
```

### Reservation and unreservation of balances

Used to move balance from free to reserved and visa versa.

```k
    syntax Action ::= reserve ( AccountId , Int )
 // ---------------------------------------------
    rule [reserve]:
         <k> reserve(ACCOUNT, AMOUNT)
          => set_reserved_balance(ACCOUNT, FREE_BALANCE +Int AMOUNT)
          ~> set_free_balance(ACCOUNT, FREE_BALANCE -Int AMOUNT)
         ...
         </k>
         <accounts>
           <account>
             <accountID> ACCOUNT </accountID>
             <freeBalance> FREE_BALANCE </freeBalance>
             <reservedBalance> _ </reservedBalance>
             ...
           </account>
         </accounts>
      requires FREE_BALANCE >=Int AMOUNT
       andBool ensure_can_withdraw(ACCOUNT, Reserve, FREE_BALANCE -Int AMOUNT)

    syntax Action ::= unreserve ( AccountId , Int )
 // -----------------------------------------------
    rule [unreserve]:
         <k> unreserve(ACCOUNT, AMOUNT)
          => set_free_balance(ACCOUNT, FREE_BALANCE +Int minInt(AMOUNT, RESERVED_BALANCE))
          ~> set_reserved_balance(ACCOUNT, FREE_BALANCE -Int minInt(AMOUNT, RESERVED_BALANCE))
         ...
         </k>
         <accounts>
           <account>
             <accountID> ACCOUNT </accountID>
             <freeBalance> FREE_BALANCE </freeBalance>
             <reservedBalance> RESERVED_BALANCE </reservedBalance>
             ...
           </account>
         </accounts>
```

Vesting
-------

* `locked_at` ― amount currently locked
* `vesting_balance` ― get the balance that cannot currently be withdrawn.

```k
    syntax Int ::= "locked_at" "(" AccountId ")" [function, functional]
 // -------------------------------------------------------------------
    rule [[ locked_at(WHO) => maxInt(0, VESTING_BALANCE -Int (PER_BLOCK *Int maxInt(0, NOW -Int STARTING_BLOCK))) ]]
         <now> NOW </now>
         <account>
           <accountID> WHO </accountID>
           <vestingBalance> VESTING_BALANCE </vestingBalance>
           <startingBlock> STARTING_BLOCK </startingBlock>
           <perBlock> PER_BLOCK </perBlock>
           ...
         </account>

    syntax Int ::= "vesting_balance" "(" AccountId ")" [function, functional]
 // -------------------------------------------------------------------------
    rule [[ vesting_balance(WHO) => minInt(FREE_BALANCE, locked_at(WHO)) ]]
         <account>
           <accountID> WHO </accountID>
           <freeBalance> FREE_BALANCE </freeBalance>
           ...
        </account>
```

Deposits
--------

Deposit into an existing account.

```k
    syntax EntryAction ::= "deposit_into_existing" "(" AccountId "," Int ")"
 // ------------------------------------------------------------------------
    rule [deposit-into-existing]:
         <k> deposit_into_existing(WHO, AMOUNT) => . ... </k>
         <totalIssuance> TOTAL_ISSUANCE => TOTAL_ISSUANCE +Int AMOUNT </totalIssuance>
         <account>
           <accountID> WHO </accountID>
           <freeBalance> FREE_BALANCE => FREE_BALANCE +Int AMOUNT </freeBalance>
           ...
         </account>
      requires FREE_BALANCE >Int 0
```

End of module

```k
endmodule
```
