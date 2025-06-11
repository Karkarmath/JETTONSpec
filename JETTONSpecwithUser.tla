---------------------------- MODULE JETTONSpecwithUser ----------------------------
EXTENDS Integers, Sequences, FiniteSets 

CONSTANTS MaxTotalSupply, Users

ASSUME MaxTotalSupply \in Nat /\ MaxTotalSupply > 0

VARIABLES Map,
          TotalSupply,
          Mintable,
          BurnMintMemory

RECURSIVE SumMap(_)
SumMap(f) == LET dom == DOMAIN f 
             IN IF dom = {} THEN 0
                ELSE LET x == CHOOSE x \in dom: TRUE
                     IN f[x] + SumMap([y \in dom \ {x} |-> f[y]])

vars == <<Map, TotalSupply, Mintable, BurnMintMemory>>

TypeOK == /\ DOMAIN Map \subseteq Users /\ \A u \in DOMAIN Map : Map[u] \in Nat 
          /\ TotalSupply \in Nat
          /\ Mintable \in BOOLEAN
          /\ BurnMintMemory \in Seq(Int)

Init == /\ Map = [x \in {} |-> 0]
        /\ TotalSupply = 0
        /\ Mintable = TRUE
        /\ BurnMintMemory = <<>>

RandomInit == \E U \in SUBSET(Users), NBM \in 0..3, su \in 0..MaxTotalSupply : /\ Map = [u \in U |-> CHOOSE x \in 0..MaxTotalSupply : TRUE]
                                                                               /\ TotalSupply = su
                                                                               /\ SumMap(Map) = su
                                                                               /\ Mintable \in BOOLEAN
                                                                               /\ BurnMintMemory = [i \in 1..NBM |-> CHOOSE x \in -MaxTotalSupply..MaxTotalSupply : TRUE]
                                                                               /\ SumMap(BurnMintMemory) = su       

NewUserJWallet(user) == /\ user \notin DOMAIN Map  
                        /\ Map' = [u \in (DOMAIN Map) \cup {user} |-> IF u = user THEN 0 ELSE Map[u]]
                        /\ UNCHANGED <<TotalSupply, Mintable, BurnMintMemory>>

Mint(user, amount) ==   /\ Mintable = TRUE
                        /\ TotalSupply + amount <= MaxTotalSupply 
                        /\ TotalSupply' = TotalSupply + amount
                        /\ BurnMintMemory' = Append(BurnMintMemory, amount) 
                        /\ Map' = [Map EXCEPT ![user] = @ + amount]
                        /\ UNCHANGED Mintable

Burn(user, amount) ==   /\ Map[user] >= amount 
                        /\ TotalSupply' = TotalSupply - amount 
                        /\ BurnMintMemory' = Append(BurnMintMemory, -amount)
                        /\ Map' = [Map EXCEPT ![user] = @ - amount]
                        /\ UNCHANGED Mintable

Transfer(userfr, userto, amount) == /\ Map[userfr] >= amount 
                                    /\ IF userfr = userto THEN UNCHANGED vars 
                                                          ELSE /\ Map' = [Map EXCEPT ![userfr] = @ - amount, ![userto] = @ + amount]
                                                               /\ UNCHANGED <<Mintable, TotalSupply, BurnMintMemory>>

CloseMint == /\ Mintable = TRUE
             /\ Mintable' = FALSE
             /\ UNCHANGED <<Map, TotalSupply, BurnMintMemory>>

Next == \/ \E user \in Users : NewUserJWallet(user)
        \/ \E user \in DOMAIN Map : ((\E amount \in 0..MaxTotalSupply : Mint(user, amount)) \/ (\E amount \in 0..TotalSupply : Burn(user, amount)))
        \/ \E userfr, userto \in DOMAIN Map, amount \in 0..TotalSupply : Transfer(userfr, userto, amount)
        \/ CloseMint     

TotalSupplyConstraint == TotalSupply <= MaxTotalSupply /\ TotalSupply = SumMap(Map)
                                                       /\ TotalSupply = SumMap(BurnMintMemory)

NoMint == []((Mintable = FALSE) => [](\A user \in DOMAIN Map, amount \in 0..MaxTotalSupply : ~ ENABLED Mint(user, amount)))

NewUserNoBalance == [][IF Cardinality(DOMAIN Map) < Cardinality(DOMAIN Map') THEN (\A u \in (DOMAIN Map' \ DOMAIN Map) : Map'[u] = 0) /\ \A v \in DOMAIN Map : Map[v] = Map'[v] ELSE TRUE]_vars

RightBehaviorWhenMapChanged == [][IF Map # Map' /\ Cardinality(DOMAIN Map) = Cardinality(DOMAIN Map') THEN                            
                                     \/ \E userfr, userto \in DOMAIN Map: /\ userfr # userto
                                                                          /\ Map'[userfr] < Map[userfr]
                                                                          /\ Map'[userto] > Map[userto]
                                                                          /\ Map'[userto] - Map[userto] = Map[userfr] - Map'[userfr]
                                                                          /\ \A v \in DOMAIN Map : v \notin {userfr, userto} => Map'[v] = Map[v]
                                                                          /\ Len(BurnMintMemory') = Len(BurnMintMemory)
                                     \/ \E user \in DOMAIN Map: /\ Map'[user] > Map[user]
                                                                /\ Len(BurnMintMemory') = Len(BurnMintMemory) + 1
                                                                /\ Mintable = TRUE
                                                                /\ \A v \in DOMAIN Map : v \notin {user} => Map'[v] = Map[v]
                                     \/ \E user \in DOMAIN Map: /\ Map'[user] < Map[user]
                                                                /\ Len(BurnMintMemory') = Len(BurnMintMemory) + 1
                                                                /\ \A v \in DOMAIN Map : v \notin {user} => Map'[v] = Map[v] 
                                                                        ELSE TRUE]_vars

LengthMemoryconstraint == Len(BurnMintMemory) <= 3

Spec == Init /\ [][Next]_vars

RandomSpec == RandomInit /\ [][Next]_vars

=============================================================================
