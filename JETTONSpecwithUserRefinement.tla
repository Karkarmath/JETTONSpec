-------------------- MODULE JETTONSpecwithUserRefinement --------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxTotalSupply, Users

ASSUME MaxTotalSupply \in Nat /\ MaxTotalSupply > 0

VARIABLES MsgQueue,
          Admin,
          Map,
          TotalSupply,
          Mintable,
          BurnMintMemory

JSpecU == INSTANCE JETTONSpecwithUser

vars == <<JSpecU!vars, MsgQueue, Admin>>

Msg == Head(MsgQueue)

TypeOK == /\ JSpecU!TypeOK
          /\ Admin \in Users
          /\ MsgQueue \in Seq([type: {"NewUser", "Transfer", "Burn", "Mint", "ChangeAdmin", "CloseMint"},
                               body: {<< >>} \cup [1..1 -> Users] \cup Users \X Users \X Nat \cup Users \X Nat,
                               sender: Users])

Init == /\ JSpecU!Init
        /\ \E u \in Users : Admin = u
        /\ MsgQueue = << >>

NewUserJWalletSend(sender, destination) == /\ MsgQueue' = Append(MsgQueue, [type |-> "NewUser", body |-> <<destination>>, sender |-> sender])
                                           /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

TransferSend(sender, destination, userto, amount) == /\ MsgQueue' = Append(MsgQueue, [type |-> "Transfer", body |-> <<destination, userto, amount>>, sender |-> sender])
                                                     /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

BurnSend(sender, destination, amount) == /\ MsgQueue' = Append(MsgQueue, [type |-> "Burn", body |-> <<destination, amount>>, sender |-> sender])
                                         /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

MintSend(sender, destination, amount) == /\ MsgQueue' = Append(MsgQueue, [type |-> "Mint", body |-> <<destination, amount>>, sender |-> sender])
                                         /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

ChangeAdminSend(sender, destination) == /\ MsgQueue' = Append(MsgQueue, [type |-> "ChangeAdmin", body |-> <<destination>>, sender |-> sender])
                                        /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

CloseMintSend(sender) == /\ MsgQueue' = Append(MsgQueue, [type |-> "CloseMint", body |-> << >>, sender |-> sender])
                         /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

SendMsg == \E sender, destination, userto \in Users : \/ (\E amount \in 0..TotalSupply : \/ BurnSend(sender, destination, amount)
                                                                                         \/ TransferSend(sender, destination, userto, amount))
                                                      \/ (\E amount \in 0..MaxTotalSupply : MintSend(sender, destination, amount))
                                                      \/ NewUserJWalletSend(sender, destination)
                                                      \/ ChangeAdminSend(sender, destination)
                                                      \/ CloseMintSend(sender)

NewUserJWalletRcv == /\ MsgQueue # << >>
                     /\ Msg.type = "NewUser"
                     /\ MsgQueue' = Tail(MsgQueue)
                     /\ JSpecU!NewUserJWallet(Msg.body[1])
                     /\ UNCHANGED Admin

TransferRcv == /\ MsgQueue # << >>
               /\ Msg.type = "Transfer"
               /\ IF Msg.sender = Msg.body[1] /\ Msg.body[1] \in DOMAIN Map THEN IF Msg.body[2] \in DOMAIN Map THEN /\ JSpecU!Transfer(Msg.body[1], Msg.body[2], Msg.body[3])
                                                                                                                    /\ MsgQueue' = Tail(MsgQueue)
                                                                                                                    /\ UNCHANGED Admin
                                                                                                               ELSE /\ JSpecU!NewUserJWallet(Msg.body[2])
                                                                                                                    /\ UNCHANGED <<Admin, MsgQueue>>
                                                                            ELSE /\ MsgQueue' = Tail(MsgQueue)
                                                                                 /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

BurnRcv == /\ MsgQueue # << >>
           /\ Msg.type = "Burn"
           /\ IF Msg.sender = Msg.body[1] /\ Msg.body[1] \in DOMAIN Map THEN /\ JSpecU!Burn(Msg.body[1], Msg.body[2])
                                                                             /\ MsgQueue' = Tail(MsgQueue)
                                                                             /\ UNCHANGED Admin
                                                                        ELSE /\ MsgQueue' = Tail(MsgQueue)
                                                                             /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

MintRcv == /\ MsgQueue # << >>
           /\ Msg.type = "Mint"
           /\ IF Msg.sender = Admin THEN /\ IF Msg.body[1] \in DOMAIN Map THEN /\ JSpecU!Mint(Msg.body[1], Msg.body[2])                                                        
                                                                               /\ MsgQueue' = Tail(MsgQueue)
                                                                               /\ UNCHANGED Admin
                                                                          ELSE /\ JSpecU!NewUserJWallet(Msg.body[1])
                                                                               /\ UNCHANGED <<Admin, MsgQueue>>
                                    ELSE /\ MsgQueue' = Tail(MsgQueue)
                                         /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

ChangeAdminRcv == /\ MsgQueue # << >>
                  /\ Msg.type = "ChangeAdmin"
                  /\ IF Msg.sender = Admin THEN /\ Admin' = Msg.body[1]
                                                /\ MsgQueue' = Tail(MsgQueue)
                                                /\ UNCHANGED <<Map, TotalSupply, Mintable, BurnMintMemory>>
                                           ELSE /\ MsgQueue' = Tail(MsgQueue)
                                                /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

CloseMintRcv == /\ MsgQueue # << >>
                /\ Msg.type = "CloseMint"
                /\ IF Msg.sender = Admin THEN /\ JSpecU!CloseMint 
                                              /\ MsgQueue' = Tail(MsgQueue)
                                              /\ UNCHANGED Admin
                                         ELSE /\ MsgQueue' = Tail(MsgQueue)
                                              /\ UNCHANGED <<Admin, Map, TotalSupply, Mintable, BurnMintMemory>>

RcvMsg == \/ NewUserJWalletRcv
          \/ TransferRcv
          \/ BurnRcv
          \/ MintRcv
          \/ ChangeAdminRcv
          \/ CloseMintRcv

LenMsgQueueConstraint == Len(MsgQueue) <= 2

LengthMemoryconstraint == Len(BurnMintMemory) <= 3

Next == SendMsg \/ RcvMsg

Spec == Init /\ [][Next]_vars

HighlevelSpec == JSpecU!Spec
=============================================================================