--------------------------- MODULE reliable_broadcast ---------------------------
EXTENDS 
    Naturals, FiniteSets, TLC, Bags
    
    
CONSTANT Process
CONSTANT Message


(* --algorithm reliable_broadcast 
variables 
    broadcast = [p \in Process |-> {}];
    delivered = [p \in Process |-> {}];
    happensBefore = [p \in Message |-> {}];
    available_messages = Message;

    network_outbox = [p \in Process |-> EmptyBag];
    network_delivered = [p \in Process |-> EmptyBag];
    beb_broadcast = [p \in Process |-> EmptyBag];
    beb_delivered = [p \in Process |-> EmptyBag]; 
    correctProcess \in SUBSET Process;
    max_mid = 0;
    local_delivered = [p \in Process |-> {}];

process client \in {[name |-> "client", proc |-> "p1"]}
    begin
        client_loop:
        while TRUE do
            with msg \in available_messages; p \in Process do
                available_messages := available_messages \ {msg};
                broadcast[p] := broadcast[p] \union {msg};
                happensBefore[msg] := delivered[p];
            end with
        end while
end process

fair process do_rb_broadcast \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}
    begin
        upon_broadcast:
        while TRUE do 
            with msg \in broadcast[self.proc]; mid = max_mid do
                broadcast[self.proc] := broadcast[self.proc] \ {msg};
                (* trigger rb-deliver: *)
                delivered[self.proc] := delivered[self.proc] \union {msg};
                (* keep track of unique ids: *)
                max_mid := max_mid + 1;
                local_delivered[self.proc] := local_delivered[self.proc] \union {mid}; 
                (* beb-broadcast *)
                beb_broadcast[self.proc] := beb_broadcast[self.proc] (+) SetToBag({[mid |-> mid, msg |-> msg]});
            end with
        end while
end process

fair process do_rb_receive \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process}
    begin
        upon_receive:
        while TRUE do
            with msg \in BagToSet(beb_delivered[self.proc]) do 
                when msg.mid \notin local_delivered[self.proc];
                local_delivered[self.proc] := local_delivered[self.proc] \union {msg.mid}; 
                beb_delivered[self.proc] := beb_delivered[self.proc] (-) SetToBag({msg});
                delivered[self.proc] := delivered[self.proc] \union {msg.msg};
                (* beb-broadcast again *)
                beb_broadcast[self.proc] := beb_broadcast[self.proc] (+) SetToBag({msg});
            end with
        end while
end process


fair process do_beb_broadcast \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process} 
    begin
        upon_broadcast:
        while TRUE do 
            with msg \in BagToSet(beb_broadcast[self.proc]) do
                beb_broadcast[self.proc] := beb_broadcast[self.proc] (-) SetToBag({msg});
                network_outbox[self.proc] := network_outbox[self.proc] (+) SetToBag({[rcv |-> q, msg |-> msg] : q \in Process })
            end with
        end while
end process

fair process do_beb_receive \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process}
    begin
        upon_receive:
        while TRUE do
            with msg \in BagToSet(network_delivered[self.proc]) do 
                network_delivered[self.proc] := network_delivered[self.proc] (-) SetToBag({msg});
                beb_delivered[self.proc] := beb_delivered[self.proc] (+) SetToBag({msg})
            end with
        end while
end process

fair process correct_network = [name |-> "correct_network", proc |-> "p1"]
    begin
        network_loop:
        while TRUE do
            with proc \in Process;  msg \in BagToSet(network_outbox[proc]) do
                when proc \in correctProcess;
                when msg.rcv \in correctProcess; 
                network_outbox[proc] := network_outbox[proc] (-) SetToBag({msg});
                network_delivered[msg.rcv] := network_delivered[msg.rcv] (+) SetToBag({msg.msg})
            end with
        end while
end process

(* the network for incorrect processes *)
process network = [name |-> "network", proc |-> "p1"]
    begin
        network_loop:
        while TRUE do
            with proc \in Process; msg \in BagToSet(network_outbox[proc]) do
                when proc \notin correctProcess \/ msg.rcv \notin correctProcess;
                network_outbox[proc] := network_outbox[proc] (-) SetToBag({msg});
                network_delivered[msg.rcv] := network_delivered[msg.rcv] (+) SetToBag({msg.msg})
            end with
        end while
end process


end algorithm *)
\* BEGIN TRANSLATION
\* Label upon_broadcast of process do_rb_broadcast at line 40 col 9 changed to upon_broadcast_
\* Label upon_receive of process do_rb_receive at line 57 col 9 changed to upon_receive_
\* Label network_loop of process correct_network at line 95 col 9 changed to network_loop_
VARIABLES broadcast, delivered, happensBefore, available_messages, 
          network_outbox, network_delivered, beb_broadcast, beb_delivered, 
          correctProcess, max_mid, local_delivered

vars == << broadcast, delivered, happensBefore, available_messages, 
           network_outbox, network_delivered, beb_broadcast, beb_delivered, 
           correctProcess, max_mid, local_delivered >>

ProcSet == ({[name |-> "client", proc |-> "p1"]}) \cup ({[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}) \cup ({[name |-> "do_beb_receive", proc |-> p] : p \in Process}) \cup ({[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}) \cup ({[name |-> "do_beb_receive", proc |-> p] : p \in Process}) \cup {[name |-> "correct_network", proc |-> "p1"]} \cup {[name |-> "network", proc |-> "p1"]}

Init == (* Global variables *)
        /\ broadcast = [p \in Process |-> {}]
        /\ delivered = [p \in Process |-> {}]
        /\ happensBefore = [p \in Message |-> {}]
        /\ available_messages = Message
        /\ network_outbox = [p \in Process |-> EmptyBag]
        /\ network_delivered = [p \in Process |-> EmptyBag]
        /\ beb_broadcast = [p \in Process |-> EmptyBag]
        /\ beb_delivered = [p \in Process |-> EmptyBag]
        /\ correctProcess \in SUBSET Process
        /\ max_mid = 0
        /\ local_delivered = [p \in Process |-> {}]

client(self) == /\ \E msg \in available_messages:
                     \E p \in Process:
                       /\ available_messages' = available_messages \ {msg}
                       /\ broadcast' = [broadcast EXCEPT ![p] = broadcast[p] \union {msg}]
                       /\ happensBefore' = [happensBefore EXCEPT ![msg] = delivered[p]]
                /\ UNCHANGED << delivered, network_outbox, network_delivered, 
                                beb_broadcast, beb_delivered, correctProcess, 
                                max_mid, local_delivered >>

do_rb_broadcast(self) == /\ \E msg \in broadcast[self.proc]:
                              LET mid == max_mid IN
                                /\ broadcast' = [broadcast EXCEPT ![self.proc] = broadcast[self.proc] \ {msg}]
                                /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg}]
                                /\ max_mid' = max_mid + 1
                                /\ local_delivered' = [local_delivered EXCEPT ![self.proc] = local_delivered[self.proc] \union {mid}]
                                /\ beb_broadcast' = [beb_broadcast EXCEPT ![self.proc] = beb_broadcast[self.proc] (+) SetToBag({[mid |-> mid, msg |-> msg]})]
                         /\ UNCHANGED << happensBefore, available_messages, 
                                         network_outbox, network_delivered, 
                                         beb_delivered, correctProcess >>

do_rb_receive(self) == /\ \E msg \in BagToSet(beb_delivered[self.proc]):
                            /\ msg.mid \notin local_delivered[self.proc]
                            /\ local_delivered' = [local_delivered EXCEPT ![self.proc] = local_delivered[self.proc] \union {msg.mid}]
                            /\ beb_delivered' = [beb_delivered EXCEPT ![self.proc] = beb_delivered[self.proc] (-) SetToBag({msg})]
                            /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg.msg}]
                            /\ beb_broadcast' = [beb_broadcast EXCEPT ![self.proc] = beb_broadcast[self.proc] (+) SetToBag({msg})]
                       /\ UNCHANGED << broadcast, happensBefore, 
                                       available_messages, network_outbox, 
                                       network_delivered, correctProcess, 
                                       max_mid >>

do_beb_broadcast(self) == /\ \E msg \in BagToSet(beb_broadcast[self.proc]):
                               /\ beb_broadcast' = [beb_broadcast EXCEPT ![self.proc] = beb_broadcast[self.proc] (-) SetToBag({msg})]
                               /\ network_outbox' = [network_outbox EXCEPT ![self.proc] = network_outbox[self.proc] (+) SetToBag({[rcv |-> q, msg |-> msg] : q \in Process })]
                          /\ UNCHANGED << broadcast, delivered, 
                                          happensBefore, available_messages, 
                                          network_delivered, beb_delivered, 
                                          correctProcess, max_mid, 
                                          local_delivered >>

do_beb_receive(self) == /\ \E msg \in BagToSet(network_delivered[self.proc]):
                             /\ network_delivered' = [network_delivered EXCEPT ![self.proc] = network_delivered[self.proc] (-) SetToBag({msg})]
                             /\ beb_delivered' = [beb_delivered EXCEPT ![self.proc] = beb_delivered[self.proc] (+) SetToBag({msg})]
                        /\ UNCHANGED << broadcast, delivered, happensBefore, 
                                        available_messages, network_outbox, 
                                        beb_broadcast, correctProcess, max_mid, 
                                        local_delivered >>

correct_network == /\ \E proc \in Process:
                        \E msg \in BagToSet(network_outbox[proc]):
                          /\ proc \in correctProcess
                          /\ msg.rcv \in correctProcess
                          /\ network_outbox' = [network_outbox EXCEPT ![proc] = network_outbox[proc] (-) SetToBag({msg})]
                          /\ network_delivered' = [network_delivered EXCEPT ![msg.rcv] = network_delivered[msg.rcv] (+) SetToBag({msg.msg})]
                   /\ UNCHANGED << broadcast, delivered, happensBefore, 
                                   available_messages, beb_broadcast, 
                                   beb_delivered, correctProcess, max_mid, 
                                   local_delivered >>

network == /\ \E proc \in Process:
                \E msg \in BagToSet(network_outbox[proc]):
                  /\ proc \notin correctProcess \/ msg.rcv \notin correctProcess
                  /\ network_outbox' = [network_outbox EXCEPT ![proc] = network_outbox[proc] (-) SetToBag({msg})]
                  /\ network_delivered' = [network_delivered EXCEPT ![msg.rcv] = network_delivered[msg.rcv] (+) SetToBag({msg.msg})]
           /\ UNCHANGED << broadcast, delivered, happensBefore, 
                           available_messages, beb_broadcast, beb_delivered, 
                           correctProcess, max_mid, local_delivered >>

Next == correct_network \/ network
           \/ (\E self \in {[name |-> "client", proc |-> "p1"]}: client(self))
           \/ (\E self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}: do_rb_broadcast(self))
           \/ (\E self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process}: do_rb_receive(self))
           \/ (\E self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}: do_beb_broadcast(self))
           \/ (\E self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process}: do_beb_receive(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process} : WF_vars(do_rb_broadcast(self))
        /\ \A self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process} : WF_vars(do_rb_receive(self))
        /\ \A self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process} : WF_vars(do_beb_broadcast(self))
        /\ \A self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process} : WF_vars(do_beb_receive(self))
        /\ WF_vars(correct_network)

\* END TRANSLATION


RbMessage == [mid: Nat, msg: Message]
OutboxMessage == [rcv: Process, msg: RbMessage]


TypeInv ==
    /\ broadcast \in [Process -> SUBSET Message]
    /\ delivered \in [Process -> SUBSET Message]
    /\ happensBefore \in [Message -> SUBSET Message]
    /\ \A p \in Process: IsABag(beb_broadcast[p]) /\ BagToSet(beb_broadcast[p]) \in SUBSET RbMessage
    /\ \A p \in Process: IsABag(beb_delivered[p]) /\ BagToSet(beb_delivered[p]) \in SUBSET RbMessage
    /\ \A p \in Process: IsABag(network_outbox[p]) /\ BagToSet(network_outbox[p]) \in SUBSET OutboxMessage
    /\ \A p \in Process: IsABag(network_delivered[p]) /\ BagToSet(network_delivered[p]) \in SUBSET RbMessage
    /\ correctProcess \in SUBSET Process


(* For any two correct processes i and j,
   every message broadcast by i is eventually delivered by j. *)
Validity == 
    [](\A i \in Process, j \in Process: i \in correctProcess /\ j \in correctProcess => 
         \A msg \in Message: msg \in broadcast[i] 
            => <>(msg \in delivered[j]))

(*
 If a message m is delivered by some correct process i, 
 then m is eventually delivered by every correct process j.
*)
Agreement == 
    [](\A msg \in Message: \A i \in Process: i \in correctProcess => 
        (msg \in delivered[i]
             => <>(\A j \in Process : j \in correctProcess => 
                        msg \in delivered[j])))

(*
 If a message m is delivered by some process i, 
 then m is eventually delivered by every correct process j.
*)
UniformAgreement == 
    [](\A msg \in Message: \A i \in Process: 
        (msg \in delivered[i]
             => <>(\A j \in Process : j \in correctProcess => 
                        msg \in delivered[j])))

(* Causal delivery: *)
CausalDelivery ==
    [](\A m \in Message: \A p \in Process: \A m2 \in Message: 
        m \in delivered[p] /\ m2 \in happensBefore[m] => m2 \in delivered[p]) 


=============================================================================
\* Modification History
\* Last modified Fri Jun 21 10:55:00 CEST 2019 by peter
\* Created Sat May 04 18:36:34 CEST 2019 by peter
