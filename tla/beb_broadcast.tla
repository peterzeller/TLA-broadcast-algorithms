--------------------------- MODULE beb_broadcast ---------------------------
EXTENDS
    Naturals, FiniteSets, TLC, Bags

CONSTANT Process
CONSTANT Message

(* --algorithm beb_broadcast
variables
    broadcast = [p \in Process |-> {}];
    delivered = [p \in Process |-> {}];
    happensBefore = [p \in Message |-> {}];
    available_messages = Message;

    network_outbox = [p \in Process |-> EmptyBag];
    network_delivered = [p \in Process |-> EmptyBag];
    correctProcess \in SUBSET Process;

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

fair process do_beb_broadcast \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}
    begin
        upon_broadcast:
        while TRUE do
            with msg \in broadcast[self.proc] do
                broadcast[self.proc] := broadcast[self.proc] \ {msg};
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
                delivered[self.proc] := delivered[self.proc] \union {msg}
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
\* BEGIN TRANSLATION PCal-f4b7de81c0277b4094add302380b0f60
\* Label network_loop of process correct_network at line 56 col 9 changed to network_loop_
VARIABLES broadcast, delivered, happensBefore, available_messages, 
          network_outbox, network_delivered, correctProcess

vars == << broadcast, delivered, happensBefore, available_messages, 
           network_outbox, network_delivered, correctProcess >>

ProcSet == ({[name |-> "client", proc |-> "p1"]}) \cup ({[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}) \cup ({[name |-> "do_beb_receive", proc |-> p] : p \in Process}) \cup {[name |-> "correct_network", proc |-> "p1"]} \cup {[name |-> "network", proc |-> "p1"]}

Init == (* Global variables *)
        /\ broadcast = [p \in Process |-> {}]
        /\ delivered = [p \in Process |-> {}]
        /\ happensBefore = [p \in Message |-> {}]
        /\ available_messages = Message
        /\ network_outbox = [p \in Process |-> EmptyBag]
        /\ network_delivered = [p \in Process |-> EmptyBag]
        /\ correctProcess \in SUBSET Process

client(self) == /\ \E msg \in available_messages:
                     \E p \in Process:
                       /\ available_messages' = available_messages \ {msg}
                       /\ broadcast' = [broadcast EXCEPT ![p] = broadcast[p] \union {msg}]
                       /\ happensBefore' = [happensBefore EXCEPT ![msg] = delivered[p]]
                /\ UNCHANGED << delivered, network_outbox, network_delivered, 
                                correctProcess >>

do_beb_broadcast(self) == /\ \E msg \in broadcast[self.proc]:
                               /\ broadcast' = [broadcast EXCEPT ![self.proc] = broadcast[self.proc] \ {msg}]
                               /\ network_outbox' = [network_outbox EXCEPT ![self.proc] = network_outbox[self.proc] (+) SetToBag({[rcv |-> q, msg |-> msg] : q \in Process })]
                          /\ UNCHANGED << delivered, happensBefore, 
                                          available_messages, 
                                          network_delivered, correctProcess >>

do_beb_receive(self) == /\ \E msg \in BagToSet(network_delivered[self.proc]):
                             /\ network_delivered' = [network_delivered EXCEPT ![self.proc] = network_delivered[self.proc] (-) SetToBag({msg})]
                             /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg}]
                        /\ UNCHANGED << broadcast, happensBefore, 
                                        available_messages, network_outbox, 
                                        correctProcess >>

correct_network == /\ \E proc \in Process:
                        \E msg \in BagToSet(network_outbox[proc]):
                          /\ proc \in correctProcess
                          /\ msg.rcv \in correctProcess
                          /\ network_outbox' = [network_outbox EXCEPT ![proc] = network_outbox[proc] (-) SetToBag({msg})]
                          /\ network_delivered' = [network_delivered EXCEPT ![msg.rcv] = network_delivered[msg.rcv] (+) SetToBag({msg.msg})]
                   /\ UNCHANGED << broadcast, delivered, happensBefore, 
                                   available_messages, correctProcess >>

network == /\ \E proc \in Process:
                \E msg \in BagToSet(network_outbox[proc]):
                  /\ proc \notin correctProcess \/ msg.rcv \notin correctProcess
                  /\ network_outbox' = [network_outbox EXCEPT ![proc] = network_outbox[proc] (-) SetToBag({msg})]
                  /\ network_delivered' = [network_delivered EXCEPT ![msg.rcv] = network_delivered[msg.rcv] (+) SetToBag({msg.msg})]
           /\ UNCHANGED << broadcast, delivered, happensBefore, 
                           available_messages, correctProcess >>

Next == correct_network \/ network
           \/ (\E self \in {[name |-> "client", proc |-> "p1"]}: client(self))
           \/ (\E self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process}: do_beb_broadcast(self))
           \/ (\E self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process}: do_beb_receive(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {[name |-> "do_beb_broadcast", proc |-> p] : p \in Process} : WF_vars(do_beb_broadcast(self))
        /\ \A self \in {[name |-> "do_beb_receive", proc |-> p] : p \in Process} : WF_vars(do_beb_receive(self))
        /\ WF_vars(correct_network)

\* END TRANSLATION TLA-e4f3f8fb7c963cf899744bd22bdc8ac2


OutboxMessage == [rcv: Process, msg: Message]

TypeInv ==
    /\ broadcast \in [Process -> SUBSET Message]
    /\ delivered \in [Process -> SUBSET Message]
    /\ happensBefore \in [Message -> SUBSET Message]
    /\ \A p \in Process: IsABag(network_outbox[p]) /\ BagToSet(network_outbox[p]) \in SUBSET OutboxMessage
    /\ \A p \in Process: IsABag(network_delivered[p]) /\ BagToSet(network_delivered[p]) \in SUBSET Message
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
\* Last modified Fri Jun 21 10:55:39 CEST 2019 by peter
\* Created Sat May 04 18:36:34 CEST 2019 by peter
