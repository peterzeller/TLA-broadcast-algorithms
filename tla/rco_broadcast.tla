--------------------------- MODULE rco_broadcast ---------------------------
EXTENDS 
    Naturals, FiniteSets, TLC, Bags
    
    
CONSTANT Process
CONSTANT Message

(* vector clock library *)
vc_initial == [p \in Process |-> 0]
vc_leq(vc1, vc2) == \A p \in Process: vc1[p] <= vc2[p] 

(* --algorithm rco_broadcast
variables 
    broadcast = [p \in Process |-> {}];
    delivered = [p \in Process |-> {}];
    happensBefore = [p \in Message |-> {}];
    available_messages = Message;
    rb_broadcast = [p \in Process |-> EmptyBag];
    rb_delivered = [p \in Process |-> EmptyBag]; 
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

fair process causal_broadcast \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Process}
    variables pending = {}, VC = [p \in Process |-> 0]; 
    begin
        causal_broadcast:
        while TRUE do 
            either (* upon rco-broadcast *)
                with msg \in broadcast[self.proc] do
                    broadcast[self.proc] := broadcast[self.proc] \ {msg};
                    (* trigger rco-deliver(self, m) *)
                    delivered[self.proc] := delivered[self.proc] \union {msg};
                    (* trigger rb-broadcast(VC, m) *)
                    rb_broadcast[self.proc] := rb_broadcast[self.proc]
                                  (+) SetToBag({[sdr |-> self.proc, vc |-> VC, msg |-> msg]});
                    VC[self.proc] := VC[self.proc] + 1;
                end with
            or (* upon rb-deliver *)
                with msg \in BagToSet(rb_delivered[self.proc]) do
                    when msg.sdr # self.proc;
                    rb_delivered[self.proc] := rb_delivered[self.proc] (-) SetToBag({msg});
                    pending := pending \union {msg};
                end with
            or
                (* deliver loop *)
                with msg \in pending do
                    when vc_leq(msg.vc, VC);
                    pending := pending \ {msg};
                    (* trigger rco-deliver *)
                    delivered[self.proc] := delivered[self.proc] \union {msg.msg};
                    VC[msg.sdr] := VC[msg.sdr] + 1;
                end with
            end either
        end while
end process

fair process do_rb_deliver \in {[name |-> "do_rb_deliver", proc |-> "p1"]}
    begin
        upon_receive:
        while TRUE do
            with proc \in Process; msg \in BagToSet(rb_broadcast[proc]); receivers \in SUBSET Process do
                (* when sender is correct, must deliver to self *)
                when proc \in correctProcess => proc \in receivers;
                (* when delivered to one correct process, must deliver to all *)
                when (\E p \in receivers: p \in correctProcess) =>
                        \A p \in correctProcess: p \in receivers;  
                rb_broadcast[proc] := rb_broadcast[proc] (-) SetToBag({msg});
                rb_delivered := [ p \in Process |-> IF p \in receivers THEN rb_delivered[p] (+) SetToBag({msg}) ELSE rb_delivered[p]]
            end with
        end while
end process



end algorithm *)
\* BEGIN TRANSLATION
\* Label causal_broadcast of process causal_broadcast at line 39 col 9 changed to causal_broadcast_
VARIABLES broadcast, delivered, happensBefore, rb_broadcast, rb_delivered, 
          correctProcess, available_messages, pending, VC

vars == << broadcast, delivered, happensBefore, rb_broadcast, 
           rb_delivered, correctProcess, available_messages, pending, VC >>

ProcSet == ({[name |-> "client", proc |-> "p1"]}) \cup ({[name |-> "do_causal_broadcast", proc |-> p] : p \in Process}) \cup ({[name |-> "do_rb_deliver", proc |-> "p1"]})

Init == (* Global variables *)
        /\ broadcast = [p \in Process |-> {}]
        /\ delivered = [p \in Process |-> {}]
        /\ happensBefore = [p \in Message |-> {}]
        /\ rb_broadcast = [p \in Process |-> EmptyBag]
        /\ rb_delivered = [p \in Process |-> EmptyBag]
        /\ correctProcess \in SUBSET Process
        /\ available_messages = Message
        (* Process causal_broadcast *)
        /\ pending = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Process} |-> {}]
        /\ VC = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Process} |-> [p \in Process |-> 0]]

client(self) == /\ \E msg \in available_messages:
                     \E p \in Process:
                       /\ available_messages' = available_messages \ {msg}
                       /\ broadcast' = [broadcast EXCEPT ![p] = broadcast[p] \union {msg}]
                       /\ happensBefore' = [happensBefore EXCEPT ![msg] = delivered[p]]
                /\ UNCHANGED << delivered, rb_broadcast, rb_delivered, 
                                correctProcess, pending, VC >>

causal_broadcast(self) == /\ \/ /\ \E msg \in broadcast[self.proc]:
                                     /\ broadcast' = [broadcast EXCEPT ![self.proc] = broadcast[self.proc] \ {msg}]
                                     /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg}]
                                     /\ rb_broadcast' = [rb_broadcast EXCEPT ![self.proc] = rb_broadcast[self.proc] (+) SetToBag({[sdr |-> self.proc, vc |-> VC[self], msg |-> msg]})]
                                     /\ VC' = [VC EXCEPT ![self][self.proc] = VC[self][self.proc] + 1]
                                /\ UNCHANGED <<rb_delivered, pending>>
                             \/ /\ \E msg \in BagToSet(rb_delivered[self.proc]):
                                     /\ msg.sdr # self.proc
                                     /\ rb_delivered' = [rb_delivered EXCEPT ![self.proc] = rb_delivered[self.proc] (-) SetToBag({msg})]
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \union {msg}]
                                /\ UNCHANGED <<broadcast, delivered, rb_broadcast, VC>>
                             \/ /\ \E msg \in pending[self]:
                                     /\ vc_leq(msg.vc, VC[self])
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \ {msg}]
                                     /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg.msg}]
                                     /\ VC' = [VC EXCEPT ![self][msg.sdr] = VC[self][msg.sdr] + 1]
                                /\ UNCHANGED <<broadcast, rb_broadcast, rb_delivered>>
                          /\ UNCHANGED << happensBefore, correctProcess, 
                                          available_messages >>

do_rb_deliver(self) == /\ \E proc \in Process:
                            \E msg \in BagToSet(rb_broadcast[proc]):
                              \E receivers \in SUBSET Process:
                                /\ proc \in correctProcess => proc \in receivers
                                /\ (\E p \in receivers: p \in correctProcess) =>
                                      \A p \in correctProcess: p \in receivers
                                /\ rb_broadcast' = [rb_broadcast EXCEPT ![proc] = rb_broadcast[proc] (-) SetToBag({msg})]
                                /\ rb_delivered' = [ p \in Process |-> IF p \in receivers THEN rb_delivered[p] (+) SetToBag({msg}) ELSE rb_delivered[p]]
                       /\ UNCHANGED << broadcast, delivered, happensBefore, 
                                       correctProcess, available_messages, 
                                       pending, VC >>

Next == (\E self \in {[name |-> "client", proc |-> "p1"]}: client(self))
           \/ (\E self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Process}: causal_broadcast(self))
           \/ (\E self \in {[name |-> "do_rb_deliver", proc |-> "p1"]}: do_rb_deliver(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Process} : WF_vars(causal_broadcast(self))
        /\ \A self \in {[name |-> "do_rb_deliver", proc |-> "p1"]} : WF_vars(do_rb_deliver(self))

\* END TRANSLATION


RbMessage == [sdr: Process, vc: [Process -> Nat], msg: Message]

TypeInv ==
    /\ broadcast \in [Process -> SUBSET Message]
    /\ delivered \in [Process -> SUBSET Message]
    /\ happensBefore \in [Message -> SUBSET Message]
    /\ \A p \in Process: IsABag(rb_broadcast[p]) /\ BagToSet(rb_broadcast[p]) \in SUBSET RbMessage
    /\ \A p \in Process: IsABag(rb_delivered[p]) /\ BagToSet(rb_delivered[p]) \in SUBSET RbMessage
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
\* Last modified Tue May 07 12:04:10 CEST 2019 by peter
\* Created Sat May 04 18:36:34 CEST 2019 by peter
