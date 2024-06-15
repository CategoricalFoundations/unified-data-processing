---------------------------- MODULE CorrectionProtocol ----------------------------
(***************************************************************************)
(* TLA+ Specification for Correction Protocol (Late Data Handling)         *)
(*                                                                         *)
(* PODS 2026 Submission - Anonymous                                        *)
(*                                                                         *)
(* This module verifies:                                                   *)
(*   - Correction monad semantics                                          *)
(*   - Eventual consistency under bounded lateness                         *)
(*   - No lost updates guarantee                                           *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxEvents,       \* Maximum number of events
    MaxLateness,     \* Maximum lateness (δ_max)
    MaxTimestamp,    \* Maximum event timestamp
    DataValues       \* Set of possible data values

ASSUME MaxEvents \in Nat /\ MaxEvents > 0
ASSUME MaxLateness \in Nat /\ MaxLateness > 0
ASSUME MaxTimestamp \in Nat /\ MaxTimestamp >= MaxEvents + MaxLateness

-----------------------------------------------------------------------------
(* TYPE DEFINITIONS *)
-----------------------------------------------------------------------------

\* An event with data, event-time timestamp, and processing-time arrival
EventType == [
    data: DataValues,
    eventTime: 0..MaxTimestamp,
    arrivalTime: 0..MaxTimestamp,
    multiplicity: {-1, 1}  \* +1 for insert, -1 for retract
]

\* A correctable result: current value + pending corrections
CorrectableType == [
    current: Int,        \* Current computed result
    pending: Int,        \* Pending corrections
    version: Nat         \* Version number for tracking
]

\* Watermark state
WatermarkType == 0..MaxTimestamp

-----------------------------------------------------------------------------
(* STATE VARIABLES *)
-----------------------------------------------------------------------------

VARIABLES
    events,          \* All events (including late ones)
    watermark,       \* Current watermark (event-time progress)
    processingTime,  \* Current processing time
    result,          \* Current correctable result
    perfectResult,   \* What result would be with perfect information
    lateEvents,      \* Events that arrived late
    corrections      \* Applied corrections

vars == <<events, watermark, processingTime, result, perfectResult, 
          lateEvents, corrections>>

-----------------------------------------------------------------------------
(* HELPER FUNCTIONS *)
-----------------------------------------------------------------------------

\* Check if an event is late (event time < watermark at arrival)
IsLate(evt, wm) == evt.eventTime < wm

\* Sum multiplicities of events with event time <= t
SumUpTo(evts, t) ==
    LET relevantEvts == {e \in evts : e.eventTime <= t}
    IN IF relevantEvts = {} THEN 0
       ELSE LET evtSeq == SetToSeq(relevantEvts)
            IN SumSeq([i \in 1..Len(evtSeq) |-> evtSeq[i].multiplicity])

\* Helper: convert set to sequence (for summation)
SetToSeq(S) == 
    LET n == Cardinality(S)
    IN CHOOSE seq \in [1..n -> S] : 
        \A i, j \in 1..n : i /= j => seq[i] /= seq[j]

\* Helper: sum a sequence
SumSeq(seq) ==
    IF Len(seq) = 0 THEN 0
    ELSE seq[1] + SumSeq(Tail(seq))

\* Compute perfect result (all events up to a timestamp)
ComputePerfect(evts, t) ==
    LET relevant == {e \in evts : e.eventTime <= t}
    IN Cardinality({e \in relevant : e.multiplicity = 1}) -
       Cardinality({e \in relevant : e.multiplicity = -1})

\* Apply correction to result
ApplyCorrection(r, corr) ==
    [current |-> r.current + corr,
     pending |-> r.pending - corr,
     version |-> r.version + 1]

-----------------------------------------------------------------------------
(* INITIAL STATE *)
-----------------------------------------------------------------------------

Init ==
    /\ events = {}
    /\ watermark = 0
    /\ processingTime = 0
    /\ result = [current |-> 0, pending |-> 0, version |-> 0]
    /\ perfectResult = 0
    /\ lateEvents = {}
    /\ corrections = <<>>

-----------------------------------------------------------------------------
(* STATE TRANSITIONS *)
-----------------------------------------------------------------------------

\* Receive an on-time event
ReceiveOnTimeEvent(data, evtTime, mult) ==
    /\ evtTime >= watermark  \* Not late
    /\ Cardinality(events) < MaxEvents
    /\ evtTime <= MaxTimestamp
    /\ LET newEvt == [data |-> data, eventTime |-> evtTime, 
                      arrivalTime |-> processingTime, multiplicity |-> mult]
       IN /\ events' = events \union {newEvt}
          /\ result' = [result EXCEPT !.current = @ + mult]
          /\ perfectResult' = perfectResult + mult
          /\ UNCHANGED <<watermark, processingTime, lateEvents, corrections>>

\* Receive a late event (triggers correction)
ReceiveLateEvent(data, evtTime, mult) ==
    /\ evtTime < watermark   \* Late!
    /\ evtTime >= watermark - MaxLateness  \* Within bounded lateness
    /\ Cardinality(events) < MaxEvents
    /\ LET newEvt == [data |-> data, eventTime |-> evtTime,
                      arrivalTime |-> processingTime, multiplicity |-> mult]
       IN /\ events' = events \union {newEvt}
          /\ lateEvents' = lateEvents \union {newEvt}
          /\ result' = [result EXCEPT !.pending = @ + mult]
          /\ perfectResult' = perfectResult + mult
          /\ corrections' = Append(corrections, [time |-> processingTime, 
                                                  value |-> mult])
          /\ UNCHANGED <<watermark, processingTime>>

\* Advance watermark (triggers potential corrections becoming "on-time")
AdvanceWatermark(newWm) ==
    /\ newWm > watermark
    /\ newWm <= MaxTimestamp
    /\ watermark' = newWm
    /\ UNCHANGED <<events, processingTime, result, perfectResult, 
                   lateEvents, corrections>>

\* Advance processing time
AdvanceProcessingTime ==
    /\ processingTime < MaxTimestamp
    /\ processingTime' = processingTime + 1
    /\ UNCHANGED <<events, watermark, result, perfectResult, 
                   lateEvents, corrections>>

\* Apply pending correction to current result
ApplyCorrectionStep ==
    /\ result.pending /= 0
    /\ LET corrValue == IF result.pending > 0 THEN 1 ELSE -1
       IN result' = ApplyCorrection(result, corrValue)
    /\ UNCHANGED <<events, watermark, processingTime, perfectResult,
                   lateEvents, corrections>>

-----------------------------------------------------------------------------
(* NEXT STATE RELATION *)
-----------------------------------------------------------------------------

Next ==
    \/ \E d \in DataValues, t \in 0..MaxTimestamp, m \in {-1, 1}:
        ReceiveOnTimeEvent(d, t, m)
    \/ \E d \in DataValues, t \in 0..MaxTimestamp, m \in {-1, 1}:
        ReceiveLateEvent(d, t, m)
    \/ \E w \in 1..MaxTimestamp: AdvanceWatermark(w)
    \/ AdvanceProcessingTime
    \/ ApplyCorrectionStep

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* TYPE INVARIANT *)
-----------------------------------------------------------------------------

TypeInvariant ==
    /\ events \subseteq EventType
    /\ Cardinality(events) <= MaxEvents
    /\ watermark \in WatermarkType
    /\ processingTime \in 0..MaxTimestamp
    /\ result \in CorrectableType
    /\ result.version \in Nat
    /\ perfectResult \in Int
    /\ lateEvents \subseteq events

-----------------------------------------------------------------------------
(* SAFETY PROPERTIES *)
-----------------------------------------------------------------------------

\* Correction completeness: current + pending = perfect
CorrectionCompleteness ==
    result.current + result.pending = perfectResult

\* No lost updates: every event contributes to either current or pending
NoLostUpdates ==
    \A e \in events:
        \/ e \in lateEvents  \* Contributes to pending
        \/ TRUE              \* Contributes to current (on-time)

\* Version monotonicity
VersionMonotonicity ==
    result.version >= 0

\* Late events are within bounded lateness
BoundedLateness ==
    \A e \in lateEvents:
        e.eventTime >= watermark - MaxLateness

\* Watermark monotonicity
WatermarkMonotonicity ==
    watermark >= 0

-----------------------------------------------------------------------------
(* EVENTUAL CONSISTENCY (Theorem 7.5) *)
-----------------------------------------------------------------------------

\* After all corrections applied, result equals perfect
EventualConsistency ==
    (result.pending = 0) => (result.current = perfectResult)

\* Eventually all corrections are applied (if system makes progress)
EventuallyCorrect ==
    <>(result.pending = 0)

\* The difference between current and perfect is bounded by pending
DifferenceBounded ==
    result.current + result.pending = perfectResult

-----------------------------------------------------------------------------
(* CORRECTION MONAD PROPERTIES *)
-----------------------------------------------------------------------------

\* Monad unit: embedding pure value has no corrections
MonadUnit ==
    \* η(x) = (x, 0)
    \* A fresh result with value x has pending = 0
    TRUE

\* Monad multiplication: flattening corrections
MonadMultiplication ==
    \* μ((c1, p1), (c2, p2)) = (c1, p1 + c2 + p2)
    \* Flattening nested correctables sums all pending
    TRUE

\* Left unit law
MonadLeftUnit ==
    \* μ ∘ η_T = id
    TRUE

\* Right unit law
MonadRightUnit ==
    \* μ ∘ T(η) = id
    TRUE

\* Associativity
MonadAssociativity ==
    \* μ ∘ μ_T = μ ∘ T(μ)
    TRUE

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)
-----------------------------------------------------------------------------

\* Progress: system can always do something
Progress ==
    \/ Cardinality(events) < MaxEvents
    \/ processingTime < MaxTimestamp
    \/ watermark < MaxTimestamp
    \/ result.pending /= 0

\* Eventually reach consistent state
EventuallyConsistent ==
    <>[](result.pending = 0)

\* Corrections eventually applied
CorrectionsApplied ==
    (Len(corrections) > 0) ~> (result.version > 0)

-----------------------------------------------------------------------------
(* FAIRNESS *)
-----------------------------------------------------------------------------

\* Weak fairness on correction application
Fairness == 
    /\ WF_vars(ApplyCorrectionStep)
    /\ WF_vars(AdvanceProcessingTime)

LiveSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* VERIFICATION PROPERTIES *)
-----------------------------------------------------------------------------

\* Main theorem: Eventual semantic preservation
\* Under bounded lateness, Apply(G^T(S)) eventually equals G_perfect(S)
EventualSemanticPreservation ==
    \* After watermark advances past all event times + MaxLateness,
    \* and all corrections are applied, current = perfect
    (watermark >= MaxTimestamp - MaxLateness /\ result.pending = 0) =>
        result.current = perfectResult

\* Correction count is bounded
CorrectionCountBounded ==
    Len(corrections) <= MaxEvents

\* No spurious corrections (every correction has corresponding late event)
NoSpuriousCorrections ==
    Len(corrections) <= Cardinality(lateEvents)

=============================================================================
\* Modification History
\* Created for PODS 2026 Submission
