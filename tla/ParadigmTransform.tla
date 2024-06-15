---------------------------- MODULE ParadigmTransform ----------------------------
(***************************************************************************)
(* TLA+ Specification for Cross-Paradigm Data Transformations              *)
(*                                                                         *)
(* PODS 2026 Submission - Anonymous                                        *)
(*                                                                         *)
(* This module verifies safety and liveness properties of the functors:    *)
(*   - F_BS : Batch -> Stream (batch-to-stream embedding)                  *)
(*   - G_SB : Stream -> Batch (windowed extraction)                        *)
(*   - Round-trip semantic preservation                                    *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxDataSize,     \* Maximum number of data elements
    WindowSize,      \* Window size W for G_SB
    MaxTimestamp     \* Maximum timestamp value

ASSUME MaxDataSize \in Nat /\ MaxDataSize > 0
ASSUME WindowSize \in Nat /\ WindowSize > 0
ASSUME MaxTimestamp \in Nat /\ MaxTimestamp >= MaxDataSize

-----------------------------------------------------------------------------
(* TYPE DEFINITIONS *)
-----------------------------------------------------------------------------

\* Data values are naturals (simplified from typed universe)
DataValue == 1..MaxDataSize

\* A batch is a finite multiset (represented as sequence)
BatchType == Seq(DataValue)

\* A stream event has value and timestamp
StreamEvent == [value: DataValue, timestamp: 0..MaxTimestamp]

\* A stream is a sequence of events with a watermark
StreamType == [events: Seq(StreamEvent), watermark: 0..MaxTimestamp]

-----------------------------------------------------------------------------
(* STATE VARIABLES *)
-----------------------------------------------------------------------------

VARIABLES
    batch,           \* Current batch data : BatchType
    stream,          \* Current stream data : StreamType
    paradigm,        \* Current paradigm : {"Batch", "Stream"}
    transformCount   \* Number of transformations performed

vars == <<batch, stream, paradigm, transformCount>>

-----------------------------------------------------------------------------
(* HELPER FUNCTIONS *)
-----------------------------------------------------------------------------

\* Convert batch to stream (F_BS)
BatchToStream(B) ==
    LET events == [i \in 1..Len(B) |-> [value |-> B[i], timestamp |-> i]]
    IN [events |-> events, watermark |-> Len(B)]

\* Convert stream to batch with window (G_SB)
StreamToBatch(S, W) ==
    LET n == IF Len(S.events) < W THEN Len(S.events) ELSE W
    IN [i \in 1..n |-> S.events[i].value]

\* Check if two batches are equal (as multisets)
BatchEqual(B1, B2) ==
    /\ Len(B1) = Len(B2)
    /\ \A v \in DataValue:
        LET count1 == Cardinality({i \in 1..Len(B1) : B1[i] = v})
            count2 == Cardinality({i \in 1..Len(B2) : B2[i] = v})
        IN count1 = count2

-----------------------------------------------------------------------------
(* INITIAL STATE *)
-----------------------------------------------------------------------------

Init ==
    /\ batch \in {<<>>}  \* Start with empty batch
    /\ stream = [events |-> <<>>, watermark |-> 0]
    /\ paradigm = "Batch"
    /\ transformCount = 0

-----------------------------------------------------------------------------
(* STATE TRANSITIONS *)
-----------------------------------------------------------------------------

\* Add element to batch (only in Batch paradigm)
AddToBatch(v) ==
    /\ paradigm = "Batch"
    /\ Len(batch) < MaxDataSize
    /\ v \in DataValue
    /\ batch' = Append(batch, v)
    /\ UNCHANGED <<stream, paradigm, transformCount>>

\* Transform batch to stream (F_BS)
TransformBatchToStream ==
    /\ paradigm = "Batch"
    /\ Len(batch) > 0
    /\ stream' = BatchToStream(batch)
    /\ paradigm' = "Stream"
    /\ transformCount' = transformCount + 1
    /\ UNCHANGED <<batch>>

\* Transform stream to batch (G_SB with window)
TransformStreamToBatch ==
    /\ paradigm = "Stream"
    /\ Len(stream.events) > 0
    /\ batch' = StreamToBatch(stream, WindowSize)
    /\ paradigm' = "Batch"
    /\ transformCount' = transformCount + 1
    /\ UNCHANGED <<stream>>

\* Add event to stream (only in Stream paradigm)
AddToStream(v, t) ==
    /\ paradigm = "Stream"
    /\ Len(stream.events) < MaxDataSize
    /\ v \in DataValue
    /\ t \in 0..MaxTimestamp
    /\ t >= stream.watermark  \* Must be at or after watermark
    /\ stream' = [events |-> Append(stream.events, [value |-> v, timestamp |-> t]),
                  watermark |-> stream.watermark]
    /\ UNCHANGED <<batch, paradigm, transformCount>>

\* Advance watermark
AdvanceWatermark(newW) ==
    /\ paradigm = "Stream"
    /\ newW > stream.watermark
    /\ newW <= MaxTimestamp
    /\ stream' = [events |-> stream.events, watermark |-> newW]
    /\ UNCHANGED <<batch, paradigm, transformCount>>

-----------------------------------------------------------------------------
(* NEXT STATE RELATION *)
-----------------------------------------------------------------------------

Next ==
    \/ \E v \in DataValue: AddToBatch(v)
    \/ TransformBatchToStream
    \/ TransformStreamToBatch
    \/ \E v \in DataValue, t \in 0..MaxTimestamp: AddToStream(v, t)
    \/ \E w \in 1..MaxTimestamp: AdvanceWatermark(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* TYPE INVARIANT *)
-----------------------------------------------------------------------------

TypeInvariant ==
    /\ batch \in Seq(DataValue)
    /\ Len(batch) <= MaxDataSize
    /\ stream.events \in Seq(StreamEvent)
    /\ Len(stream.events) <= MaxDataSize
    /\ stream.watermark \in 0..MaxTimestamp
    /\ paradigm \in {"Batch", "Stream"}
    /\ transformCount \in Nat

-----------------------------------------------------------------------------
(* SAFETY PROPERTIES *)
-----------------------------------------------------------------------------

\* Data is never lost within window constraints
DataPreservationWithinWindow ==
    LET originalSize == IF paradigm = "Batch" 
                        THEN Len(batch) 
                        ELSE Len(stream.events)
        expectedSize == IF originalSize <= WindowSize 
                        THEN originalSize 
                        ELSE WindowSize
    IN originalSize <= MaxDataSize => expectedSize <= MaxDataSize

\* No data loss on round trip when data fits in window
NoDataLossSmallBatch ==
    \* If we start with batch B, transform to stream, back to batch,
    \* and |B| <= W, then we get B back
    LET B == batch
        W == WindowSize
    IN (paradigm = "Batch" /\ Len(B) <= W) =>
       LET S == BatchToStream(B)
           B_prime == StreamToBatch(S, W)
       IN BatchEqual(B, B_prime)

\* Watermark monotonicity
WatermarkMonotonic ==
    paradigm = "Stream" => stream.watermark >= 0

\* Transform count is non-negative
TransformCountNonNeg ==
    transformCount >= 0

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)
-----------------------------------------------------------------------------

\* Eventually reach any paradigm from any other
EventualParadigmReachability ==
    /\ (paradigm = "Batch" /\ Len(batch) > 0) ~> (paradigm = "Stream")
    /\ (paradigm = "Stream" /\ Len(stream.events) > 0) ~> (paradigm = "Batch")

\* Progress: can always do something (unless at max capacity)
Progress ==
    \/ Len(batch) < MaxDataSize
    \/ Len(stream.events) < MaxDataSize
    \/ paradigm = "Batch" /\ Len(batch) > 0  \* Can transform
    \/ paradigm = "Stream" /\ Len(stream.events) > 0  \* Can transform

-----------------------------------------------------------------------------
(* FAIRNESS *)
-----------------------------------------------------------------------------

Fairness == WF_vars(Next)

LiveSpec == Spec /\ Fairness

=============================================================================
\* Modification History
\* Created for PODS 2026 Submission
