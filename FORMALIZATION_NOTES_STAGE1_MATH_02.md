# Stage 1 Math Formalization Notes, Part 2

This file continues the root formalization notes after
`FORMALIZATION_NOTES.md` became large.  The rule remains the same: every Lean
move is recorded with the mathematical reason for making it.

## 1. Local Tensor Packets Carry Typed Capsule Log-Volumes

### Goal

We started tightening the `(Ind2)` local tensor-factor coordinate from
Theorem 3.11 by connecting it to the typed capsule/log-volume data developed
from Proposition 3.9.

The previous Lean state

```text
IUTStage1LocalTensorState
```

only recorded a symmetry label, a direct summand count, and a representative.
That was useful for modeling the existence of a local tensor symmetry, but it
did not yet know about packet/procession-normalized log-volumes.

### Lean/API Check

The new source-facing record is:

```text
IUTStage1LocalTensorPacketLogVolumeState
```

It carries:

```text
tensorState
localObject
capsuleFamily
direct_summand_count_eq_capsuleCount
capsule_family_localObject_eq
```

The key mathematical interface is:

```text
tensorState.directSummandCount = capsuleFamily.capsuleCount
```

This is deliberately a proof field, not a definitional reduction.  At this
stage we have not constructed Mochizuki's local tensor packet internally, so
Lean should require an explicit source obligation whenever a tensor-packet
state is supplied.

We also exposed the typed capsule family's positivity field as:

```text
IUTStage1TypedCapsuleFamilyLogVolume.capsuleCount_pos
```

The packet state uses this theorem to prove positivity of the local tensor
direct summand count after rewriting by the direct-summand/capsule-count
equality.

### Theorem 3.11 Link

We added:

```text
IUTStage1TensorPacketTheorem311Choice
```

This is the existing Theorem 3.11 choice record with the local tensor coordinate
specialized to `IUTStage1LocalTensorPacketLogVolumeState`.

We also added a forgetful map:

```text
forgetPacket :
  IUTStage1TensorPacketTheorem311Choice coric kind ->
  IUTStage1StructuredTheorem311Choice coric
```

The map forgets the typed capsule/log-volume refinement and keeps the older
local tensor state.  This is one-way for now: a later refined `(Ind2)` step must
prove how the packet data transforms before we can quotient by it safely.

### Why This Matches the Source Direction

IUT III Proposition 3.9 discusses packet-normalized and
procession-normalized log-volumes, with averaging over finite capsule data.
IUT III Theorem 3.11 then separates `(Ind2)` local tensor-factor symmetries
from `(Ind3)` upper semi-compatibility.  The debated route to Corollary 3.12
depends on not silently collapsing these layers into one undifferentiated
object.

This milestone keeps the layers separate while making their first explicit
interface:

```text
local tensor direct summands <-> typed capsule count
```

That interface is intentionally minimal and auditable.

### Toy Check

The source examples now check:

```text
upperSemi_typedCapsuleFamily_capsuleCount_pos_example
localTensorPacket_to_localTensorState_example
localTensorPacket_directSummandCount_eq_capsuleCount_example
localTensorPacket_directSummandCount_pos_example
localTensorPacket_localObject_eq_example
localTensorPacket_totalLogVolume_eq_sum_example
tensorPacketTheorem311_forgetPacket_example
tensorPacketTheorem311_directSummandCount_eq_capsuleCount_example
```

### Remaining Gap

The local tensor packet itself is not yet built from Hodge-theater or Frobenioid
objects.  The next useful refinement is a packet-aware `(Ind2)` step relation:
it should allow representative changes while preserving the capsule/log-volume
obligations needed for later upper-semi comparison.
