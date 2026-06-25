/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1HodgeSHE

/-!
Theorem 3.11 source-choice and multiradial image data for Stage 1.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps Theorem 3.11 choice/indeterminacy records, refined direct-summand and
place-audited multiradial possible-image records, algorithm-output records, and
SHE-alignment source records.  The Step (xi) hull/determinant, IPL, and endpoint
route declarations remain in `Iut.Stage1.IUTStage1Source` for now.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

/--
Source-shaped choice data for Theorem 3.11.

The integer coordinates model the log-theta-lattice column `n` and row `m`.
The remaining coordinates separate the coric data from the representative data
affected by `(Ind1)`, `(Ind2)`, `(Ind3)`.
-/
structure IUTStage1Theorem311Choice
    (coric : Type u) (processionState : Type v)
    (localTensorState : Type w) (upperSemiState : Type x) where
  column : Int
  row : Int
  coric : coric
  procession_state : processionState
  local_tensor_state : localTensorState
  upper_semi_state : upperSemiState

namespace IUTStage1Theorem311Choice

variable {coric : Type u} {processionState : Type v}
variable {localTensorState : Type w} {upperSemiState : Type x}

abbrev Choice :=
  IUTStage1Theorem311Choice
    coric processionState localTensorState upperSemiState

/-- `(Ind1)` changes procession representatives and preserves the other coordinates. -/
structure ProcessionAutomorphismStep
    (choice₁ choice₂ : Choice
      (coric := coric) (processionState := processionState)
      (localTensorState := localTensorState)
      (upperSemiState := upperSemiState)) : Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state

/-- `(Ind2)` changes local tensor representatives and preserves the other coordinates. -/
structure LocalTensorSymmetryStep
    (choice₁ choice₂ : Choice
      (coric := coric) (processionState := processionState)
      (localTensorState := localTensorState)
      (upperSemiState := upperSemiState)) : Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state

/--
`(Ind3)` records upper semi-compatibility as the row `m` varies. It preserves
the column and coric data but may change the row and upper-semi representative.
-/
structure UpperSemiCompatibilityStep
    (choice₁ choice₂ : Choice
      (coric := coric) (processionState := processionState)
      (localTensorState := localTensorState)
      (upperSemiState := upperSemiState)) : Prop where
  column_eq : choice₁.column = choice₂.column
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state

def indeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (Choice
        (coric := coric) (processionState := processionState)
        (localTensorState := localTensorState)
        (upperSemiState := upperSemiState)) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := LocalTensorSymmetryStep,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

theorem generated_coric_eq
    {choice₁ choice₂ :
      Choice
        (coric := coric) (processionState := processionState)
        (localTensorState := localTensorState)
        (upperSemiState := upperSemiState)}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        indeterminacySourceData.generators choice₁ choice₂) :
    choice₁.coric = choice₂.coric := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.coric_eq
  | ind2 hstep =>
      exact hstep.coric_eq
  | ind3 hstep =>
      exact hstep.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_column_eq
    {choice₁ choice₂ :
      Choice
        (coric := coric) (processionState := processionState)
        (localTensorState := localTensorState)
        (upperSemiState := upperSemiState)}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        indeterminacySourceData.generators choice₁ choice₂) :
    choice₁.column = choice₂.column := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.column_eq
  | ind2 hstep =>
      exact hstep.column_eq
  | ind3 hstep =>
      exact hstep.column_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (Choice
          (coric := coric) (processionState := processionState)
          (localTensorState := localTensorState)
          (upperSemiState := upperSemiState)))
    (hcoric :
      ∀ choice₁ choice₂,
        choice₁.coric = choice₂.coric ->
          images.region choice₁ = images.region choice₂) :
    ∀ {choice₁ choice₂ :
      Choice
        (coric := coric) (processionState := processionState)
        (localTensorState := localTensorState)
        (upperSemiState := upperSemiState)},
      IUTStage1GeneratedIndeterminacyRelation
        indeterminacySourceData.generators choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  intro choice₁ choice₂ hrel
  exact hcoric choice₁ choice₂ (generated_coric_eq hrel)

end IUTStage1Theorem311Choice

/--
Theorem 3.11 choice specialized to the state records currently modeled in this
file.
-/
abbrev IUTStage1StructuredTheorem311Choice (coric : Type u) :=
  IUTStage1Theorem311Choice
    coric
    IUTStage1ProcessionState
    IUTStage1LocalTensorState
    IUTStage1UpperSemiCompatibilityState

namespace IUTStage1StructuredTheorem311Choice

variable {coric : Type u}

/-- Structured `(Ind1)` step: procession representative may change. -/
structure ProcessionAutomorphismStep
    (choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric) : Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq :
    choice₁.procession_state.procession =
      choice₂.procession_state.procession
  procession_column_eq :
    choice₁.procession_state.column = choice₂.procession_state.column
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state

/-- Structured `(Ind2)` step: local tensor representative may change. -/
structure LocalTensorSymmetryStep
    (choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric) : Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  direct_summand_count_eq :
    choice₁.local_tensor_state.directSummandCount =
      choice₂.local_tensor_state.directSummandCount
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state

/--
Structured `(Ind3)` step: row and upper-semi representative may vary, but the
log-theta column and the local comparison shape are preserved.
-/
structure UpperSemiCompatibilityStep
    (choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric) : Prop where
  column_eq : choice₁.column = choice₂.column
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  logThetaColumn_eq :
    choice₁.upper_semi_state.logThetaColumn =
      choice₂.upper_semi_state.logThetaColumn
  nonarchimedean_inclusions_eq :
    choice₁.upper_semi_state.nonarchimedeanInclusions =
      choice₂.upper_semi_state.nonarchimedeanInclusions
  archimedean_surjections_eq :
    choice₁.upper_semi_state.archimedeanSurjections =
      choice₂.upper_semi_state.archimedeanSurjections
  log_volume_compatibility_eq :
    choice₁.upper_semi_state.logVolumeCompatibility =
      choice₂.upper_semi_state.logVolumeCompatibility
  has_nonarchimedean_inclusions_eq :
    choice₁.upper_semi_state.hasNonarchimedeanInclusions =
      choice₂.upper_semi_state.hasNonarchimedeanInclusions
  has_archimedean_surjections_eq :
    choice₁.upper_semi_state.hasArchimedeanSurjections =
      choice₂.upper_semi_state.hasArchimedeanSurjections

def indeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (IUTStage1StructuredTheorem311Choice coric) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := LocalTensorSymmetryStep,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

theorem ind1_preserves_procession_column
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      ProcessionAutomorphismStep choice₁ choice₂) :
    choice₁.procession_state.column = choice₂.procession_state.column := by
  exact hstep.procession_column_eq

theorem ind2_preserves_directSummandCount
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      LocalTensorSymmetryStep choice₁ choice₂) :
    choice₁.local_tensor_state.directSummandCount =
      choice₂.local_tensor_state.directSummandCount := by
  exact hstep.direct_summand_count_eq

theorem ind3_preserves_logThetaColumn
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₁.upper_semi_state.logThetaColumn =
      choice₂.upper_semi_state.logThetaColumn := by
  exact hstep.logThetaColumn_eq

theorem ind3_preserves_nonarchimedeanInclusions
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₁.upper_semi_state.nonarchimedeanInclusions =
      choice₂.upper_semi_state.nonarchimedeanInclusions := by
  exact hstep.nonarchimedean_inclusions_eq

theorem ind3_preserves_archimedeanSurjections
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₁.upper_semi_state.archimedeanSurjections =
      choice₂.upper_semi_state.archimedeanSurjections := by
  exact hstep.archimedean_surjections_eq

theorem ind3_preserves_logVolumeCompatibility
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₁.upper_semi_state.logVolumeCompatibility =
      choice₂.upper_semi_state.logVolumeCompatibility := by
  exact hstep.log_volume_compatibility_eq

theorem ind3_target_logVolumeCompatible
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (_hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₂.upper_semi_state.logVolumeCompatible := by
  exact choice₂.upper_semi_state.logVolumeCompatibleProof

theorem ind3_target_logVolumeUpperBound
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (_hstep :
      UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₂.upper_semi_state.logVolumeCompatibility.sourceLogVolume <=
      choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume :=
  choice₂.upper_semi_state.logVolumeUpperBound

theorem generated_preserves_coric
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.coric = choice₂.coric := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.coric_eq
  | ind2 hstep =>
      exact hstep.coric_eq
  | ind3 hstep =>
      exact hstep.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_column
    {choice₁ choice₂ : IUTStage1StructuredTheorem311Choice coric}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.column = choice₂.column := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.column_eq
  | ind2 hstep =>
      exact hstep.column_eq
  | ind3 hstep =>
      exact hstep.column_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

end IUTStage1StructuredTheorem311Choice

/--
Theorem 3.11 choice whose local tensor coordinate already carries typed
capsule/log-volume data.
-/
abbrev IUTStage1TensorPacketTheorem311Choice
    (coric : Type u) (kind : IUTStage1PlaceKind) :=
  IUTStage1Theorem311Choice
    coric
    IUTStage1ProcessionState
    (IUTStage1LocalTensorPacketLogVolumeState kind)
    IUTStage1UpperSemiCompatibilityState

namespace IUTStage1TensorPacketTheorem311Choice

variable {coric : Type u} {kind : IUTStage1PlaceKind}

/--
Forget the typed capsule/log-volume refinement of the local tensor coordinate.

This is deliberately one-way: refined steps must prove that the extra
packet/log-volume fields are preserved or transformed correctly before they can
descend to the structured interface.
-/
def forgetPacket
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    IUTStage1StructuredTheorem311Choice coric :=
  { column := choice.column,
    row := choice.row,
    coric := choice.coric,
    procession_state := choice.procession_state,
    local_tensor_state := choice.local_tensor_state.toLocalTensorState,
    upper_semi_state := choice.upper_semi_state }

theorem forgetPacket_column
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    choice.forgetPacket.column = choice.column :=
  rfl

theorem forgetPacket_row
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    choice.forgetPacket.row = choice.row :=
  rfl

theorem localTensor_directSummandCount_eq_capsuleCount
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    choice.local_tensor_state.tensorState.directSummandCount =
      choice.local_tensor_state.capsuleFamily.capsuleCount :=
  choice.local_tensor_state.directSummandCount_eq_capsuleCount

theorem localTensor_directSummandCount_pos
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    0 < choice.local_tensor_state.tensorState.directSummandCount :=
  choice.local_tensor_state.directSummandCount_pos

theorem localTensor_capsule_totalLogVolume_eq_sum
    (choice : IUTStage1TensorPacketTheorem311Choice coric kind) :
    choice.local_tensor_state.capsuleFamily.totalLogVolume =
      Finset.univ.sum fun i =>
        (choice.local_tensor_state.capsuleFamily.capsule i).logVolume :=
  choice.local_tensor_state.capsule_totalLogVolume_eq_sum

/--
Packet-aware `(Ind2)` step.

The local tensor representative may change, but the procession, coric data,
upper-semi data, and packet-level log-volume quantities are preserved.
-/
structure LocalTensorPacketSymmetryStep
    (choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  local_object_eq :
    choice₁.local_tensor_state.localObject =
      choice₂.local_tensor_state.localObject
  capsule_count_eq :
    choice₁.local_tensor_state.capsuleFamily.capsuleCount =
      choice₂.local_tensor_state.capsuleFamily.capsuleCount
  capsule_totalLogVolume_eq :
    choice₁.local_tensor_state.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.capsuleFamily.totalLogVolume
  capsule_normalizedLogVolume_eq :
    choice₁.local_tensor_state.capsuleFamily.normalizedLogVolume =
      choice₂.local_tensor_state.capsuleFamily.normalizedLogVolume

theorem ind2_preserves_directSummandCount
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂) :
    choice₁.local_tensor_state.tensorState.directSummandCount =
      choice₂.local_tensor_state.tensorState.directSummandCount := by
  calc
    choice₁.local_tensor_state.tensorState.directSummandCount =
        choice₁.local_tensor_state.capsuleFamily.capsuleCount :=
      choice₁.local_tensor_state.directSummandCount_eq_capsuleCount
    _ = choice₂.local_tensor_state.capsuleFamily.capsuleCount :=
      hstep.capsule_count_eq
    _ = choice₂.local_tensor_state.tensorState.directSummandCount :=
      (choice₂.local_tensor_state.directSummandCount_eq_capsuleCount).symm

theorem ind2_preserves_localObject
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂) :
    choice₁.local_tensor_state.localObject =
      choice₂.local_tensor_state.localObject :=
  hstep.local_object_eq

theorem ind2_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂) :
    choice₁.local_tensor_state.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.capsuleFamily.totalLogVolume :=
  hstep.capsule_totalLogVolume_eq

theorem ind2_preserves_capsuleNormalizedLogVolume
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂) :
    choice₁.local_tensor_state.capsuleFamily.normalizedLogVolume =
      choice₂.local_tensor_state.capsuleFamily.normalizedLogVolume :=
  hstep.capsule_normalizedLogVolume_eq

def ind2_transports_packetNormalizedCompatibility
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂)
    (compat :
      IUTStage1LocalTensorPacketNormalizedCompatibility
        choice₁.local_tensor_state) :
    IUTStage1LocalTensorPacketNormalizedCompatibility
      choice₂.local_tensor_state :=
  { normalizedLogVolume_eq_localObject := by
      calc
        choice₂.local_tensor_state.capsuleFamily.normalizedLogVolume =
            choice₁.local_tensor_state.capsuleFamily.normalizedLogVolume :=
          hstep.capsule_normalizedLogVolume_eq.symm
        _ = choice₁.local_tensor_state.localObject.finiteLogVolume :=
          compat.normalizedLogVolume_eq_localObject
        _ = choice₂.local_tensor_state.localObject.finiteLogVolume := by
          rw [hstep.local_object_eq] }

def ind2_transports_classifiedPacketNormalizedCompatibility
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂)
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        choice₁.local_tensor_state) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
      choice₂.local_tensor_state :=
  IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.ofInd2TransportedPacketNormalization
    (ind2_transports_packetNormalizedCompatibility hstep
      classified.compatibility)

def toStructuredLocalTensorSymmetryStep
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketSymmetryStep choice₁ choice₂) :
    IUTStage1StructuredTheorem311Choice.LocalTensorSymmetryStep
      choice₁.forgetPacket choice₂.forgetPacket :=
  { column_eq := hstep.column_eq,
    row_eq := hstep.row_eq,
    coric_eq := hstep.coric_eq,
    procession_eq := hstep.procession_eq,
    direct_summand_count_eq :=
      ind2_preserves_directSummandCount hstep,
    upper_semi_eq := hstep.upper_semi_eq }

/--
Packet-aware `(Ind2)` step generated by an action on the indexed capsule
family.

This is stronger than `LocalTensorPacketSymmetryStep`: total and normalized
log-volume preservation are consequences of pointwise capsule log-volume
preservation.
-/
structure LocalTensorPacketActionStep
    (choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  local_object_eq :
    choice₁.local_tensor_state.localObject =
      choice₂.local_tensor_state.localObject
  capsule_action_exists :
    ∃ action :
      IUTStage1TypedCapsuleFamilyLogVolumeAction
        choice₁.local_tensor_state.capsuleFamily,
      choice₂.local_tensor_state.capsuleFamily =
        action.transformedFamily

theorem actionStep_preserves_capsuleCount
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.capsuleFamily.capsuleCount =
      choice₂.local_tensor_state.capsuleFamily.capsuleCount := by
  rcases hstep.capsule_action_exists with ⟨action, htarget⟩
  rw [htarget]
  exact action.transformedFamily_capsuleCount.symm

theorem actionStep_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.capsuleFamily.totalLogVolume := by
  rcases hstep.capsule_action_exists with ⟨action, htarget⟩
  rw [htarget]
  exact action.transformedFamily_totalLogVolume.symm

theorem actionStep_preserves_capsuleNormalizedLogVolume
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.capsuleFamily.normalizedLogVolume =
      choice₂.local_tensor_state.capsuleFamily.normalizedLogVolume := by
  rcases hstep.capsule_action_exists with ⟨action, htarget⟩
  rw [htarget]
  exact action.transformedFamily_normalizedLogVolume.symm

def actionStep_toPacketSymmetryStep
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketActionStep choice₁ choice₂) :
    LocalTensorPacketSymmetryStep choice₁ choice₂ :=
  { column_eq := hstep.column_eq,
    row_eq := hstep.row_eq,
    coric_eq := hstep.coric_eq,
    procession_eq := hstep.procession_eq,
    upper_semi_eq := hstep.upper_semi_eq,
    local_object_eq := hstep.local_object_eq,
    capsule_count_eq := actionStep_preserves_capsuleCount hstep,
    capsule_totalLogVolume_eq :=
      actionStep_preserves_capsuleTotalLogVolume hstep,
    capsule_normalizedLogVolume_eq :=
      actionStep_preserves_capsuleNormalizedLogVolume hstep }

theorem actionStep_preserves_directSummandCount
    {choice₁ choice₂ : IUTStage1TensorPacketTheorem311Choice coric kind}
    (hstep : LocalTensorPacketActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.tensorState.directSummandCount =
      choice₂.local_tensor_state.tensorState.directSummandCount :=
  ind2_preserves_directSummandCount
    (actionStep_toPacketSymmetryStep hstep)

end IUTStage1TensorPacketTheorem311Choice

/--
Theorem 3.11 choice whose local tensor coordinate carries both typed capsule
log-volume data and the direct summand family that induces capsule actions.
-/
abbrev IUTStage1DirectSummandPacketTheorem311Choice
    (coric : Type u) (kind : IUTStage1PlaceKind) :=
  IUTStage1Theorem311Choice
    coric
    IUTStage1ProcessionState
    (IUTStage1LocalTensorDirectSummandPacketState kind)
    IUTStage1UpperSemiCompatibilityState

namespace IUTStage1DirectSummandPacketTheorem311Choice

variable {coric : Type u} {kind : IUTStage1PlaceKind}

def forgetDirectSummands
    (choice : IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    IUTStage1TensorPacketTheorem311Choice coric kind :=
  { column := choice.column,
    row := choice.row,
    coric := choice.coric,
    procession_state := choice.procession_state,
    local_tensor_state :=
      choice.local_tensor_state.toLocalTensorPacketLogVolumeState,
    upper_semi_state := choice.upper_semi_state }

def forgetPacket
    (choice : IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    IUTStage1StructuredTheorem311Choice coric :=
  choice.forgetDirectSummands.forgetPacket

theorem localTensor_directSummandCount_eq_capsuleCount
    (choice : IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    choice.local_tensor_state.packetState.tensorState.directSummandCount =
      choice.local_tensor_state.packetState.capsuleFamily.capsuleCount :=
  choice.local_tensor_state.directSummandCount_eq_capsuleCount

theorem localTensor_summandCapsuleLogVolume_eq
    (choice : IUTStage1DirectSummandPacketTheorem311Choice coric kind)
    (i : Fin choice.local_tensor_state.packetState.capsuleFamily.capsuleCount) :
    (choice.local_tensor_state.summandFamily.summand i).capsule.logVolume =
      (choice.local_tensor_state.packetState.capsuleFamily.capsule i).logVolume :=
  choice.local_tensor_state.summandCapsuleLogVolume_eq i

/--
Direct-summand-level `(Ind2)` step for the refined packet choice.

The step records an action on the source direct summand family whose induced
capsule action gives the target capsule family.
-/
structure LocalTensorDirectSummandActionStep
    (choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  local_object_eq :
    choice₁.local_tensor_state.packetState.localObject =
      choice₂.local_tensor_state.packetState.localObject
  summand_action_exists :
    ∃ action :
      IUTStage1TensorDirectSummandFamilyAction
        choice₁.local_tensor_state.summandFamily,
      choice₂.local_tensor_state.packetState.capsuleFamily =
        action.toCapsuleAction.transformedFamily

def toTensorPacketActionStep
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂) :
    IUTStage1TensorPacketTheorem311Choice.LocalTensorPacketActionStep
      choice₁.forgetDirectSummands choice₂.forgetDirectSummands :=
  { column_eq := hstep.column_eq,
    row_eq := hstep.row_eq,
    coric_eq := hstep.coric_eq,
    procession_eq := hstep.procession_eq,
    upper_semi_eq := hstep.upper_semi_eq,
    local_object_eq := hstep.local_object_eq,
    capsule_action_exists := by
      rcases hstep.summand_action_exists with ⟨action, htarget⟩
      exact ⟨action.toCapsuleAction, htarget⟩ }

theorem ind2_preserves_directSummandCount
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.tensorState.directSummandCount =
      choice₂.local_tensor_state.packetState.tensorState.directSummandCount :=
  IUTStage1TensorPacketTheorem311Choice.actionStep_preserves_directSummandCount
    (toTensorPacketActionStep hstep)

theorem ind2_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  IUTStage1TensorPacketTheorem311Choice.actionStep_preserves_capsuleTotalLogVolume
    (toTensorPacketActionStep hstep)

theorem ind2_preserves_capsuleNormalizedLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  IUTStage1TensorPacketTheorem311Choice.actionStep_preserves_capsuleNormalizedLogVolume
    (toTensorPacketActionStep hstep)

def ind2_transports_packetNormalizedCompatibility
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂)
    (compat :
      IUTStage1LocalTensorPacketNormalizedCompatibility
        choice₁.local_tensor_state.packetState) :
    IUTStage1LocalTensorPacketNormalizedCompatibility
      choice₂.local_tensor_state.packetState :=
  IUTStage1TensorPacketTheorem311Choice.ind2_transports_packetNormalizedCompatibility
    (IUTStage1TensorPacketTheorem311Choice.actionStep_toPacketSymmetryStep
      (toTensorPacketActionStep hstep))
    compat

def ind2_transports_classifiedPacketNormalizedCompatibility
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂)
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        choice₁.local_tensor_state.packetState) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
      choice₂.local_tensor_state.packetState :=
  IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.ofInd2TransportedPacketNormalization
    (ind2_transports_packetNormalizedCompatibility hstep
      classified.compatibility)

theorem ind2_transports_capsuleContainerBound
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : LocalTensorDirectSummandActionStep choice₁ choice₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned choice₁.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      choice₂.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume := by
  rcases hstep.summand_action_exists with ⟨action, htarget⟩
  rw [htarget]
  exact
    action.transformedContainerEstimate_targetSigned_le_normalizedLogVolume
      estimate

/-- Nonarchimedean `Ism` instance of the direct-summand `(Ind2)` step. -/
structure NonarchimedeanIsmInd2Step
    (choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  local_object_eq :
    choice₁.local_tensor_state.packetState.localObject =
      choice₂.local_tensor_state.packetState.localObject
  ism_action_exists :
    ∃ action :
      IUTStage1NonarchimedeanIsmDirectSummandAction
        choice₁.local_tensor_state.summandFamily,
      choice₂.local_tensor_state.packetState.capsuleFamily =
        action.toDirectSummandAction.toCapsuleAction.transformedFamily

/-- Archimedean order-two instance of the direct-summand `(Ind2)` step. -/
structure ArchimedeanOrderTwoInd2Step
    (choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  local_object_eq :
    choice₁.local_tensor_state.packetState.localObject =
      choice₂.local_tensor_state.packetState.localObject
  order_two_action_exists :
    ∃ action :
      IUTStage1ArchimedeanOrderTwoDirectSummandAction
        choice₁.local_tensor_state.summandFamily,
      choice₂.local_tensor_state.packetState.capsuleFamily =
        action.toDirectSummandAction.toCapsuleAction.transformedFamily

def nonarchimedeanIsm_toDirectSummandActionStep
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step choice₁ choice₂) :
    LocalTensorDirectSummandActionStep choice₁ choice₂ :=
  { column_eq := hstep.column_eq,
    row_eq := hstep.row_eq,
    coric_eq := hstep.coric_eq,
    procession_eq := hstep.procession_eq,
    upper_semi_eq := hstep.upper_semi_eq,
    local_object_eq := hstep.local_object_eq,
    summand_action_exists := by
      rcases hstep.ism_action_exists with ⟨action, htarget⟩
      exact ⟨action.toDirectSummandAction, htarget⟩ }

def archimedeanOrderTwo_toDirectSummandActionStep
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step choice₁ choice₂) :
    LocalTensorDirectSummandActionStep choice₁ choice₂ :=
  { column_eq := hstep.column_eq,
    row_eq := hstep.row_eq,
    coric_eq := hstep.coric_eq,
    procession_eq := hstep.procession_eq,
    upper_semi_eq := hstep.upper_semi_eq,
    local_object_eq := hstep.local_object_eq,
    summand_action_exists := by
      rcases hstep.order_two_action_exists with ⟨action, htarget⟩
      exact ⟨action.toDirectSummandAction, htarget⟩ }

theorem nonarchimedeanIsm_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (nonarchimedeanIsm_toDirectSummandActionStep hstep)

theorem archimedeanOrderTwo_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (archimedeanOrderTwo_toDirectSummandActionStep hstep)

theorem nonarchimedeanIsm_transports_capsuleContainerBound
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step choice₁ choice₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned choice₁.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      choice₂.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  ind2_transports_capsuleContainerBound
    (nonarchimedeanIsm_toDirectSummandActionStep hstep) estimate

theorem archimedeanOrderTwo_transports_capsuleContainerBound
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step choice₁ choice₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned choice₁.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      choice₂.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  ind2_transports_capsuleContainerBound
    (archimedeanOrderTwo_toDirectSummandActionStep hstep) estimate

/-- Refined `(Ind1)` step for direct-summand packet choices. -/
structure ProcessionAutomorphismStep
    (choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  row_eq : choice₁.row = choice₂.row
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq :
    choice₁.procession_state.procession =
      choice₂.procession_state.procession
  procession_column_eq :
    choice₁.procession_state.column = choice₂.procession_state.column
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state

/-- Refined `(Ind3)` step for direct-summand packet choices. -/
structure UpperSemiCompatibilityStep
    (choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind) :
    Prop where
  column_eq : choice₁.column = choice₂.column
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  logThetaColumn_eq :
    choice₁.upper_semi_state.logThetaColumn =
      choice₂.upper_semi_state.logThetaColumn
  nonarchimedean_inclusions_eq :
    choice₁.upper_semi_state.nonarchimedeanInclusions =
      choice₂.upper_semi_state.nonarchimedeanInclusions
  archimedean_surjections_eq :
    choice₁.upper_semi_state.archimedeanSurjections =
      choice₂.upper_semi_state.archimedeanSurjections
  log_volume_compatibility_eq :
    choice₁.upper_semi_state.logVolumeCompatibility =
      choice₂.upper_semi_state.logVolumeCompatibility
  has_nonarchimedean_inclusions_eq :
    choice₁.upper_semi_state.hasNonarchimedeanInclusions =
      choice₂.upper_semi_state.hasNonarchimedeanInclusions
  has_archimedean_surjections_eq :
    choice₁.upper_semi_state.hasArchimedeanSurjections =
      choice₂.upper_semi_state.hasArchimedeanSurjections

def indeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := LocalTensorDirectSummandActionStep,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

theorem ind1_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : ProcessionAutomorphismStep choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  congrArg
    (fun state =>
      state.packetState.capsuleFamily.totalLogVolume)
    hstep.local_tensor_eq

theorem ind3_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hstep : UpperSemiCompatibilityStep choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  congrArg
    (fun state =>
      state.packetState.capsuleFamily.totalLogVolume)
    hstep.local_tensor_eq

def nonarchimedeanIsmIndeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := NonarchimedeanIsmInd2Step,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

def archimedeanOrderTwoIndeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := ArchimedeanOrderTwoInd2Step,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

theorem nonarchimedeanIsm_generated_preserves_coric
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (nonarchimedeanIsmIndeterminacySourceData
          (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.coric = choice₂.coric := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.coric_eq
  | ind2 hstep =>
      exact hstep.coric_eq
  | ind3 hstep =>
      exact hstep.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem archimedeanOrderTwo_generated_preserves_coric
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (archimedeanOrderTwoIndeterminacySourceData
          (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.coric = choice₂.coric := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.coric_eq
  | ind2 hstep =>
      exact hstep.coric_eq
  | ind3 hstep =>
      exact hstep.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem nonarchimedeanIsm_generated_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (nonarchimedeanIsmIndeterminacySourceData
          (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact ind1_preserves_capsuleTotalLogVolume hstep
  | ind2 hstep =>
      exact nonarchimedeanIsm_preserves_capsuleTotalLogVolume hstep
  | ind3 hstep =>
      exact ind3_preserves_capsuleTotalLogVolume hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem archimedeanOrderTwo_generated_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (archimedeanOrderTwoIndeterminacySourceData
          (coric := coric)).generators
        choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact ind1_preserves_capsuleTotalLogVolume hstep
  | ind2 hstep =>
      exact archimedeanOrderTwo_preserves_capsuleTotalLogVolume hstep
  | ind3 hstep =>
      exact ind3_preserves_capsuleTotalLogVolume hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_coric
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        choice₁ choice₂) :
    choice₁.coric = choice₂.coric := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.coric_eq
  | ind2 hstep =>
      exact hstep.coric_eq
  | ind3 hstep =>
      exact hstep.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_column
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        choice₁ choice₂) :
    choice₁.column = choice₂.column := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep.column_eq
  | ind2 hstep =>
      exact hstep.column_eq
  | ind3 hstep =>
      exact hstep.column_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_capsuleTotalLogVolume
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        choice₁ choice₂) :
    choice₁.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      choice₂.local_tensor_state.packetState.capsuleFamily.totalLogVolume := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact ind1_preserves_capsuleTotalLogVolume hstep
  | ind2 hstep =>
      exact ind2_preserves_capsuleTotalLogVolume hstep
  | ind3 hstep =>
      exact ind3_preserves_capsuleTotalLogVolume hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind))
    (hcoric :
      ∀ choice₁ choice₂,
        choice₁.coric = choice₂.coric ->
          images.region choice₁ = images.region choice₂) :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind},
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  intro choice₁ choice₂ hrel
  exact hcoric choice₁ choice₂ (generated_preserves_coric hrel)

end IUTStage1DirectSummandPacketTheorem311Choice

/--
Multiradial possible images indexed by refined direct-summand packet
Theorem 3.11 choices.
-/
structure IUTStage1DirectSummandPacketMultiradialImages
    {target : Copy}
    (coric : Type u) (kind : IUTStage1PlaceKind) where
  possibleImages :
    RegionFamily target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)
  quotient :
    IUTStage1IndeterminacyQuotient
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)
  quotient_eq_generated :
    quotient =
      (IUTStage1DirectSummandPacketTheorem311Choice.indeterminacySourceData
        (coric := coric) (kind := kind)).quotient
  image_invariant :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind},
      quotient.relation choice₁ choice₂ ->
        possibleImages.region choice₁ = possibleImages.region choice₂

namespace IUTStage1DirectSummandPacketMultiradialImages

variable {target : Copy} {coric : Type u} {kind : IUTStage1PlaceKind}

def ofCoricInvariant
    (images :
      RegionFamily target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind))
    (hcoric :
      ∀ choice₁ choice₂,
        choice₁.coric = choice₂.coric ->
          images.region choice₁ = images.region choice₂) :
    IUTStage1DirectSummandPacketMultiradialImages
      (target := target) coric kind :=
  { possibleImages := images,
    quotient :=
      (IUTStage1DirectSummandPacketTheorem311Choice.indeterminacySourceData
        (coric := coric) (kind := kind)).quotient,
    quotient_eq_generated := rfl,
    image_invariant := by
      intro choice₁ choice₂ hrel
      exact
        IUTStage1DirectSummandPacketTheorem311Choice.image_invariant_of_coric
          images hcoric hrel }

theorem region_eq_of_related
    (data :
      IUTStage1DirectSummandPacketMultiradialImages
        (target := target) coric kind)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel : data.quotient.relation choice₁ choice₂) :
    data.possibleImages.region choice₁ = data.possibleImages.region choice₂ :=
  data.image_invariant hrel

theorem quotient_profile
    (data :
      IUTStage1DirectSummandPacketMultiradialImages
        (target := target) coric kind) :
    data.quotient.profile = theorem311IndeterminacyProfile := by
  rw [data.quotient_eq_generated]
  exact
    IUTStage1Theorem311IndeterminacySourceData.quotient_profile
      (IUTStage1DirectSummandPacketTheorem311Choice.indeterminacySourceData
        (coric := coric) (kind := kind))

end IUTStage1DirectSummandPacketMultiradialImages

/--
Source-package version of refined direct-summand packet multiradial theta
images.
-/
structure IUTStage1RefinedDirectSummandPacketMultiradialThetaImages
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind)) where
  multiradialOutput : MultiradialOutputId
  possibleImages : IUTStage1ThetaPilotPossibleImages package
  refinedImages :
    IUTStage1DirectSummandPacketMultiradialImages
      (target := target) coric kind
  multiradial_output_eq : multiradialOutput = package.multiradialOutput
  refined_possibleImages_eq :
    refinedImages.possibleImages = possibleImages.images

namespace IUTStage1RefinedDirectSummandPacketMultiradialThetaImages

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)}

def ofPackageWithCoricInvariant
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind))
    (hcoric :
      ∀ choice₁ choice₂,
        choice₁.coric = choice₂.coric ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂) :
    IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    refinedImages :=
      IUTStage1DirectSummandPacketMultiradialImages.ofCoricInvariant
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
        hcoric,
    multiradial_output_eq := rfl,
    refined_possibleImages_eq := rfl }

theorem region_eq_of_related
    (data :
      IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel : data.refinedImages.quotient.relation choice₁ choice₂) :
    data.possibleImages.images.region choice₁ =
      data.possibleImages.images.region choice₂ := by
  rw [← data.refined_possibleImages_eq]
  exact data.refinedImages.region_eq_of_related hrel

theorem quotient_profile
    (data :
      IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package) :
    data.refinedImages.quotient.profile = theorem311IndeterminacyProfile :=
  data.refinedImages.quotient_profile

theorem union_eq_targetUnion
    (data :
      IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package) :
    data.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  data.possibleImages.union_eq_targetUnion

end IUTStage1RefinedDirectSummandPacketMultiradialThetaImages

/--
Refined direct-summand packet choice together with a place-family compatibility
audit linking its upper-semi state to `(Ind2)` action-family data.
-/
structure IUTStage1PlaceAuditedDirectSummandPacketChoice
    (coric : Type u) (kind : IUTStage1PlaceKind) where
  choice : IUTStage1DirectSummandPacketTheorem311Choice coric kind
  placeFamilyCompatibility :
    IUTStage1Ind2UpperSemiPlaceFamilyCompatibility
  upper_semi_state_eq :
    placeFamilyCompatibility.upperSemiState = choice.upper_semi_state

namespace IUTStage1PlaceAuditedDirectSummandPacketChoice

variable {coric : Type u} {kind : IUTStage1PlaceKind}

def toDirectSummandPacketTheorem311Choice
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1DirectSummandPacketTheorem311Choice coric kind :=
  audited.choice

theorem upperSemiState_eq
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    audited.placeFamilyCompatibility.upperSemiState =
      audited.choice.upper_semi_state :=
  audited.upper_semi_state_eq

theorem upperSemi_logVolumeCompatible
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    audited.choice.upper_semi_state.logVolumeCompatible := by
  rw [← audited.upperSemiState_eq]
  exact audited.placeFamilyCompatibility.logVolumeCompatible

theorem upperSemi_logVolumeUpperBound
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    audited.choice.upper_semi_state.logVolumeCompatibility.sourceLogVolume <=
      audited.choice.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
  rw [← audited.upperSemiState_eq]
  exact audited.placeFamilyCompatibility.logVolumeUpperBound

theorem nonarchimedeanPlaces_eq
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    audited.placeFamilyCompatibility.ind2Actions.nonarchimedeanPlaces =
      audited.choice.upper_semi_state.nonarchimedeanInclusions.map fun entry =>
        entry.place := by
  rw [← audited.upperSemiState_eq]
  exact audited.placeFamilyCompatibility.nonarchimedeanPlaces_eq

theorem archimedeanPlaces_eq
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    audited.placeFamilyCompatibility.ind2Actions.archimedeanPlaces =
      audited.choice.upper_semi_state.archimedeanSurjections.map fun entry =>
        entry.place := by
  rw [← audited.upperSemiState_eq]
  exact audited.placeFamilyCompatibility.archimedeanPlaces_eq

/--
Audit that the direct-summand count of a place-audited Theorem 3.11 choice
matches the number of `(Ind2)` action entries of the corresponding place kind.
-/
structure DirectSummandPlaceCountAudit
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) where
  direct_summand_count_eq_actionCount :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited.placeFamilyCompatibility.ind2Actions.actionCountForKind kind

namespace DirectSummandPlaceCountAudit

variable
  {audited :
    IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}

theorem capsuleCount_eq_actionCount
    (audit : DirectSummandPlaceCountAudit audited) :
    audited.choice.local_tensor_state.packetState.capsuleFamily.capsuleCount =
      audited.placeFamilyCompatibility.ind2Actions.actionCountForKind kind := by
  rw [← audited.choice.local_tensor_state.packetState.direct_summand_count_eq_capsuleCount]
  exact audit.direct_summand_count_eq_actionCount

theorem nonarchimedean_directSummandCount_eq
    {audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (audit : DirectSummandPlaceCountAudit audited) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited.placeFamilyCompatibility.ind2Actions.nonarchimedeanActions.length := by
  rw [audit.direct_summand_count_eq_actionCount]
  exact
    audited.placeFamilyCompatibility.ind2Actions.actionCountForKind_nonarchimedean

theorem archimedean_directSummandCount_eq
    {audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (audit : DirectSummandPlaceCountAudit audited) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited.placeFamilyCompatibility.ind2Actions.archimedeanActions.length := by
  rw [audit.direct_summand_count_eq_actionCount]
  exact
    audited.placeFamilyCompatibility.ind2Actions.actionCountForKind_archimedean

theorem nonarchimedean_directSummandCount_eq_fiberCardinality
    {audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (countAudit : DirectSummandPlaceCountAudit audited)
    (fiberAudit :
      IUTStage1NonarchimedeanInd2PlaceFiberAudit
        audited.placeFamilyCompatibility.ind2Actions) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      fiberAudit.fiber.cardinality :=
  (countAudit.nonarchimedean_directSummandCount_eq).trans
    fiberAudit.actionCount_eq_fiberCardinality

theorem archimedean_directSummandCount_eq_fiberCardinality
    {audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (countAudit : DirectSummandPlaceCountAudit audited)
    (fiberAudit :
      IUTStage1ArchimedeanInd2PlaceFiberAudit
        audited.placeFamilyCompatibility.ind2Actions) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      fiberAudit.fiber.cardinality :=
  (countAudit.archimedean_directSummandCount_eq).trans
    fiberAudit.actionCount_eq_fiberCardinality

end DirectSummandPlaceCountAudit

/--
Source-facing nonarchimedean `(Ind2)` fiber package for an audited choice.
-/
structure NonarchimedeanInd2FiberPackage
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  countAudit : DirectSummandPlaceCountAudit audited
  fiberAudit :
    IUTStage1NonarchimedeanInd2PlaceFiberAudit
      audited.placeFamilyCompatibility.ind2Actions

/--
Source-facing archimedean `(Ind2)` fiber package for an audited choice.
-/
structure ArchimedeanInd2FiberPackage
    (audited :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  countAudit : DirectSummandPlaceCountAudit audited
  fiberAudit :
    IUTStage1ArchimedeanInd2PlaceFiberAudit
      audited.placeFamilyCompatibility.ind2Actions

namespace NonarchimedeanInd2FiberPackage

variable
  {audited :
    IUTStage1PlaceAuditedDirectSummandPacketChoice
      coric IUTStage1PlaceKind.nonarchimedean}

theorem directSummandCount_eq_fiberCardinality
    (package : NonarchimedeanInd2FiberPackage audited) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      package.fiberAudit.fiber.cardinality :=
  package.countAudit.nonarchimedean_directSummandCount_eq_fiberCardinality
    package.fiberAudit

theorem capsuleCount_eq_fiberCardinality
    (package : NonarchimedeanInd2FiberPackage audited) :
    audited.choice.local_tensor_state.packetState.capsuleFamily.capsuleCount =
      package.fiberAudit.fiber.cardinality := by
  rw [← audited.choice.local_tensor_state.packetState.direct_summand_count_eq_capsuleCount]
  exact package.directSummandCount_eq_fiberCardinality

end NonarchimedeanInd2FiberPackage

namespace ArchimedeanInd2FiberPackage

variable
  {audited :
    IUTStage1PlaceAuditedDirectSummandPacketChoice
      coric IUTStage1PlaceKind.archimedean}

theorem directSummandCount_eq_fiberCardinality
    (package : ArchimedeanInd2FiberPackage audited) :
    audited.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      package.fiberAudit.fiber.cardinality :=
  package.countAudit.archimedean_directSummandCount_eq_fiberCardinality
    package.fiberAudit

theorem capsuleCount_eq_fiberCardinality
    (package : ArchimedeanInd2FiberPackage audited) :
    audited.choice.local_tensor_state.packetState.capsuleFamily.capsuleCount =
      package.fiberAudit.fiber.cardinality := by
  rw [← audited.choice.local_tensor_state.packetState.direct_summand_count_eq_capsuleCount]
  exact package.directSummandCount_eq_fiberCardinality

end ArchimedeanInd2FiberPackage

/-- Audited `(Ind1)` step preserving the place-family compatibility audit. -/
structure ProcessionAutomorphismStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    Prop where
  choice_step :
    IUTStage1DirectSummandPacketTheorem311Choice.ProcessionAutomorphismStep
      audited₁.choice audited₂.choice
  place_family_compatibility_eq :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility

/-- Audited `(Ind2)` step preserving the place-family compatibility audit. -/
structure LocalTensorDirectSummandActionStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    Prop where
  choice_step :
    IUTStage1DirectSummandPacketTheorem311Choice.LocalTensorDirectSummandActionStep
      audited₁.choice audited₂.choice
  place_family_compatibility_eq :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility

/-- Audited `(Ind3)` step preserving the place-family compatibility audit. -/
structure UpperSemiCompatibilityStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    Prop where
  choice_step :
    IUTStage1DirectSummandPacketTheorem311Choice.UpperSemiCompatibilityStep
      audited₁.choice audited₂.choice
  place_family_compatibility_eq :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility

theorem ind1_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : ProcessionAutomorphismStep audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility :=
  hstep.place_family_compatibility_eq

theorem ind2_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility :=
  hstep.place_family_compatibility_eq

theorem ind3_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : UpperSemiCompatibilityStep audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility :=
  hstep.place_family_compatibility_eq

theorem ind2_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  IUTStage1DirectSummandPacketTheorem311Choice.ind2_preserves_capsuleTotalLogVolume
    hstep.choice_step

theorem ind1_preserves_capsuleNormalizedLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : ProcessionAutomorphismStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume := by
  rw [hstep.choice_step.local_tensor_eq]

theorem ind2_preserves_capsuleNormalizedLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  IUTStage1DirectSummandPacketTheorem311Choice.ind2_preserves_capsuleNormalizedLogVolume
    hstep.choice_step

def ind2_transports_packetNormalizedCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂)
    (compat :
      IUTStage1LocalTensorPacketNormalizedCompatibility
        audited₁.choice.local_tensor_state.packetState) :
    IUTStage1LocalTensorPacketNormalizedCompatibility
      audited₂.choice.local_tensor_state.packetState :=
  IUTStage1DirectSummandPacketTheorem311Choice.ind2_transports_packetNormalizedCompatibility
    hstep.choice_step compat

def ind2_transports_classifiedPacketNormalizedCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂)
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        audited₁.choice.local_tensor_state.packetState) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
      audited₂.choice.local_tensor_state.packetState :=
  IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.ofInd2TransportedPacketNormalization
    (ind2_transports_packetNormalizedCompatibility hstep
      classified.compatibility)

theorem ind2_transports_capsuleContainerBound
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned
        audited₁.choice.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  IUTStage1DirectSummandPacketTheorem311Choice.ind2_transports_capsuleContainerBound
    hstep.choice_step estimate

/--
Audited nonarchimedean `Ism` instance of the direct-summand `(Ind2)` step.
-/
structure NonarchimedeanIsmInd2Step
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) :
    Prop where
  choice_step :
    IUTStage1DirectSummandPacketTheorem311Choice.NonarchimedeanIsmInd2Step
      audited₁.choice audited₂.choice
  place_family_compatibility_eq :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility

/--
Audited archimedean order-two instance of the direct-summand `(Ind2)` step.
-/
structure ArchimedeanOrderTwoInd2Step
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) :
    Prop where
  choice_step :
    IUTStage1DirectSummandPacketTheorem311Choice.ArchimedeanOrderTwoInd2Step
      audited₁.choice audited₂.choice
  place_family_compatibility_eq :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility

def nonarchimedeanIsm_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  { choice_step := by
      exact
        IUTStage1DirectSummandPacketTheorem311Choice.nonarchimedeanIsm_toDirectSummandActionStep
          hstep.choice_step,
    place_family_compatibility_eq :=
      hstep.place_family_compatibility_eq }

def archimedeanOrderTwo_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  { choice_step := by
      exact
        IUTStage1DirectSummandPacketTheorem311Choice.archimedeanOrderTwo_toDirectSummandActionStep
          hstep.choice_step,
    place_family_compatibility_eq :=
      hstep.place_family_compatibility_eq }

theorem nonarchimedeanIsm_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility :=
  hstep.place_family_compatibility_eq

theorem archimedeanOrderTwo_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility :=
  hstep.place_family_compatibility_eq

theorem nonarchimedeanIsm_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (nonarchimedeanIsm_toDirectSummandActionStep hstep)

theorem archimedeanOrderTwo_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (archimedeanOrderTwo_toDirectSummandActionStep hstep)

theorem nonarchimedeanIsm_transports_capsuleContainerBound
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step audited₁ audited₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned
        audited₁.choice.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  ind2_transports_capsuleContainerBound
    (nonarchimedeanIsm_toDirectSummandActionStep hstep) estimate

theorem archimedeanOrderTwo_transports_capsuleContainerBound
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step audited₁ audited₂)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned
        audited₁.choice.local_tensor_state.packetState.capsuleFamily) :
    targetSigned <=
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  ind2_transports_capsuleContainerBound
    (archimedeanOrderTwo_toDirectSummandActionStep hstep) estimate

/--
Audited nonarchimedean `Ism` step tied to an entry in the `(Ind2)`
place-family action data.
-/
structure NonarchimedeanIsmActionEntryStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_entry : IUTStage1NonarchimedeanIsmActionEntry
  action_entry_mem :
    action_entry ∈
      audited₁.placeFamilyCompatibility.ind2Actions.nonarchimedeanActions
  source_step : NonarchimedeanIsmInd2Step audited₁ audited₂
  matching_action_exists :
    ∃ action :
      IUTStage1NonarchimedeanIsmDirectSummandAction
        audited₁.choice.local_tensor_state.summandFamily,
      action.place = action_entry.place ∧
        action.toDirectSummandAction.toCapsuleAction.transformedFamily =
          action_entry.toDirectSummandAction.toCapsuleAction.transformedFamily ∧
        audited₂.choice.local_tensor_state.packetState.capsuleFamily =
          action.toDirectSummandAction.toCapsuleAction.transformedFamily

/--
Audited archimedean order-two step tied to an entry in the `(Ind2)`
place-family action data.
-/
structure ArchimedeanOrderTwoActionEntryStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_entry : IUTStage1ArchimedeanOrderTwoActionEntry
  action_entry_mem :
    action_entry ∈
      audited₁.placeFamilyCompatibility.ind2Actions.archimedeanActions
  source_step : ArchimedeanOrderTwoInd2Step audited₁ audited₂
  matching_action_exists :
    ∃ action :
      IUTStage1ArchimedeanOrderTwoDirectSummandAction
        audited₁.choice.local_tensor_state.summandFamily,
      action.place = action_entry.place ∧
        action.toDirectSummandAction.toCapsuleAction.transformedFamily =
          action_entry.toDirectSummandAction.toCapsuleAction.transformedFamily ∧
        audited₂.choice.local_tensor_state.packetState.capsuleFamily =
          action.toDirectSummandAction.toCapsuleAction.transformedFamily

def nonarchimedeanEntry_toNonarchimedeanIsmStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    NonarchimedeanIsmInd2Step audited₁ audited₂ :=
  hstep.source_step

def archimedeanEntry_toArchimedeanOrderTwoStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    ArchimedeanOrderTwoInd2Step audited₁ audited₂ :=
  hstep.source_step

def nonarchimedeanEntry_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  nonarchimedeanIsm_toDirectSummandActionStep
    (nonarchimedeanEntry_toNonarchimedeanIsmStep hstep)

def archimedeanEntry_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  archimedeanOrderTwo_toDirectSummandActionStep
    (archimedeanEntry_toArchimedeanOrderTwoStep hstep)

theorem nonarchimedeanEntry_place_mem_ind2Actions
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈
      audited₁.placeFamilyCompatibility.ind2Actions.nonarchimedeanPlaces := by
  exact List.mem_map.mpr ⟨hstep.action_entry, hstep.action_entry_mem, rfl⟩

theorem archimedeanEntry_place_mem_ind2Actions
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈
      audited₁.placeFamilyCompatibility.ind2Actions.archimedeanPlaces := by
  exact List.mem_map.mpr ⟨hstep.action_entry, hstep.action_entry_mem, rfl⟩

theorem nonarchimedeanEntry_place_mem_upperSemi
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈
      audited₁.choice.upper_semi_state.nonarchimedeanInclusions.map
        fun entry => entry.place := by
  rw [← audited₁.nonarchimedeanPlaces_eq]
  exact nonarchimedeanEntry_place_mem_ind2Actions hstep

theorem archimedeanEntry_place_mem_upperSemi
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈
      audited₁.choice.upper_semi_state.archimedeanSurjections.map
        fun entry => entry.place := by
  rw [← audited₁.archimedeanPlaces_eq]
  exact archimedeanEntry_place_mem_ind2Actions hstep

theorem nonarchimedeanEntry_place_mem_fiber
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂)
    (fiberAudit :
      IUTStage1NonarchimedeanInd2PlaceFiberAudit
        audited₁.placeFamilyCompatibility.ind2Actions) :
    hstep.action_entry.place ∈ fiberAudit.fiber.places := by
  rw [← fiberAudit.places_eq]
  exact nonarchimedeanEntry_place_mem_ind2Actions hstep

theorem archimedeanEntry_place_mem_fiber
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂)
    (fiberAudit :
      IUTStage1ArchimedeanInd2PlaceFiberAudit
        audited₁.placeFamilyCompatibility.ind2Actions) :
    hstep.action_entry.place ∈ fiberAudit.fiber.places := by
  rw [← fiberAudit.places_eq]
  exact archimedeanEntry_place_mem_ind2Actions hstep

namespace NonarchimedeanInd2FiberPackage

theorem entry_place_mem_fiber
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (package : NonarchimedeanInd2FiberPackage audited₁)
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈ package.fiberAudit.fiber.places :=
  nonarchimedeanEntry_place_mem_fiber hstep package.fiberAudit

end NonarchimedeanInd2FiberPackage

namespace ArchimedeanInd2FiberPackage

theorem entry_place_mem_fiber
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (package : ArchimedeanInd2FiberPackage audited₁)
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    hstep.action_entry.place ∈ package.fiberAudit.fiber.places :=
  archimedeanEntry_place_mem_fiber hstep package.fiberAudit

end ArchimedeanInd2FiberPackage

theorem nonarchimedeanEntry_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (nonarchimedeanEntry_toDirectSummandActionStep hstep)

theorem archimedeanEntry_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (archimedeanEntry_toDirectSummandActionStep hstep)

def indeterminacySourceData :
    IUTStage1Theorem311IndeterminacySourceData
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :=
  { procession_automorphism_step := ProcessionAutomorphismStep,
    local_tensor_symmetry_step := LocalTensorDirectSummandActionStep,
    upper_semi_compatibility_step := UpperSemiCompatibilityStep }

theorem generated_preserves_placeFamilyCompatibility
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        audited₁ audited₂) :
    audited₁.placeFamilyCompatibility =
      audited₂.placeFamilyCompatibility := by
  induction hrel with
  | refl audited =>
      rfl
  | ind1 hstep =>
      exact ind1_preserves_placeFamilyCompatibility hstep
  | ind2 hstep =>
      exact ind2_preserves_placeFamilyCompatibility hstep
  | ind3 hstep =>
      exact ind3_preserves_placeFamilyCompatibility hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_coric
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        audited₁ audited₂) :
    audited₁.choice.coric = audited₂.choice.coric := by
  induction hrel with
  | refl audited =>
      rfl
  | ind1 hstep =>
      exact hstep.choice_step.coric_eq
  | ind2 hstep =>
      exact hstep.choice_step.coric_eq
  | ind3 hstep =>
      exact hstep.choice_step.coric_eq
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

theorem generated_preserves_upperSemiLogVolumeCompatible
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (_hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        audited₁ audited₂) :
    audited₂.choice.upper_semi_state.logVolumeCompatible :=
  audited₂.upperSemi_logVolumeCompatible

theorem image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂) :
    ∀ {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind},
      IUTStage1GeneratedIndeterminacyRelation
        (indeterminacySourceData (coric := coric) (kind := kind)).generators
        audited₁ audited₂ ->
        images.region audited₁ = images.region audited₂ := by
  intro audited₁ audited₂ hrel
  exact hcoric audited₁ audited₂ (generated_preserves_coric hrel)

theorem ind1_image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : ProcessionAutomorphismStep audited₁ audited₂) :
    images.region audited₁ = images.region audited₂ :=
  hcoric audited₁ audited₂ hstep.choice_step.coric_eq

theorem ind2_image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : LocalTensorDirectSummandActionStep audited₁ audited₂) :
    images.region audited₁ = images.region audited₂ :=
  hcoric audited₁ audited₂ hstep.choice_step.coric_eq

theorem nonarchimedeanIsm_image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmInd2Step audited₁ audited₂) :
    images.region audited₁ = images.region audited₂ :=
  ind2_image_invariant_of_coric images hcoric
    (nonarchimedeanIsm_toDirectSummandActionStep hstep)

theorem archimedeanOrderTwo_image_invariant_of_coric
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoInd2Step audited₁ audited₂) :
    images.region audited₁ = images.region audited₂ :=
  ind2_image_invariant_of_coric images hcoric
    (archimedeanOrderTwo_toDirectSummandActionStep hstep)

theorem ind3_image_invariant_of_coric_as_extra_equality
    {target : Copy}
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep : UpperSemiCompatibilityStep audited₁ audited₂) :
    images.region audited₁ = images.region audited₂ :=
  hcoric audited₁ audited₂ hstep.choice_step.coric_eq

end IUTStage1PlaceAuditedDirectSummandPacketChoice

/--
Multiradial possible images indexed by place-audited refined Theorem 3.11
choices.
-/
structure IUTStage1PlaceAuditedMultiradialImages
    {target : Copy}
    (coric : Type u) (kind : IUTStage1PlaceKind) where
  possibleImages :
    RegionFamily target
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
  quotient :
    IUTStage1IndeterminacyQuotient
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
  quotient_eq_generated :
    quotient =
      (IUTStage1PlaceAuditedDirectSummandPacketChoice.indeterminacySourceData
        (coric := coric) (kind := kind)).quotient
  image_invariant :
    ∀ {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind},
      quotient.relation audited₁ audited₂ ->
        possibleImages.region audited₁ = possibleImages.region audited₂

namespace IUTStage1PlaceAuditedMultiradialImages

variable {target : Copy} {coric : Type u} {kind : IUTStage1PlaceKind}

def ofCoricInvariant
    (images :
      RegionFamily target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          images.region audited₁ = images.region audited₂) :
    IUTStage1PlaceAuditedMultiradialImages
      (target := target) coric kind :=
  { possibleImages := images,
    quotient :=
      (IUTStage1PlaceAuditedDirectSummandPacketChoice.indeterminacySourceData
        (coric := coric) (kind := kind)).quotient,
    quotient_eq_generated := rfl,
    image_invariant := by
      intro audited₁ audited₂ hrel
      exact
        IUTStage1PlaceAuditedDirectSummandPacketChoice.image_invariant_of_coric
          images hcoric hrel }

theorem region_eq_of_related
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric kind)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hrel : data.quotient.relation audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.image_invariant hrel

theorem region_eq_of_ind1_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric kind)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ProcessionAutomorphismStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_related (by
    rw [data.quotient_eq_generated]
    exact IUTStage1GeneratedIndeterminacyRelation.ind1 hstep)

theorem region_eq_of_ind2_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric kind)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.LocalTensorDirectSummandActionStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_related (by
    rw [data.quotient_eq_generated]
    exact IUTStage1GeneratedIndeterminacyRelation.ind2 hstep)

theorem region_eq_of_nonarchimedeanIsm_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmInd2Step
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_ind2_step
    (IUTStage1PlaceAuditedDirectSummandPacketChoice.nonarchimedeanIsm_toDirectSummandActionStep
      hstep)

theorem region_eq_of_nonarchimedeanEntry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_nonarchimedeanIsm_step
    (IUTStage1PlaceAuditedDirectSummandPacketChoice.nonarchimedeanEntry_toNonarchimedeanIsmStep
      hstep)

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (fiberPackage :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanInd2FiberPackage
        audited₁)
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep⟩

theorem region_eq_of_archimedeanOrderTwo_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoInd2Step
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_ind2_step
    (IUTStage1PlaceAuditedDirectSummandPacketChoice.archimedeanOrderTwo_toDirectSummandActionStep
      hstep)

theorem region_eq_of_archimedeanEntry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_archimedeanOrderTwo_step
    (IUTStage1PlaceAuditedDirectSummandPacketChoice.archimedeanEntry_toArchimedeanOrderTwoStep
      hstep)

theorem region_eq_and_fiber_mem_of_archimedeanEntry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (fiberPackage :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanInd2FiberPackage
        audited₁)
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep⟩

/--
Equality projection for an `(Ind3)` generator when the supplied possible-image
quotient already carries equality across that generator. This is an extra
equality interface; the source-facing Corollary 3.12 route uses
`NonarchimedeanInd3EntryAlignment` for the Step (x) one-sided upper-semi input.
-/
theorem region_eq_of_ind3_step_from_equalityQuotient
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric kind)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.UpperSemiCompatibilityStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_related (by
    rw [data.quotient_eq_generated]
    exact IUTStage1GeneratedIndeterminacyRelation.ind3 hstep)

theorem quotient_profile
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric kind) :
    data.quotient.profile = theorem311IndeterminacyProfile := by
  rw [data.quotient_eq_generated]
  exact
    IUTStage1Theorem311IndeterminacySourceData.quotient_profile
      (IUTStage1PlaceAuditedDirectSummandPacketChoice.indeterminacySourceData
        (coric := coric) (kind := kind))

end IUTStage1PlaceAuditedMultiradialImages

/--
Source-package version of place-audited refined multiradial theta images.
-/
structure IUTStage1PlaceAuditedMultiradialThetaImages
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)) where
  multiradialOutput : MultiradialOutputId
  possibleImages : IUTStage1ThetaPilotPossibleImages package
  auditedImages :
    IUTStage1PlaceAuditedMultiradialImages
      (target := target) coric kind
  multiradial_output_eq : multiradialOutput = package.multiradialOutput
  audited_possibleImages_eq :
    auditedImages.possibleImages = possibleImages.images

namespace IUTStage1PlaceAuditedMultiradialThetaImages

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)}

def ofPackageWithCoricInvariant
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind))
    (hcoric :
      ∀ audited₁ audited₂,
        audited₁.choice.coric = audited₂.choice.coric ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            audited₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            audited₂) :
    IUTStage1PlaceAuditedMultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    auditedImages :=
      IUTStage1PlaceAuditedMultiradialImages.ofCoricInvariant
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
        hcoric,
    multiradial_output_eq := rfl,
    audited_possibleImages_eq := rfl }

theorem region_eq_of_related
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hrel : data.auditedImages.quotient.relation audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_related hrel

theorem region_eq_of_ind1_step
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ProcessionAutomorphismStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_ind1_step hstep

theorem region_eq_of_ind2_step
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.LocalTensorDirectSummandActionStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_ind2_step hstep

theorem region_eq_of_nonarchimedeanIsm_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmInd2Step
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_nonarchimedeanIsm_step hstep

theorem region_eq_of_nonarchimedeanEntry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_nonarchimedeanEntry_step hstep

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (fiberPackage :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanInd2FiberPackage
        audited₁)
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep⟩

theorem region_eq_of_archimedeanOrderTwo_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoInd2Step
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_archimedeanOrderTwo_step hstep

theorem region_eq_of_archimedeanEntry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_archimedeanEntry_step hstep

theorem region_eq_and_fiber_mem_of_archimedeanEntry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (fiberPackage :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanInd2FiberPackage
        audited₁)
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep⟩

/--
Equality projection for an `(Ind3)` generator when the supplied audited
possible-image quotient already carries equality across that generator. This is
not the Step (x) upper-semi input used by the Corollary 3.12 route.
-/
theorem region_eq_of_ind3_step_from_equalityQuotient
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.UpperSemiCompatibilityStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_ind3_step_from_equalityQuotient hstep

theorem quotient_profile
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package) :
    data.auditedImages.quotient.profile =
      theorem311IndeterminacyProfile :=
  data.auditedImages.quotient_profile

theorem union_eq_targetUnion
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package) :
    data.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  data.possibleImages.union_eq_targetUnion

end IUTStage1PlaceAuditedMultiradialThetaImages

/--
Refined obligation that source-package Theta-pilot possible images depend only
on the coric coordinate of direct-summand packet choices.

This is the refined Theorem 3.11 multiradiality obligation: it is stated for the
choice type whose `(Ind2)` coordinate carries direct summands, capsules, and
log-volume data.
-/
structure IUTStage1RefinedThetaImagesDependOnlyOnCoric
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind)) :
    Prop where
  region_eq_of_coric_eq :
    ∀ choice₁ choice₂,
      choice₁.coric = choice₂.coric ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂

namespace IUTStage1RefinedThetaImagesDependOnlyOnCoric

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)}

def toRefinedMultiradialThetaImages
    (dependence : IUTStage1RefinedThetaImagesDependOnlyOnCoric package) :
    IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package :=
  IUTStage1RefinedDirectSummandPacketMultiradialThetaImages.ofPackageWithCoricInvariant
    package dependence.region_eq_of_coric_eq

theorem imageInvariant
    (dependence : IUTStage1RefinedThetaImagesDependOnlyOnCoric package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      dependence.toRefinedMultiradialThetaImages.refinedImages.quotient.relation
        choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  dependence.toRefinedMultiradialThetaImages.region_eq_of_related hrel

theorem quotientProfile
    (dependence : IUTStage1RefinedThetaImagesDependOnlyOnCoric package) :
    dependence.toRefinedMultiradialThetaImages.refinedImages.quotient.profile =
      theorem311IndeterminacyProfile :=
  dependence.toRefinedMultiradialThetaImages.quotient_profile

theorem union_eq_targetUnion
    (dependence : IUTStage1RefinedThetaImagesDependOnlyOnCoric package) :
    dependence.toRefinedMultiradialThetaImages.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  dependence.toRefinedMultiradialThetaImages.union_eq_targetUnion

end IUTStage1RefinedThetaImagesDependOnlyOnCoric

/--
Named source subclaim for the refined Theorem 3.11 multiradial representation.

The field is intentionally just the refined coric-dependence obligation.  It
does not assert the Corollary 3.12 inequality or collapse the refined
indeterminacy relation into equality of all representatives.
-/
structure IUTStage1Theorem311RefinedMultiradialSubclaim
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind)) :
    Prop where
  theta_images_depend_only_on_coric :
    IUTStage1RefinedThetaImagesDependOnlyOnCoric package

namespace IUTStage1Theorem311RefinedMultiradialSubclaim

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)}

def toRefinedThetaImagesDependOnlyOnCoric
    (subclaim : IUTStage1Theorem311RefinedMultiradialSubclaim package) :
    IUTStage1RefinedThetaImagesDependOnlyOnCoric package :=
  subclaim.theta_images_depend_only_on_coric

def toRefinedMultiradialThetaImages
    (subclaim : IUTStage1Theorem311RefinedMultiradialSubclaim package) :
    IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package :=
  subclaim.toRefinedThetaImagesDependOnlyOnCoric.toRefinedMultiradialThetaImages

theorem imageInvariant
    (subclaim : IUTStage1Theorem311RefinedMultiradialSubclaim package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel : subclaim.toRefinedMultiradialThetaImages.refinedImages.quotient.relation
      choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  subclaim.toRefinedMultiradialThetaImages.region_eq_of_related hrel

theorem quotientProfile
    (subclaim : IUTStage1Theorem311RefinedMultiradialSubclaim package) :
    subclaim.toRefinedMultiradialThetaImages.refinedImages.quotient.profile =
      theorem311IndeterminacyProfile :=
  subclaim.toRefinedMultiradialThetaImages.quotient_profile

theorem union_eq_targetUnion
    (subclaim : IUTStage1Theorem311RefinedMultiradialSubclaim package) :
    subclaim.toRefinedMultiradialThetaImages.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  subclaim.toRefinedMultiradialThetaImages.union_eq_targetUnion

end IUTStage1Theorem311RefinedMultiradialSubclaim

/--
Generator-wise refined multiradial invariance for direct-summand packet
Theorem 3.11 choices.

This decomposes refined image invariance into the three source generators
`(Ind1)`, `(Ind2)`, and `(Ind3)`.
-/
structure IUTStage1RefinedThetaImageGeneratorInvariance
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind)) :
    Prop where
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind},
      IUTStage1DirectSummandPacketTheorem311Choice.ProcessionAutomorphismStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind},
      IUTStage1DirectSummandPacketTheorem311Choice.LocalTensorDirectSummandActionStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind3_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind},
      IUTStage1DirectSummandPacketTheorem311Choice.UpperSemiCompatibilityStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂

namespace IUTStage1RefinedThetaImageGeneratorInvariance

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)}

theorem generatedImageInvariant
    (invariance : IUTStage1RefinedThetaImageGeneratorInvariance package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (IUTStage1DirectSummandPacketTheorem311Choice.indeterminacySourceData
          (coric := coric) (kind := kind)).generators choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  IUTStage1GeneratedIndeterminacyRelation.image_invariant
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
    invariance.ind1_region_eq
    invariance.ind2_region_eq
    invariance.ind3_region_eq
    hrel

def toRefinedMultiradialThetaImages
    (invariance : IUTStage1RefinedThetaImageGeneratorInvariance package) :
    IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    refinedImages :=
      { possibleImages :=
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images,
        quotient :=
          (IUTStage1DirectSummandPacketTheorem311Choice.indeterminacySourceData
            (coric := coric) (kind := kind)).quotient,
        quotient_eq_generated := rfl,
        image_invariant := by
          intro choice₁ choice₂ hrel
          exact invariance.generatedImageInvariant hrel },
    multiradial_output_eq := rfl,
    refined_possibleImages_eq := rfl }

theorem imageInvariant
    (invariance : IUTStage1RefinedThetaImageGeneratorInvariance package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel :
      invariance.toRefinedMultiradialThetaImages.refinedImages.quotient.relation
        choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  invariance.toRefinedMultiradialThetaImages.region_eq_of_related hrel

theorem quotientProfile
    (invariance : IUTStage1RefinedThetaImageGeneratorInvariance package) :
    invariance.toRefinedMultiradialThetaImages.refinedImages.quotient.profile =
      theorem311IndeterminacyProfile :=
  invariance.toRefinedMultiradialThetaImages.quotient_profile

theorem union_eq_targetUnion
    (invariance : IUTStage1RefinedThetaImageGeneratorInvariance package) :
    invariance.toRefinedMultiradialThetaImages.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  invariance.toRefinedMultiradialThetaImages.union_eq_targetUnion

end IUTStage1RefinedThetaImageGeneratorInvariance

/--
Named source subclaim that proves refined multiradiality generator by
generator.
-/
structure IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim
    {source target : Copy} {coric : Type u}
    {kind : IUTStage1PlaceKind}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice coric kind)) :
    Prop where
  generator_invariance :
    IUTStage1RefinedThetaImageGeneratorInvariance package

namespace IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim

variable {source target : Copy} {coric : Type u}
variable {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice coric kind)}

def toRefinedThetaImageGeneratorInvariance
    (subclaim :
      IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim package) :
    IUTStage1RefinedThetaImageGeneratorInvariance package :=
  subclaim.generator_invariance

def toRefinedMultiradialThetaImages
    (subclaim :
      IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim package) :
    IUTStage1RefinedDirectSummandPacketMultiradialThetaImages package :=
  subclaim.toRefinedThetaImageGeneratorInvariance.toRefinedMultiradialThetaImages

theorem imageInvariant
    (subclaim :
      IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice coric kind}
    (hrel : subclaim.toRefinedMultiradialThetaImages.refinedImages.quotient.relation
      choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  subclaim.toRefinedMultiradialThetaImages.region_eq_of_related hrel

theorem quotientProfile
    (subclaim :
      IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim package) :
    subclaim.toRefinedMultiradialThetaImages.refinedImages.quotient.profile =
      theorem311IndeterminacyProfile :=
  subclaim.toRefinedMultiradialThetaImages.quotient_profile

theorem union_eq_targetUnion
    (subclaim :
      IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim package) :
    subclaim.toRefinedMultiradialThetaImages.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  subclaim.toRefinedMultiradialThetaImages.union_eq_targetUnion

end IUTStage1Theorem311RefinedGeneratorInvarianceSubclaim

/--
Generator-wise image invariance for the nonarchimedean `Ism` refined quotient.
-/
structure IUTStage1NonarchimedeanIsmThetaImageGeneratorInvariance
    {source target : Copy} {coric : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.nonarchimedean)) :
    Prop where
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.ProcessionAutomorphismStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.NonarchimedeanIsmInd2Step
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind3_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.UpperSemiCompatibilityStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂

/--
Generator-wise image invariance for the archimedean order-two refined quotient.
-/
structure IUTStage1ArchimedeanOrderTwoThetaImageGeneratorInvariance
    {source target : Copy} {coric : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.archimedean)) :
    Prop where
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.ProcessionAutomorphismStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.ArchimedeanOrderTwoInd2Step
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂
  ind3_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean},
      IUTStage1DirectSummandPacketTheorem311Choice.UpperSemiCompatibilityStep
        choice₁ choice₂ ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂

namespace IUTStage1NonarchimedeanIsmThetaImageGeneratorInvariance

variable {source target : Copy} {coric : Type u}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean)}

theorem generatedImageInvariant
    (invariance :
      IUTStage1NonarchimedeanIsmThetaImageGeneratorInvariance package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (IUTStage1DirectSummandPacketTheorem311Choice.nonarchimedeanIsmIndeterminacySourceData
          (coric := coric)).generators choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  IUTStage1GeneratedIndeterminacyRelation.image_invariant
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
    invariance.ind1_region_eq
    invariance.ind2_region_eq
    invariance.ind3_region_eq
    hrel

end IUTStage1NonarchimedeanIsmThetaImageGeneratorInvariance

namespace IUTStage1ArchimedeanOrderTwoThetaImageGeneratorInvariance

variable {source target : Copy} {coric : Type u}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean)}

theorem generatedImageInvariant
    (invariance :
      IUTStage1ArchimedeanOrderTwoThetaImageGeneratorInvariance package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (IUTStage1DirectSummandPacketTheorem311Choice.archimedeanOrderTwoIndeterminacySourceData
          (coric := coric)).generators choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  IUTStage1GeneratedIndeterminacyRelation.image_invariant
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
    invariance.ind1_region_eq
    invariance.ind2_region_eq
    invariance.ind3_region_eq
    hrel

end IUTStage1ArchimedeanOrderTwoThetaImageGeneratorInvariance

/-- Source-level multiradial image package for the nonarchimedean `Ism` quotient. -/
structure IUTStage1NonarchimedeanIsmMultiradialThetaImages
    {source target : Copy} {coric : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.nonarchimedean)) where
  multiradialOutput : MultiradialOutputId
  possibleImages : IUTStage1ThetaPilotPossibleImages package
  quotient :
    IUTStage1IndeterminacyQuotient
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean)
  quotient_eq_generated :
    quotient =
      (IUTStage1DirectSummandPacketTheorem311Choice.nonarchimedeanIsmIndeterminacySourceData
        (coric := coric)).quotient
  multiradial_output_eq : multiradialOutput = package.multiradialOutput
  image_invariant :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean},
      quotient.relation choice₁ choice₂ ->
        possibleImages.images.region choice₁ =
          possibleImages.images.region choice₂

/-- Source-level multiradial image package for the archimedean order-two quotient. -/
structure IUTStage1ArchimedeanOrderTwoMultiradialThetaImages
    {source target : Copy} {coric : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.archimedean)) where
  multiradialOutput : MultiradialOutputId
  possibleImages : IUTStage1ThetaPilotPossibleImages package
  quotient :
    IUTStage1IndeterminacyQuotient
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean)
  quotient_eq_generated :
    quotient =
      (IUTStage1DirectSummandPacketTheorem311Choice.archimedeanOrderTwoIndeterminacySourceData
        (coric := coric)).quotient
  multiradial_output_eq : multiradialOutput = package.multiradialOutput
  image_invariant :
    ∀ {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean},
      quotient.relation choice₁ choice₂ ->
        possibleImages.images.region choice₁ =
          possibleImages.images.region choice₂

namespace IUTStage1NonarchimedeanIsmMultiradialThetaImages

variable {source target : Copy} {coric : Type u}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean)}

def ofGeneratorInvariance
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.nonarchimedean))
    (invariance :
      IUTStage1NonarchimedeanIsmThetaImageGeneratorInvariance package) :
    IUTStage1NonarchimedeanIsmMultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    quotient :=
      (IUTStage1DirectSummandPacketTheorem311Choice.nonarchimedeanIsmIndeterminacySourceData
        (coric := coric)).quotient,
    quotient_eq_generated := rfl,
    multiradial_output_eq := rfl,
    image_invariant := by
      intro choice₁ choice₂ hrel
      exact invariance.generatedImageInvariant hrel }

theorem region_eq_of_related
    (data : IUTStage1NonarchimedeanIsmMultiradialThetaImages package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hrel : data.quotient.relation choice₁ choice₂) :
    data.possibleImages.images.region choice₁ =
      data.possibleImages.images.region choice₂ :=
  data.image_invariant hrel

theorem quotient_profile
    (data : IUTStage1NonarchimedeanIsmMultiradialThetaImages package) :
    data.quotient.profile = theorem311IndeterminacyProfile := by
  rw [data.quotient_eq_generated]
  exact
    IUTStage1Theorem311IndeterminacySourceData.quotient_profile
      (IUTStage1DirectSummandPacketTheorem311Choice.nonarchimedeanIsmIndeterminacySourceData
        (coric := coric))

theorem union_eq_targetUnion
    (data : IUTStage1NonarchimedeanIsmMultiradialThetaImages package) :
    data.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  data.possibleImages.union_eq_targetUnion

end IUTStage1NonarchimedeanIsmMultiradialThetaImages

namespace IUTStage1ArchimedeanOrderTwoMultiradialThetaImages

variable {source target : Copy} {coric : Type u}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean)}

def ofGeneratorInvariance
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1DirectSummandPacketTheorem311Choice
          coric IUTStage1PlaceKind.archimedean))
    (invariance :
      IUTStage1ArchimedeanOrderTwoThetaImageGeneratorInvariance package) :
    IUTStage1ArchimedeanOrderTwoMultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    quotient :=
      (IUTStage1DirectSummandPacketTheorem311Choice.archimedeanOrderTwoIndeterminacySourceData
        (coric := coric)).quotient,
    quotient_eq_generated := rfl,
    multiradial_output_eq := rfl,
    image_invariant := by
      intro choice₁ choice₂ hrel
      exact invariance.generatedImageInvariant hrel }

theorem region_eq_of_related
    (data : IUTStage1ArchimedeanOrderTwoMultiradialThetaImages package)
    {choice₁ choice₂ :
      IUTStage1DirectSummandPacketTheorem311Choice
        coric IUTStage1PlaceKind.archimedean}
    (hrel : data.quotient.relation choice₁ choice₂) :
    data.possibleImages.images.region choice₁ =
      data.possibleImages.images.region choice₂ :=
  data.image_invariant hrel

theorem quotient_profile
    (data : IUTStage1ArchimedeanOrderTwoMultiradialThetaImages package) :
    data.quotient.profile = theorem311IndeterminacyProfile := by
  rw [data.quotient_eq_generated]
  exact
    IUTStage1Theorem311IndeterminacySourceData.quotient_profile
      (IUTStage1DirectSummandPacketTheorem311Choice.archimedeanOrderTwoIndeterminacySourceData
        (coric := coric))

theorem union_eq_targetUnion
    (data : IUTStage1ArchimedeanOrderTwoMultiradialThetaImages package) :
    data.possibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  data.possibleImages.union_eq_targetUnion

end IUTStage1ArchimedeanOrderTwoMultiradialThetaImages

/--
Multiradial possible images of the Theta-pilot, recorded together with the
indeterminacy quotient on choices.

The key field is `image_invariant`: related choices give the same target
region. If the quotient includes `(Ind3)`, this field is a stronger extra
obligation than the Corollary 3.12 Step (x) log-volume statement: in the source
text `(Ind3)` becomes an upper-semi inequality after applying log-volume.
The source-faithful one-sided route is the procession-normalized corridor, not
this optional equality quotient.
-/
structure IUTStage1MultiradialThetaImages
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  multiradialOutput : MultiradialOutputId
  possibleImages : IUTStage1ThetaPilotPossibleImages package
  quotient : IUTStage1IndeterminacyQuotient index
  multiradial_output_eq : multiradialOutput = package.multiradialOutput
  image_invariant :
    ∀ {choice₁ choice₂ : index},
      quotient.relation choice₁ choice₂ ->
        possibleImages.images.region choice₁ =
          possibleImages.images.region choice₂

namespace IUTStage1MultiradialThetaImages

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def ofPackageWithQuotient
    (package : IUTStage1SourcePackage source target index)
    (quotient : IUTStage1IndeterminacyQuotient index)
    (hinvariant :
      ∀ {choice₁ choice₂ : index},
        quotient.relation choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂) :
    IUTStage1MultiradialThetaImages package :=
  { multiradialOutput := package.multiradialOutput,
    possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    quotient := quotient,
    multiradial_output_eq := rfl,
    image_invariant := hinvariant }

/--
Generated quotient constructor. The `hInd3` argument is deliberately an
explicit equality hypothesis on possible-image regions; it is not inferred from
the paper's Step (x) upper-semi statement.
-/
def ofPackageWithGeneratedQuotient
    (package : IUTStage1SourcePackage source target index)
    (steps : IUTStage1IndeterminacyGenerators index)
    (hInd1 :
      ∀ {choice₁ choice₂ : index},
        steps.ind1_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂)
    (hInd2 :
      ∀ {choice₁ choice₂ : index},
        steps.ind2_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂)
    (hInd3 :
      ∀ {choice₁ choice₂ : index},
        steps.ind3_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂) :
    IUTStage1MultiradialThetaImages package :=
  ofPackageWithQuotient package
    (IUTStage1IndeterminacyQuotient.generated steps)
    (IUTStage1GeneratedIndeterminacyRelation.image_invariant
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images
      hInd1 hInd2 hInd3)

def ofPackageWithCoordinateQuotient
    {coric ind1State ind2State ind3State : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1IndeterminacyChoice coric ind1State ind2State ind3State))
    (hcoric :
      ∀ choice₁ choice₂,
        choice₁.coric = choice₂.coric ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
              choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
              choice₂) :
    IUTStage1MultiradialThetaImages package :=
  ofPackageWithGeneratedQuotient package
    (IUTStage1IndeterminacyChoice.coordinateGenerators
      (coric := coric) (ind1State := ind1State)
      (ind2State := ind2State) (ind3State := ind3State))
    (by
      intro choice₁ choice₂ hstep
      exact hcoric choice₁ choice₂ hstep.1)
    (by
      intro choice₁ choice₂ hstep
      exact hcoric choice₁ choice₂ hstep.1)
    (by
      intro choice₁ choice₂ hstep
      exact hcoric choice₁ choice₂ hstep.1)

/--
Theorem 3.11 indeterminacy quotient constructor. The `(Ind3)` equality input is
an explicit possible-image equality hypothesis, separate from the one-sided
upper-semi input used in the source-facing Corollary 3.12 route.
-/
def ofPackageWithTheorem311Indeterminacies
    (package : IUTStage1SourcePackage source target index)
    (indeterminacyData :
      IUTStage1Theorem311IndeterminacySourceData index)
    (hInd1 :
      ∀ {choice₁ choice₂ : index},
        indeterminacyData.procession_automorphism_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂)
    (hInd2 :
      ∀ {choice₁ choice₂ : index},
        indeterminacyData.local_tensor_symmetry_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂)
    (hInd3 :
      ∀ {choice₁ choice₂ : index},
        indeterminacyData.upper_semi_compatibility_step choice₁ choice₂ ->
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₁ =
            (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region choice₂) :
    IUTStage1MultiradialThetaImages package :=
  ofPackageWithGeneratedQuotient package indeterminacyData.generators
    hInd1 hInd2 hInd3

def union (images : IUTStage1MultiradialThetaImages package) :
    Region target :=
  images.possibleImages.union

theorem union_eq_targetUnion
    (images : IUTStage1MultiradialThetaImages package) :
    images.union = package.preLedger.output.comparisons.targetUnion :=
  images.possibleImages.union_eq_targetUnion

theorem region_eq_of_related
    (images : IUTStage1MultiradialThetaImages package)
    {choice₁ choice₂ : index}
    (hrel : images.quotient.relation choice₁ choice₂) :
    images.possibleImages.images.region choice₁ =
      images.possibleImages.images.region choice₂ :=
  images.image_invariant hrel

theorem multiradialOutputMatchesPackage
    (images : IUTStage1MultiradialThetaImages package) :
    images.multiradialOutput = package.multiradialOutput :=
  images.multiradial_output_eq

theorem thetaPilotMatchesPackage
    (images : IUTStage1MultiradialThetaImages package) :
    images.possibleImages.thetaPilot = package.thetaPilot :=
  images.possibleImages.thetaPilotMatchesPackage

theorem indeterminaciesMatchPackage
    (images : IUTStage1MultiradialThetaImages package) :
    images.possibleImages.indeterminacies = package.indeterminacies :=
  images.possibleImages.indeterminaciesMatchPackage

def toRemark395PossibleImageFamilySource
    (images : IUTStage1MultiradialThetaImages package)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    IUTStage1Remark395PossibleImageFamilySource (Point target) index :=
  { hullOperator := hullOperator,
    possibleRegion := images.possibleImages.possibleImageSet }

set_option linter.style.longLine false in
/--
Theorem 3.11 indeterminacy bridge to Remark 3.9.5(v)--(vi) Ob5.

Once a multiradial possible-image package supplies a typed
`(Ind1),(Ind2),(Ind3)` quotient and image invariance for related choices, the
corresponding Remark 3.9.5 possible-image family has the expected Ob5 collapse:
related possible-image regions are equal, both lie in the family hull
`phi(P_B)`, and the upper-semi quotient by this hull identifies their images.
-/
theorem remark395Ob5QuotientEndpoint_of_related
    (images : IUTStage1MultiradialThetaImages package)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    {choice₁ choice₂ : index}
    (hrel : images.quotient.relation choice₁ choice₂)
    (hne₁ :
      (images.possibleImages.possibleImageSet choice₁).Nonempty)
    (hne₂ :
      (images.possibleImages.possibleImageSet choice₂).Nonempty) :
    let familySource :=
      images.toRemark395PossibleImageFamilySource hullOperator;
    familySource.possibleRegion choice₁ =
        familySource.possibleRegion choice₂ ∧
      familySource.familyUnion ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion choice₁ ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion choice₂ ⊆ familySource.canonicalHull ∧
      familySource.canonicalPhi.approximant = familySource.canonicalHull ∧
      familySource.hullOperator.isClosed familySource.canonicalHull ∧
      familySource.quotientMap '' (familySource.possibleRegion choice₁) =
        familySource.quotientMap '' (familySource.possibleRegion choice₂) :=
  by
    intro familySource
    have hregion :
        familySource.possibleRegion choice₁ =
          familySource.possibleRegion choice₂ :=
      congrArg Region.toSet (images.region_eq_of_related hrel)
    exact
      ⟨hregion,
        familySource.familyUnion_subset_phi,
        familySource.possibleRegion_subset_phi choice₁,
        familySource.possibleRegion_subset_phi choice₂,
        familySource.canonicalPhi_approximant_eq_phi,
        familySource.phi_closed,
        familySource.quotientMap_images_eq choice₁ choice₂ hne₁ hne₂⟩

set_option linter.style.longLine false in
/--
Theorem 3.11 indeterminacy bridge through Remark 3.9.5 Ob5--Ob7.

This is the source-facing audit that keeps the three pieces reviewed together:
the `(Ind1),(Ind2),(Ind3)` quotient identifies related possible images as in
Ob5; the `Phi`/`Xi` hull-approximant passage supplies the Ob6 log-volume
inequalities; and the retained `F^{×μ}` prime-strip lift supplies the Ob7
log-Kummer/Frobenioid compatibility.  The extra equalities tie the supplied Ob7
hull/determinant bridge to the Theorem 3.11 possible-image family rather than
allowing it to float as an unrelated real-line comparison.
-/
theorem remark395Ob5Ob6Ob7Endpoint_of_related
    {κ : Type w} {β Penv Pgau V μ : Type x}
    [Fintype β] [Fintype Penv] [Fintype Pgau] [Fintype V]
    (images : IUTStage1MultiradialThetaImages package)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    (phiFamily :
      (images.toRemark395PossibleImageFamilySource hullOperator).PhiFamily κ)
    (xiFamily :
      (images.toRemark395PossibleImageFamilySource hullOperator).XiFamily κ)
    (k : κ)
    {choice₁ choice₂ : index}
    (hrel : images.quotient.relation choice₁ choice₂)
    (hne₁ :
      (images.possibleImages.possibleImageSet choice₁).Nonempty)
    (hne₂ :
      (images.possibleImages.possibleImageSet choice₂).Nonempty)
    (ob7Source :
      IUTStage1Remark395Ob7LogKummerCompatibilitySource
        (Point target) index β Penv Pgau V μ)
    (ob7_possibleRegion_eq :
      ob7Source.bridgeSource.possibleRegion =
        (images.toRemark395PossibleImageFamilySource
          hullOperator).possibleRegion)
    (ob7_hullOperator_eq :
      ob7Source.bridgeSource.hullOperator = hullOperator) :
    let familySource :=
      images.toRemark395PossibleImageFamilySource hullOperator;
    familySource.possibleRegion choice₁ =
        familySource.possibleRegion choice₂ ∧
      familySource.familyUnion ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion choice₁ ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion choice₂ ⊆ familySource.canonicalHull ∧
      familySource.quotientMap '' (familySource.possibleRegion choice₁) =
        familySource.quotientMap '' (familySource.possibleRegion choice₂) ∧
      familySource.HPhi phiFamily = familySource.canonicalHull ∧
      familySource.hullOperator.logVolume familySource.familyUnion <=
        familySource.hullOperator.logVolume (familySource.HPhi phiFamily) ∧
      familySource.hullOperator.logVolume (familySource.possibleRegion choice₁) <=
        familySource.hullOperator.logVolume (familySource.HPhi phiFamily) ∧
      familySource.HXi xiFamily = familySource.canonicalHull ∧
      familySource.hullOperator.logVolume familySource.familyUnion <=
        familySource.hullOperator.logVolume (familySource.HXi xiFamily) ∧
      familySource.hullOperator.logVolume (familySource.possibleRegion choice₁) <=
        familySource.hullOperator.logVolume (familySource.HXi xiFamily) ∧
      familySource.hullOperator.logVolume
          ((xiFamily.exactApproximant k).approximant).approximant =
        familySource.hullOperator.logVolume familySource.familyUnion ∧
      ob7Source.bridgeSource.qRegion ⊆ familySource.canonicalHull ∧
      ob7Source.bridgeSource.qRegionLogVolume <=
        ob7Source.primeStripGlobalLogVolume ∧
      (∀ p : Penv,
        ob7Source.primeStripLift.base.gaussianPrimeToPlace
            (ob7Source.primeStripLift.base.primeEvaluation p) =
          ob7Source.primeStripLift.base.environmentPrimeToPlace p ∧
        (ob7Source.primeStripLift.base.localEvaluation.gaussianLocal.localObject
            (ob7Source.primeStripLift.base.gaussianPrimeToPlace
              (ob7Source.primeStripLift.base.primeEvaluation p))).realifiedLogVolume =
          (ob7Source.primeStripLift.base.localEvaluation.environmentLocal.localObject
            (ob7Source.primeStripLift.base.environmentPrimeToPlace p)).realifiedLogVolume ∧
        ob7Source.primeStripLift.gaussianUnitCharacter
            (ob7Source.primeStripLift.base.primeEvaluation p) =
          ob7Source.primeStripLift.environmentUnitCharacter p) :=
  by
    intro familySource
    have hob5 :=
      images.remark395Ob5QuotientEndpoint_of_related
        hullOperator hrel hne₁ hne₂
    have hob6 :=
      familySource.PhiXi_ob6_logVolume_endpoint
        phiFamily xiFamily k choice₁
    rcases hob5 with
      ⟨hregion, hfamily_subset, hchoice₁_subset, hchoice₂_subset,
        _hcanonicalPhi, _hphi_closed, hquotient⟩
    rcases hob6 with
      ⟨hHPhi_eq, _hHPhi_subset, _hphi_subset_HPhi, hfamily_le_HPhi,
        _hHPhi_log, hchoice₁_le_HPhi, hHXi_eq, _hHXi_subset,
        _hphi_subset_HXi, hfamily_le_HXi, _hHXi_log, hchoice₁_le_HXi,
        hxi_exact_log⟩
    have hbridgeHull :
        ob7Source.bridgeSource.familyHull = familySource.canonicalHull := by
      dsimp [IUTStage1Remark395HullDeterminantBridgeSource.familyHull,
        IUTStage1Remark395PossibleImageFamilySource.canonicalHull,
        IUTStage1Remark395HullDeterminantBridgeSource.familyUnion,
        IUTStage1Remark395PossibleImageFamilySource.familyUnion,
        familySource]
      rw [ob7_hullOperator_eq, ob7_possibleRegion_eq]
      simp [IUTStage1MultiradialThetaImages.toRemark395PossibleImageFamilySource]
    have hq_subset_family :
        ob7Source.bridgeSource.qRegion ⊆ familySource.canonicalHull := by
      intro x hx
      exact hbridgeHull ▸ ob7Source.bridgeSource.qRegion_subset_familyHull hx
    exact
      ⟨hregion,
        hfamily_subset,
        hchoice₁_subset,
        hchoice₂_subset,
        hquotient,
        hHPhi_eq,
        hfamily_le_HPhi,
        hchoice₁_le_HPhi,
        hHXi_eq,
        hfamily_le_HXi,
        hchoice₁_le_HXi,
        hxi_exact_log,
        hq_subset_family,
        ob7Source.qRegionLogVolume_le_primeStripGlobal,
        fun p =>
          ⟨ob7Source.gaussianPlaceOfEvaluation_eq_environmentPlace p,
            ob7Source.gaussianLocalLogVolume_at_evaluatedPrime_eq_environment p,
            ob7Source.gaussianUnitCharacter_at_evaluatedPrime p⟩⟩

end IUTStage1MultiradialThetaImages

/--
Obligation that Theta-pilot possible images depend only on the coric coordinate
of a coordinate choice.

This is the source-facing form of the multiradiality requirement needed by the
generated quotient interface. When applied to an `(Ind3)` generator it is an
extra equality hypothesis; the Step (x) Corollary 3.12 route instead uses the
upper-semi log-volume corridor.
-/
structure IUTStage1ThetaImagesDependOnlyOnCoric
    {source target : Copy}
    {coric ind1State ind2State ind3State : Type u}
    (package :
      IUTStage1SourcePackage source target
        (IUTStage1IndeterminacyChoice coric ind1State ind2State ind3State)) :
    Prop where
  region_eq_of_coric_eq :
    ∀ choice₁ choice₂,
      choice₁.coric = choice₂.coric ->
        (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₁ =
          (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
            choice₂

namespace IUTStage1ThetaImagesDependOnlyOnCoric

variable {source target : Copy}
variable {coric ind1State ind2State ind3State : Type u}
variable {package :
  IUTStage1SourcePackage source target
    (IUTStage1IndeterminacyChoice coric ind1State ind2State ind3State)}

def toMultiradialThetaImages
    (dependence : IUTStage1ThetaImagesDependOnlyOnCoric package) :
    IUTStage1MultiradialThetaImages package :=
  IUTStage1MultiradialThetaImages.ofPackageWithCoordinateQuotient
    package dependence.region_eq_of_coric_eq

theorem imageInvariant
    (dependence : IUTStage1ThetaImagesDependOnlyOnCoric package)
    {choice₁ choice₂ :
      IUTStage1IndeterminacyChoice coric ind1State ind2State ind3State}
    (hrel :
      IUTStage1GeneratedIndeterminacyRelation
        (IUTStage1IndeterminacyChoice.coordinateGenerators
          (coric := coric) (ind1State := ind1State)
          (ind2State := ind2State) (ind3State := ind3State))
        choice₁ choice₂) :
    (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₁ =
      (IUTStage1ThetaPilotPossibleImages.ofPackage package).images.region
        choice₂ :=
  (dependence.toMultiradialThetaImages).region_eq_of_related hrel

theorem union_eq_targetUnion
    (dependence : IUTStage1ThetaImagesDependOnlyOnCoric package) :
    dependence.toMultiradialThetaImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  dependence.toMultiradialThetaImages.union_eq_targetUnion

end IUTStage1ThetaImagesDependOnlyOnCoric

/--
Typed `(Ind1)` action on a Theorem 3.11 choice space.

This is the source-facing action layer used by the local-to-global
`C_\Theta` milestone.  The action is not represented by names or boolean
flags: it is a relation on choices, together with the paper-side invariant that
procession-normalized log-volume is unchanged along `(Ind1)`.
-/
structure IUTStage1Theorem311Ind1Action (choice : Type u) where
  step : choice -> choice -> Prop
  logVolume : choice -> Real
  preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂ : choice},
      step choice₁ choice₂ ->
        logVolume choice₁ = logVolume choice₂

namespace IUTStage1Theorem311Ind1Action

variable {choice : Type u}

theorem logVolume_eq
    (action : IUTStage1Theorem311Ind1Action choice)
    {choice₁ choice₂ : choice}
    (hstep : action.step choice₁ choice₂) :
    action.logVolume choice₁ = action.logVolume choice₂ :=
  action.preserves_processionNormalizedLogVolume hstep

end IUTStage1Theorem311Ind1Action

/--
Typed `(Ind2)` action on a Theorem 3.11 choice space.

The action records the local tensor/aut-Frobenioid ambiguity and the invariant
required in the proof of Corollary 3.12: procession-normalized log-volume is
unchanged along `(Ind2)`.
-/
structure IUTStage1Theorem311Ind2Action (choice : Type u) where
  step : choice -> choice -> Prop
  logVolume : choice -> Real
  preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂ : choice},
      step choice₁ choice₂ ->
        logVolume choice₁ = logVolume choice₂

namespace IUTStage1Theorem311Ind2Action

variable {choice : Type u}

theorem logVolume_eq
    (action : IUTStage1Theorem311Ind2Action choice)
    {choice₁ choice₂ : choice}
    (hstep : action.step choice₁ choice₂) :
    action.logVolume choice₁ = action.logVolume choice₂ :=
  action.preserves_processionNormalizedLogVolume hstep

end IUTStage1Theorem311Ind2Action

/--
Typed `(Ind3)` upper-semi relation on a Theorem 3.11 choice space.

Unlike `(Ind1)` and `(Ind2)`, `(Ind3)` is deliberately one-sided.  A step may
move to a different representative, but the only log-volume assertion on the
critical path is the source-paper upper-semi inequality.
-/
structure IUTStage1Theorem311Ind3UpperSemiRelation (choice : Type u) where
  step : choice -> choice -> Prop
  logVolume : choice -> Real
  upper_semi_logVolume :
    ∀ {choice₁ choice₂ : choice},
      step choice₁ choice₂ ->
        logVolume choice₁ <= logVolume choice₂

namespace IUTStage1Theorem311Ind3UpperSemiRelation

variable {choice : Type u}

theorem logVolume_le
    (relation : IUTStage1Theorem311Ind3UpperSemiRelation choice)
    {choice₁ choice₂ : choice}
    (hstep : relation.step choice₁ choice₂) :
    relation.logVolume choice₁ <= relation.logVolume choice₂ :=
  relation.upper_semi_logVolume hstep

end IUTStage1Theorem311Ind3UpperSemiRelation

/--
The typed indeterminacy core used by the local-to-global `C_\Theta` milestone.

It bundles the three source-paper indeterminacies around a common
procession-normalized log-volume.  The compatibility fields assert that the
three action records are measuring the same log-volume function, so downstream
audits can state the exact equality/equality/inequality pattern:
`(Ind1)` preserves, `(Ind2)` preserves, `(Ind3)` upper-bounds.
-/
structure IUTStage1Theorem311TypedIndeterminacyCore (choice : Type u) where
  logVolume : choice -> Real
  ind1 : IUTStage1Theorem311Ind1Action choice
  ind2 : IUTStage1Theorem311Ind2Action choice
  ind3 : IUTStage1Theorem311Ind3UpperSemiRelation choice
  ind1_logVolume_eq : ind1.logVolume = logVolume
  ind2_logVolume_eq : ind2.logVolume = logVolume
  ind3_logVolume_eq : ind3.logVolume = logVolume

namespace IUTStage1Theorem311TypedIndeterminacyCore

variable {choice : Type u}

def generators (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    IUTStage1IndeterminacyGenerators choice :=
  { ind1_step := core.ind1.step,
    ind2_step := core.ind2.step,
    ind3_step := core.ind3.step }

def quotient (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    IUTStage1IndeterminacyQuotient choice :=
  IUTStage1IndeterminacyQuotient.generated core.generators

def quotientMap (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    choice -> Quot core.quotient.relation :=
  Quot.mk core.quotient.relation

/--
Equality-type quotient generated only by `(Ind1)` and `(Ind2)`.

This is the quotient appropriate for possible-image equality.  The `(Ind3)`
upper-semi relation is deliberately replaced by `False`, since the source
theorem only gives a one-sided log-volume inequality for `(Ind3)` on the
critical Corollary 3.12 corridor.
-/
def equalityGenerators
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    IUTStage1IndeterminacyGenerators choice :=
  { ind1_step := core.ind1.step,
    ind2_step := core.ind2.step,
    ind3_step := fun _ _ => False }

def equalityQuotient
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    IUTStage1IndeterminacyQuotient choice :=
  IUTStage1IndeterminacyQuotient.generated core.equalityGenerators

def equalityQuotientMap
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    choice -> Quot core.equalityQuotient.relation :=
  Quot.mk core.equalityQuotient.relation

theorem ind1_preserves_logVolume
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    core.logVolume choice₁ = core.logVolume choice₂ := by
  rw [← core.ind1_logVolume_eq]
  exact core.ind1.logVolume_eq hstep

theorem ind2_preserves_logVolume
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    core.logVolume choice₁ = core.logVolume choice₂ := by
  rw [← core.ind2_logVolume_eq]
  exact core.ind2.logVolume_eq hstep

theorem ind3_logVolume_le
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ := by
  rw [← core.ind3_logVolume_eq]
  exact core.ind3.logVolume_le hstep

theorem ind1_equalityQuotientMap_eq
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    core.equalityQuotientMap choice₁ =
      core.equalityQuotientMap choice₂ :=
  Quot.sound (IUTStage1GeneratedIndeterminacyRelation.ind1 hstep)

theorem ind2_equalityQuotientMap_eq
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    core.equalityQuotientMap choice₁ =
      core.equalityQuotientMap choice₂ :=
  Quot.sound (IUTStage1GeneratedIndeterminacyRelation.ind2 hstep)

/-- Equality orbit generated by the `(Ind1)` and `(Ind2)` part of the typed core. -/
def equalityOrbit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (choice₀ : choice) : Set choice :=
  { choice | core.equalityQuotient.relation choice₀ choice }

theorem mem_equalityOrbit_self
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (choice₀ : choice) :
    choice₀ ∈ core.equalityOrbit choice₀ :=
  IUTStage1GeneratedIndeterminacyRelation.refl choice₀

theorem ind1_mem_equalityOrbit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    choice₂ ∈ core.equalityOrbit choice₁ :=
  IUTStage1GeneratedIndeterminacyRelation.ind1 hstep

theorem ind2_mem_equalityOrbit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    choice₂ ∈ core.equalityOrbit choice₁ :=
  IUTStage1GeneratedIndeterminacyRelation.ind2 hstep

theorem equalityGenerators_ind3_false
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice} :
    core.equalityGenerators.ind3_step choice₁ choice₂ -> False :=
  id

/--
Step-level certificate for the one-sided `(Ind3)` contribution.

It keeps the actual source and target log-volume coordinates of the typed core,
the upper-semi inequality, and the fact that this arrow is not available as an
equality-quotient generator.  This is the local object used when the Corollary
3.12 corridor must distinguish upper-semi transport from equality transport.
-/
structure Ind3UpperSemiStepAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (choice₁ choice₂ : choice) : Prop where
  ind3_step : core.ind3.step choice₁ choice₂
  source_logVolume_eq_relation_logVolume :
    core.logVolume choice₁ = core.ind3.logVolume choice₁
  target_logVolume_eq_relation_logVolume :
    core.logVolume choice₂ = core.ind3.logVolume choice₂
  upper_semi_logVolume :
    core.logVolume choice₁ <= core.logVolume choice₂
  excluded_from_equality_quotient :
    core.equalityGenerators.ind3_step choice₁ choice₂ -> False

theorem ind3UpperSemiStepAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    Ind3UpperSemiStepAudit core choice₁ choice₂ :=
  { ind3_step := hstep,
    source_logVolume_eq_relation_logVolume := by
      rw [core.ind3_logVolume_eq],
    target_logVolume_eq_relation_logVolume := by
      rw [core.ind3_logVolume_eq],
    upper_semi_logVolume := core.ind3_logVolume_le hstep,
    excluded_from_equality_quotient := by
      intro hfalse
      exact core.equalityGenerators_ind3_false hfalse }

/--
Relation-level audit for the typed `(Ind3)` upper-semi law.

The audit is intentionally asymmetric: it certifies all real `(Ind3)` steps as
one-sided log-volume transports, and separately certifies that the equality
quotient has no `(Ind3)` generator.
-/
structure Ind3UpperSemiRelationAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) : Prop where
  relation_logVolume_eq_core :
    core.ind3.logVolume = core.logVolume
  upper_semi_step_audit :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        Ind3UpperSemiStepAudit core choice₁ choice₂
  equalityQuotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : choice},
      core.equalityGenerators.ind3_step choice₁ choice₂ -> False

theorem ind3UpperSemiRelationAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    Ind3UpperSemiRelationAudit core :=
  { relation_logVolume_eq_core := core.ind3_logVolume_eq,
    upper_semi_step_audit := by
      intro choice₁ choice₂ hstep
      exact core.ind3UpperSemiStepAudit hstep,
    equalityQuotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact core.equalityGenerators_ind3_false hstep }

/--
Named action-law audit for the typed Theorem 3.11 indeterminacy core.

This is the compact kernel-facing certificate that the critical corridor is using
the source-paper equality/equality/upper-semi pattern: `(Ind1)` and `(Ind2)`
preserve the procession-normalized log-volume and generate the equality quotient,
while `(Ind3)` is excluded from that quotient and contributes only a one-sided
upper-semi log-volume inequality.
-/
structure ActionLawAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) : Prop where
  ind1_logVolume_eq_core :
    core.ind1.logVolume = core.logVolume
  ind2_logVolume_eq_core :
    core.ind2.logVolume = core.logVolume
  ind3_logVolume_eq_core :
    core.ind3.logVolume = core.logVolume
  ind1_preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        core.logVolume choice₁ = core.logVolume choice₂
  ind2_preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        core.logVolume choice₁ = core.logVolume choice₂
  ind3_upper_semi_logVolume :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂
  ind3_upper_semi_relation_audit :
    Ind3UpperSemiRelationAudit core
  ind1_equalityQuotientMap_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        core.equalityQuotientMap choice₁ =
          core.equalityQuotientMap choice₂
  ind2_equalityQuotientMap_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        core.equalityQuotientMap choice₁ =
          core.equalityQuotientMap choice₂
  equalityQuotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : choice},
      core.equalityGenerators.ind3_step choice₁ choice₂ -> False

theorem actionLawAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    ActionLawAudit core :=
  { ind1_logVolume_eq_core := core.ind1_logVolume_eq,
    ind2_logVolume_eq_core := core.ind2_logVolume_eq,
    ind3_logVolume_eq_core := core.ind3_logVolume_eq,
    ind1_preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact core.ind1_preserves_logVolume hstep,
    ind2_preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact core.ind2_preserves_logVolume hstep,
    ind3_upper_semi_logVolume := by
      intro choice₁ choice₂ hstep
      exact core.ind3_logVolume_le hstep,
    ind3_upper_semi_relation_audit :=
      core.ind3UpperSemiRelationAudit,
    ind1_equalityQuotientMap_eq := by
      intro choice₁ choice₂ hstep
      exact core.ind1_equalityQuotientMap_eq hstep,
    ind2_equalityQuotientMap_eq := by
      intro choice₁ choice₂ hstep
      exact core.ind2_equalityQuotientMap_eq hstep,
    equalityQuotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact core.equalityGenerators_ind3_false hstep }

/--
Compatibility between typed indeterminacies and a possible-image family.

This keeps the quotient-map construction honest: `(Ind1)` and `(Ind2)` identify
possible-image regions, while `(Ind3)` only supplies the log-volume inequality
needed by the Step (x) corridor.
-/
structure PossibleImageQuotientCompatibility
    {target : Copy}
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (images : RegionFamily target choice) : Prop where
  ind1_region_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂
  ind3_logVolume_upper :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂

namespace PossibleImageQuotientCompatibility

variable {target : Copy}
variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}
variable {images : RegionFamily target choice}

theorem ind3_upper_from_core
    (compatibility : PossibleImageQuotientCompatibility core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  compatibility.ind3_logVolume_upper hstep

theorem ind1_quotientMap_eq
    (_compatibility : PossibleImageQuotientCompatibility core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    core.quotientMap choice₁ = core.quotientMap choice₂ :=
  Quot.sound (IUTStage1GeneratedIndeterminacyRelation.ind1 hstep)

theorem ind2_quotientMap_eq
    (_compatibility : PossibleImageQuotientCompatibility core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    core.quotientMap choice₁ = core.quotientMap choice₂ :=
  Quot.sound (IUTStage1GeneratedIndeterminacyRelation.ind2 hstep)

theorem equalityQuotient_image_invariant
    (compatibility : PossibleImageQuotientCompatibility core images) :
    ∀ {choice₁ choice₂ : choice},
      core.equalityQuotient.relation choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ :=
  IUTStage1GeneratedIndeterminacyRelation.image_invariant
    images
    compatibility.ind1_region_eq
    compatibility.ind2_region_eq
    (by intro choice₁ choice₂ hfalse; cases hfalse)

theorem ind1_equalityQuotientMap_eq
    (_compatibility : PossibleImageQuotientCompatibility core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    core.equalityQuotientMap choice₁ =
      core.equalityQuotientMap choice₂ :=
  core.ind1_equalityQuotientMap_eq hstep

theorem ind2_equalityQuotientMap_eq
    (_compatibility : PossibleImageQuotientCompatibility core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    core.equalityQuotientMap choice₁ =
      core.equalityQuotientMap choice₂ :=
  core.ind2_equalityQuotientMap_eq hstep

end PossibleImageQuotientCompatibility

/--
Possible-image family indexed by the equality quotient of the typed core.

This is the explicit quotient/factorization object for the Corollary 3.12
corridor: the choice-indexed possible-image family is recovered by pulling back
along `equalityQuotientMap`.  Since this quotient is generated only by `(Ind1)`
and `(Ind2)`, the `(Ind3)` data remains one-sided log-volume data rather than a
possible-image identification.
-/
structure EqualityQuotientPossibleImages
    {target : Copy}
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (images : RegionFamily target choice) where
  quotientImages : RegionFamily target (Quot core.equalityQuotient.relation)
  pullback_region_eq :
    ∀ choice₀ : choice,
      quotientImages.region (core.equalityQuotientMap choice₀) =
        images.region choice₀

namespace EqualityQuotientPossibleImages

variable {target : Copy}
variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}
variable {images : RegionFamily target choice}

def ofCompatibility
    (compatibility : PossibleImageQuotientCompatibility core images) :
    EqualityQuotientPossibleImages core images :=
  { quotientImages :=
      { region :=
          Quot.lift
            (fun choice₀ => images.region choice₀)
            (by
              intro choice₁ choice₂ hrel
              exact compatibility.equalityQuotient_image_invariant hrel) },
    pullback_region_eq := by
      intro choice₀
      rfl }

theorem region_eq_of_equalityOrbit
    (quotientImages : EqualityQuotientPossibleImages core images)
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    images.region choice₁ = images.region choice₂ := by
  calc
    images.region choice₁ =
        quotientImages.quotientImages.region (core.equalityQuotientMap choice₁) := by
          rw [quotientImages.pullback_region_eq]
    _ = quotientImages.quotientImages.region (core.equalityQuotientMap choice₂) := by
          rw [show core.equalityQuotientMap choice₁ =
              core.equalityQuotientMap choice₂ from Quot.sound hmem]
    _ = images.region choice₂ := by
          rw [quotientImages.pullback_region_eq]

theorem ind1_region_eq
    (quotientImages : EqualityQuotientPossibleImages core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    images.region choice₁ = images.region choice₂ :=
  quotientImages.region_eq_of_equalityOrbit (core.ind1_mem_equalityOrbit hstep)

theorem ind2_region_eq
    (quotientImages : EqualityQuotientPossibleImages core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    images.region choice₁ = images.region choice₂ :=
  quotientImages.region_eq_of_equalityOrbit (core.ind2_mem_equalityOrbit hstep)

theorem ind3_logVolume_le
    (_quotientImages : EqualityQuotientPossibleImages core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  core.ind3_logVolume_le hstep

/--
Quotient-indexed Remark 3.9.5 possible-image family attached to the typed
Theorem 3.11 equality quotient.

The index is `Quot core.equalityQuotient.relation`, not the original choice
space.  Thus `(Ind1)` and `(Ind2)` have already been collapsed at the source
of the hull construction, while `(Ind3)` remains outside this equality quotient
and contributes only the upper-semi log-volume theorem above.
-/
def toRemark395PossibleImageFamilySource
    (quotientImages : EqualityQuotientPossibleImages core images)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    IUTStage1Remark395PossibleImageFamilySource
      (Point target) (Quot core.equalityQuotient.relation) :=
  { hullOperator := hullOperator,
    possibleRegion := fun quotientChoice =>
      (quotientImages.quotientImages.region quotientChoice).toSet }

theorem remark395PossibleRegion_pullback_eq
    (quotientImages : EqualityQuotientPossibleImages core images)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    (choice₀ : choice) :
    (quotientImages.toRemark395PossibleImageFamilySource hullOperator).possibleRegion
        (core.equalityQuotientMap choice₀) =
      (images.region choice₀).toSet := by
  exact congrArg Region.toSet (quotientImages.pullback_region_eq choice₀)

set_option linter.style.longLine false in
/--
Typed equality quotient to Remark 3.9.5 Ob5 endpoint.

For choices in the `(Ind1)/(Ind2)` equality orbit, the quotient-indexed
Remark 3.9.5 possible-image regions are equal and both are contained in the
canonical family hull.  This is the hull-side counterpart of
`region_eq_of_equalityOrbit`, with `(Ind3)` still excluded from the equality
quotient.
-/
theorem remark395Ob5EqualityQuotientEndpoint_of_equalityOrbit
    (quotientImages : EqualityQuotientPossibleImages core images)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    let familySource :=
      quotientImages.toRemark395PossibleImageFamilySource hullOperator;
    familySource.possibleRegion (core.equalityQuotientMap choice₁) =
        familySource.possibleRegion (core.equalityQuotientMap choice₂) ∧
      familySource.familyUnion ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion (core.equalityQuotientMap choice₁) ⊆
        familySource.canonicalHull ∧
      familySource.possibleRegion (core.equalityQuotientMap choice₂) ⊆
        familySource.canonicalHull ∧
      familySource.canonicalPhi.approximant = familySource.canonicalHull ∧
      familySource.hullOperator.isClosed familySource.canonicalHull :=
  by
    intro familySource
    have hquot :
        core.equalityQuotientMap choice₁ =
          core.equalityQuotientMap choice₂ :=
      Quot.sound hmem
    exact
      ⟨congrArg familySource.possibleRegion hquot,
        familySource.familyUnion_subset_phi,
        familySource.possibleRegion_subset_phi (core.equalityQuotientMap choice₁),
        familySource.possibleRegion_subset_phi (core.equalityQuotientMap choice₂),
        familySource.canonicalPhi_approximant_eq_phi,
        familySource.phi_closed⟩

set_option linter.style.longLine false in
/--
Typed equality quotient through Remark 3.9.5 Ob5--Ob6.

This extends the Ob5 collapse by adding the `Phi`/`Xi` hull-approximant
log-volume inequalities used on the Step (xi) side of the Corollary 3.12
corridor.
-/
theorem remark395Ob5Ob6EqualityQuotientEndpoint_of_equalityOrbit
    {κ : Type w}
    (quotientImages : EqualityQuotientPossibleImages core images)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    (phiFamily :
      (quotientImages.toRemark395PossibleImageFamilySource hullOperator).PhiFamily κ)
    (xiFamily :
      (quotientImages.toRemark395PossibleImageFamilySource hullOperator).XiFamily κ)
    (k : κ)
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    let familySource :=
      quotientImages.toRemark395PossibleImageFamilySource hullOperator;
    familySource.possibleRegion (core.equalityQuotientMap choice₁) =
        familySource.possibleRegion (core.equalityQuotientMap choice₂) ∧
      familySource.familyUnion ⊆ familySource.canonicalHull ∧
      familySource.possibleRegion (core.equalityQuotientMap choice₁) ⊆
        familySource.canonicalHull ∧
      familySource.possibleRegion (core.equalityQuotientMap choice₂) ⊆
        familySource.canonicalHull ∧
      familySource.HPhi phiFamily = familySource.canonicalHull ∧
      familySource.hullOperator.logVolume familySource.familyUnion <=
        familySource.hullOperator.logVolume (familySource.HPhi phiFamily) ∧
      familySource.hullOperator.logVolume
          (familySource.possibleRegion (core.equalityQuotientMap choice₁)) <=
        familySource.hullOperator.logVolume (familySource.HPhi phiFamily) ∧
      familySource.HXi xiFamily = familySource.canonicalHull ∧
      familySource.hullOperator.logVolume familySource.familyUnion <=
        familySource.hullOperator.logVolume (familySource.HXi xiFamily) ∧
      familySource.hullOperator.logVolume
          (familySource.possibleRegion (core.equalityQuotientMap choice₁)) <=
        familySource.hullOperator.logVolume (familySource.HXi xiFamily) ∧
      familySource.hullOperator.logVolume
          ((xiFamily.exactApproximant k).approximant).approximant =
        familySource.hullOperator.logVolume familySource.familyUnion :=
  by
    intro familySource
    have hob5 :=
      quotientImages.remark395Ob5EqualityQuotientEndpoint_of_equalityOrbit
        hullOperator hmem
    rcases hob5 with
      ⟨hregion, hfamily_subset, hchoice₁_subset, hchoice₂_subset,
        _hcanonicalPhi, _hphi_closed⟩
    have hob6 :=
      familySource.PhiXi_ob6_logVolume_endpoint
        phiFamily xiFamily k (core.equalityQuotientMap choice₁)
    rcases hob6 with
      ⟨hHPhi_eq, _hHPhi_subset, _hphi_subset_HPhi, hfamily_le_HPhi,
        _hHPhi_log, hchoice₁_le_HPhi, hHXi_eq, _hHXi_subset,
        _hphi_subset_HXi, hfamily_le_HXi, _hHXi_log, hchoice₁_le_HXi,
        hxi_exact_log⟩
    exact
      ⟨hregion,
        hfamily_subset,
        hchoice₁_subset,
        hchoice₂_subset,
        hHPhi_eq,
        hfamily_le_HPhi,
        hchoice₁_le_HPhi,
        hHXi_eq,
        hfamily_le_HXi,
        hchoice₁_le_HXi,
        hxi_exact_log⟩

end EqualityQuotientPossibleImages

set_option linter.style.longLine false in
/--
Hull/log-volume compatibility for possible images factored through the typed
Theorem 3.11 equality quotient.

This is the first-class version of the quotient-to-Remark 3.9.5 bridge used by
the Step (xi) corridor.  The possible-image family is indexed by the
`(Ind1)/(Ind2)` equality quotient; pullback recovers the original choice-indexed
family; and the hull/log-volume maps are applied only after this quotient
factorization.  The `(Ind3)` component is retained separately as the
upper-semi log-volume relation of the typed core.
-/
structure EqualityQuotientHullLogVolumeCompatibility
    {target : Copy}
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (images : RegionFamily target choice)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) where
  quotientImages : EqualityQuotientPossibleImages core images

namespace EqualityQuotientHullLogVolumeCompatibility

variable {target : Copy}
variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}
variable {images : RegionFamily target choice}
variable {hullOperator :
  IUTStage1Remark395HolomorphicHullOperator (Point target)}

def ofCompatibility
    (compatibility :
      IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
        core images)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    EqualityQuotientHullLogVolumeCompatibility core images hullOperator :=
  { quotientImages :=
      IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages.ofCompatibility
        compatibility }

def familySource
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator) :
    IUTStage1Remark395PossibleImageFamilySource
      (Point target) (Quot core.equalityQuotient.relation) :=
  compatibility.quotientImages.toRemark395PossibleImageFamilySource hullOperator

theorem possibleRegion_pullback_eq
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    (choice₀ : choice) :
    compatibility.familySource.possibleRegion
        (core.equalityQuotientMap choice₀) =
      (images.region choice₀).toSet :=
  compatibility.quotientImages.remark395PossibleRegion_pullback_eq
    hullOperator choice₀

theorem possibleRegion_eq_of_equalityOrbit
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    compatibility.familySource.possibleRegion
        (core.equalityQuotientMap choice₁) =
      compatibility.familySource.possibleRegion
        (core.equalityQuotientMap choice₂) := by
  have hquot :
      core.equalityQuotientMap choice₁ =
        core.equalityQuotientMap choice₂ :=
    Quot.sound hmem
  exact congrArg compatibility.familySource.possibleRegion hquot

theorem logVolume_eq_of_equalityOrbit
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₁)) =
      hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₂)) := by
  exact congrArg hullOperator.logVolume
    (compatibility.possibleRegion_eq_of_equalityOrbit hmem)

theorem ind1_logVolume_eq
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₁)) =
      hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₂)) :=
  compatibility.logVolume_eq_of_equalityOrbit
    (core.ind1_mem_equalityOrbit hstep)

theorem ind2_logVolume_eq
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₁)) =
      hullOperator.logVolume
        (compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₂)) :=
  compatibility.logVolume_eq_of_equalityOrbit
    (core.ind2_mem_equalityOrbit hstep)

theorem ind3_upper_semi_logVolume
    (_compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  core.ind3_logVolume_le hstep

set_option linter.style.longLine false in
theorem hull_endpoint_of_equalityOrbit
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator)
    {choice₁ choice₂ : choice}
    (hmem : choice₂ ∈ core.equalityOrbit choice₁) :
    compatibility.familySource.possibleRegion
        (core.equalityQuotientMap choice₁) =
        compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₂) ∧
      compatibility.familySource.familyUnion ⊆
        compatibility.familySource.canonicalHull ∧
      compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₁) ⊆
        compatibility.familySource.canonicalHull ∧
      compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₂) ⊆
        compatibility.familySource.canonicalHull ∧
      hullOperator.logVolume
          (compatibility.familySource.possibleRegion
            (core.equalityQuotientMap choice₁)) =
        hullOperator.logVolume
          (compatibility.familySource.possibleRegion
            (core.equalityQuotientMap choice₂)) :=
  ⟨compatibility.possibleRegion_eq_of_equalityOrbit hmem,
    compatibility.familySource.familyUnion_subset_phi,
    compatibility.familySource.possibleRegion_subset_phi
      (core.equalityQuotientMap choice₁),
    compatibility.familySource.possibleRegion_subset_phi
      (core.equalityQuotientMap choice₂),
    compatibility.logVolume_eq_of_equalityOrbit hmem⟩

set_option linter.style.longLine false in
theorem endpoint
    (compatibility :
      EqualityQuotientHullLogVolumeCompatibility core images hullOperator) :
    (∀ choice₀,
      compatibility.familySource.possibleRegion
          (core.equalityQuotientMap choice₀) =
        (images.region choice₀).toSet) ∧
      (∀ {choice₁ choice₂ : choice},
        choice₂ ∈ core.equalityOrbit choice₁ ->
          compatibility.familySource.possibleRegion
              (core.equalityQuotientMap choice₁) =
            compatibility.familySource.possibleRegion
              (core.equalityQuotientMap choice₂)) ∧
      (∀ {choice₁ choice₂ : choice},
        choice₂ ∈ core.equalityOrbit choice₁ ->
          hullOperator.logVolume
              (compatibility.familySource.possibleRegion
                (core.equalityQuotientMap choice₁)) =
            hullOperator.logVolume
              (compatibility.familySource.possibleRegion
                (core.equalityQuotientMap choice₂))) ∧
      (∀ {choice₁ choice₂ : choice},
        core.ind3.step choice₁ choice₂ ->
          core.logVolume choice₁ <= core.logVolume choice₂) ∧
      compatibility.familySource.familyUnion ⊆
        compatibility.familySource.canonicalHull :=
  ⟨compatibility.possibleRegion_pullback_eq,
    fun hmem => compatibility.possibleRegion_eq_of_equalityOrbit hmem,
    fun hmem => compatibility.logVolume_eq_of_equalityOrbit hmem,
    fun hstep => compatibility.ind3_upper_semi_logVolume hstep,
    compatibility.familySource.familyUnion_subset_phi⟩

end EqualityQuotientHullLogVolumeCompatibility

/--
Finite nonvacuity witness for the typed indeterminacy core.

The choice type is `Fin 1`; all three indeterminacy relations are equality and
the procession-normalized log-volume is constantly `0`.  This is not intended
as an IUT model, but it verifies that the typed action/quotient interface is
jointly satisfiable.
-/
def finiteToyCore : IUTStage1Theorem311TypedIndeterminacyCore (Fin 1) :=
  { logVolume := fun _ => 0,
    ind1 :=
      { step := Eq,
        logVolume := fun _ => 0,
        preserves_processionNormalizedLogVolume := by
          intro choice₁ choice₂ hstep
          subst hstep
          rfl },
    ind2 :=
      { step := Eq,
        logVolume := fun _ => 0,
        preserves_processionNormalizedLogVolume := by
          intro choice₁ choice₂ hstep
          subst hstep
          rfl },
    ind3 :=
      { step := Eq,
        logVolume := fun _ => 0,
        upper_semi_logVolume := by
          intro choice₁ choice₂ hstep
          subst hstep
          exact le_rfl },
    ind1_logVolume_eq := rfl,
    ind2_logVolume_eq := rfl,
    ind3_logVolume_eq := rfl }

theorem finiteToyCore_ind3_upper
    {choice₁ choice₂ : Fin 1}
    (hstep : finiteToyCore.ind3.step choice₁ choice₂) :
    finiteToyCore.logVolume choice₁ <= finiteToyCore.logVolume choice₂ :=
  finiteToyCore.ind3_logVolume_le hstep

def finiteToyPossibleImageFamily (target : Copy) : RegionFamily target (Fin 1) :=
  { region := fun _ => Region.upperRay target 0 }

def finiteToyPossibleImageCompatibility
    (target : Copy) :
    PossibleImageQuotientCompatibility finiteToyCore
      (finiteToyPossibleImageFamily target) where
  ind1_region_eq := by
    intro choice₁ choice₂ hstep
    subst hstep
    rfl
  ind2_region_eq := by
    intro choice₁ choice₂ hstep
    subst hstep
    rfl
  ind3_logVolume_upper := by
    intro choice₁ choice₂ hstep
    exact finiteToyCore.ind3_logVolume_le hstep

def finiteToyEqualityQuotientPossibleImages
    (target : Copy) :
    EqualityQuotientPossibleImages finiteToyCore
      (finiteToyPossibleImageFamily target) :=
  EqualityQuotientPossibleImages.ofCompatibility
    (finiteToyPossibleImageCompatibility target)

theorem finiteToyEqualityQuotientPossibleImages_pullback
    (target : Copy) (choice₀ : Fin 1) :
    (finiteToyEqualityQuotientPossibleImages target).quotientImages.region
        (finiteToyCore.equalityQuotientMap choice₀) =
      (finiteToyPossibleImageFamily target).region choice₀ :=
  (finiteToyEqualityQuotientPossibleImages target).pullback_region_eq choice₀

/--
Focused nonvacuity audit for the typed `(Ind1)/(Ind2)/(Ind3)` interface.

The witness is intentionally tiny: the choice space is `Fin 1`, all three
relations are equality, and the procession-normalized log-volume is constantly
zero.  The audit still checks the critical shape required by the Corollary 3.12
corridor: `(Ind1)` and `(Ind2)` preserve log-volume, `(Ind3)` only supplies an
upper-semi inequality, the equality quotient has no `(Ind3)` generator, and the
quotient-indexed possible-image family pulls back to the original family.
-/
structure FiniteToyTypedIndeterminacyNonvacuityAudit (target : Copy) where
  choice_nonempty : Nonempty (Fin 1)
  ind1_step_self :
    finiteToyCore.ind1.step (0 : Fin 1) (0 : Fin 1)
  ind2_step_self :
    finiteToyCore.ind2.step (0 : Fin 1) (0 : Fin 1)
  ind3_step_self :
    finiteToyCore.ind3.step (0 : Fin 1) (0 : Fin 1)
  ind1_preserves_every_step :
    ∀ {choice₁ choice₂ : Fin 1},
      finiteToyCore.ind1.step choice₁ choice₂ ->
        finiteToyCore.logVolume choice₁ = finiteToyCore.logVolume choice₂
  ind2_preserves_every_step :
    ∀ {choice₁ choice₂ : Fin 1},
      finiteToyCore.ind2.step choice₁ choice₂ ->
        finiteToyCore.logVolume choice₁ = finiteToyCore.logVolume choice₂
  ind3_upper_every_step :
    ∀ {choice₁ choice₂ : Fin 1},
      finiteToyCore.ind3.step choice₁ choice₂ ->
        finiteToyCore.logVolume choice₁ <= finiteToyCore.logVolume choice₂
  equalityQuotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : Fin 1},
      finiteToyCore.equalityGenerators.ind3_step choice₁ choice₂ -> False
  possible_image_compatibility :
    PossibleImageQuotientCompatibility finiteToyCore
      (finiteToyPossibleImageFamily target)
  equality_quotient_images :
    EqualityQuotientPossibleImages finiteToyCore
      (finiteToyPossibleImageFamily target)
  equality_quotient_pullback :
    ∀ choice₀ : Fin 1,
      (finiteToyEqualityQuotientPossibleImages target).quotientImages.region
          (finiteToyCore.equalityQuotientMap choice₀) =
        (finiteToyPossibleImageFamily target).region choice₀

def finiteToyTypedIndeterminacyNonvacuityAudit
    (target : Copy) :
    FiniteToyTypedIndeterminacyNonvacuityAudit target :=
  { choice_nonempty := ⟨0⟩,
    ind1_step_self := rfl,
    ind2_step_self := rfl,
    ind3_step_self := rfl,
    ind1_preserves_every_step := by
      intro choice₁ choice₂ hstep
      exact finiteToyCore.ind1_preserves_logVolume hstep,
    ind2_preserves_every_step := by
      intro choice₁ choice₂ hstep
      exact finiteToyCore.ind2_preserves_logVolume hstep,
    ind3_upper_every_step := by
      intro choice₁ choice₂ hstep
      exact finiteToyCore.ind3_logVolume_le hstep,
    equalityQuotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact finiteToyCore.equalityGenerators_ind3_false hstep,
    possible_image_compatibility := finiteToyPossibleImageCompatibility target,
    equality_quotient_images := finiteToyEqualityQuotientPossibleImages target,
    equality_quotient_pullback :=
      finiteToyEqualityQuotientPossibleImages_pullback target }

theorem finiteToyTypedIndeterminacyNonvacuityAudit_ind3_is_one_sided
    (target : Copy) :
    finiteToyCore.logVolume (0 : Fin 1) <=
        finiteToyCore.logVolume (0 : Fin 1) ∧
      (∀ {choice₁ choice₂ : Fin 1},
        finiteToyCore.equalityGenerators.ind3_step choice₁ choice₂ -> False) :=
  ⟨(finiteToyTypedIndeterminacyNonvacuityAudit target).ind3_upper_every_step
      (finiteToyTypedIndeterminacyNonvacuityAudit target).ind3_step_self,
    (finiteToyTypedIndeterminacyNonvacuityAudit target).equalityQuotient_no_ind3_generator⟩

/--
Two-point nonvacuity witness for a genuinely one-sided `(Ind3)` step.

The `(Ind1)` and `(Ind2)` relations are equality, while `(Ind3)` permits the
strict step `0 -> 1`.  The procession-normalized log-volume is `0` at `0` and
`1` at `1`, so the `(Ind3)` assertion is a strict upper-semi inequality, not a
hidden equality.
-/
def strictFiniteToyLogVolume : Fin 2 -> Real :=
  fun choice => choice.val

def strictFiniteToyInd3Step (choice₁ choice₂ : Fin 2) : Prop :=
  choice₁ = choice₂ ∨
    (choice₁ = (0 : Fin 2) ∧ choice₂ = (1 : Fin 2))

def strictFiniteToyCore : IUTStage1Theorem311TypedIndeterminacyCore (Fin 2) :=
  { logVolume := strictFiniteToyLogVolume,
    ind1 :=
      { step := Eq,
        logVolume := strictFiniteToyLogVolume,
        preserves_processionNormalizedLogVolume := by
          intro choice₁ choice₂ hstep
          subst hstep
          rfl },
    ind2 :=
      { step := Eq,
        logVolume := strictFiniteToyLogVolume,
        preserves_processionNormalizedLogVolume := by
          intro choice₁ choice₂ hstep
          subst hstep
          rfl },
    ind3 :=
      { step := strictFiniteToyInd3Step,
        logVolume := strictFiniteToyLogVolume,
        upper_semi_logVolume := by
          intro choice₁ choice₂ hstep
          rcases hstep with hEq | hStrict
          · subst hEq
            exact le_rfl
          · rcases hStrict with ⟨hzero, hone⟩
            subst hzero
            subst hone
            norm_num [strictFiniteToyLogVolume] },
    ind1_logVolume_eq := rfl,
    ind2_logVolume_eq := rfl,
    ind3_logVolume_eq := rfl }

def strictFiniteToyPossibleImageFamily
    (target : Copy) : RegionFamily target (Fin 2) :=
  { region := fun choice => Region.upperRay target choice.val }

def strictFiniteToyPossibleImageCompatibility
    (target : Copy) :
    PossibleImageQuotientCompatibility strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target) where
  ind1_region_eq := by
    intro choice₁ choice₂ hstep
    subst hstep
    rfl
  ind2_region_eq := by
    intro choice₁ choice₂ hstep
    subst hstep
    rfl
  ind3_logVolume_upper := by
    intro choice₁ choice₂ hstep
    exact strictFiniteToyCore.ind3_logVolume_le hstep

def strictFiniteToyEqualityQuotientPossibleImages
    (target : Copy) :
    EqualityQuotientPossibleImages strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target) :=
  EqualityQuotientPossibleImages.ofCompatibility
    (strictFiniteToyPossibleImageCompatibility target)

def strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
    (target : Copy)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    EqualityQuotientHullLogVolumeCompatibility strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target) hullOperator :=
  EqualityQuotientHullLogVolumeCompatibility.ofCompatibility
    (strictFiniteToyPossibleImageCompatibility target) hullOperator

set_option linter.style.longLine false in
theorem strictFiniteToyEqualityQuotientHullLogVolumeCompatibility_endpoint
    (target : Copy)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    (∀ choice₀,
      (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
          target hullOperator).familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap choice₀) =
        ((strictFiniteToyPossibleImageFamily target).region choice₀).toSet) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        choice₂ ∈ strictFiniteToyCore.equalityOrbit choice₁ ->
          (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
              target hullOperator).familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₁) =
            (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
              target hullOperator).familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₂)) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        choice₂ ∈ strictFiniteToyCore.equalityOrbit choice₁ ->
          hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
                target hullOperator).familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₁)) =
            hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
                target hullOperator).familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₂))) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        strictFiniteToyCore.ind3.step choice₁ choice₂ ->
          strictFiniteToyCore.logVolume choice₁ <=
            strictFiniteToyCore.logVolume choice₂) ∧
      (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
        target hullOperator).familySource.familyUnion ⊆
        (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
          target hullOperator).familySource.canonicalHull :=
  (strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
    target hullOperator).endpoint

theorem strictFiniteToyEqualityQuotient_relation_eq
    {choice₁ choice₂ : Fin 2}
    (hrel : strictFiniteToyCore.equalityQuotient.relation choice₁ choice₂) :
    choice₁ = choice₂ := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact hstep
  | ind2 hstep =>
      exact hstep
  | ind3 hstep =>
      exact False.elim hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁₂ ih₂₃ =>
      exact ih₁₂.trans ih₂₃

def strictFiniteToyEqualityQuotientRepresentative :
    Quot strictFiniteToyCore.equalityQuotient.relation -> Fin 2 :=
  Quot.lift id (by
    intro choice₁ choice₂ hrel
    exact strictFiniteToyEqualityQuotient_relation_eq hrel)

theorem strictFiniteToyEqualityQuotientMap_ne :
    strictFiniteToyCore.equalityQuotientMap (0 : Fin 2) ≠
      strictFiniteToyCore.equalityQuotientMap (1 : Fin 2) := by
  intro hquot
  have h01 : (0 : Fin 2) = (1 : Fin 2) :=
    congrArg strictFiniteToyEqualityQuotientRepresentative hquot
  norm_num at h01

theorem strictFiniteToyInd3Step_not_in_equalityOrbit :
    (1 : Fin 2) ∉ strictFiniteToyCore.equalityOrbit (0 : Fin 2) := by
  intro hmem
  have h01 : (0 : Fin 2) = (1 : Fin 2) :=
    strictFiniteToyEqualityQuotient_relation_eq hmem
  norm_num at h01

structure StrictFiniteToyTypedIndeterminacyNonvacuityAudit (target : Copy) where
  choice_nonempty : Nonempty (Fin 2)
  actionLawAudit :
    strictFiniteToyCore.ActionLawAudit
  ind1_preserves_every_step :
    ∀ {choice₁ choice₂ : Fin 2},
      strictFiniteToyCore.ind1.step choice₁ choice₂ ->
        strictFiniteToyCore.logVolume choice₁ =
          strictFiniteToyCore.logVolume choice₂
  ind2_preserves_every_step :
    ∀ {choice₁ choice₂ : Fin 2},
      strictFiniteToyCore.ind2.step choice₁ choice₂ ->
        strictFiniteToyCore.logVolume choice₁ =
          strictFiniteToyCore.logVolume choice₂
  ind3_strict_step :
    strictFiniteToyCore.ind3.step (0 : Fin 2) (1 : Fin 2)
  ind3_strict_logVolume :
    strictFiniteToyCore.logVolume (0 : Fin 2) <
      strictFiniteToyCore.logVolume (1 : Fin 2)
  ind3_upper_for_strict_step :
    strictFiniteToyCore.logVolume (0 : Fin 2) <=
      strictFiniteToyCore.logVolume (1 : Fin 2)
  ind3_strict_not_in_equalityOrbit :
    (1 : Fin 2) ∉ strictFiniteToyCore.equalityOrbit (0 : Fin 2)
  ind3_strict_quotientMap_ne :
    strictFiniteToyCore.equalityQuotientMap (0 : Fin 2) ≠
      strictFiniteToyCore.equalityQuotientMap (1 : Fin 2)
  equalityQuotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : Fin 2},
      strictFiniteToyCore.equalityGenerators.ind3_step choice₁ choice₂ -> False
  possible_image_compatibility :
    PossibleImageQuotientCompatibility strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target)
  equality_quotient_images :
    EqualityQuotientPossibleImages strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target)

structure StrictFiniteToyEqualityQuotientHullNonvacuityAudit
    (target : Copy)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) where
  typed_nonvacuity :
    StrictFiniteToyTypedIndeterminacyNonvacuityAudit target
  hull_logVolume_compatibility :
    EqualityQuotientHullLogVolumeCompatibility strictFiniteToyCore
      (strictFiniteToyPossibleImageFamily target) hullOperator
  pullback_endpoint :
    ∀ choice₀,
      hull_logVolume_compatibility.familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap choice₀) =
        ((strictFiniteToyPossibleImageFamily target).region choice₀).toSet
  self_hull_endpoint :
    hull_logVolume_compatibility.familySource.possibleRegion
        (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2)) =
        hull_logVolume_compatibility.familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2)) ∧
      hull_logVolume_compatibility.familySource.familyUnion ⊆
        hull_logVolume_compatibility.familySource.canonicalHull ∧
      hull_logVolume_compatibility.familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2)) ⊆
        hull_logVolume_compatibility.familySource.canonicalHull ∧
      hull_logVolume_compatibility.familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2)) ⊆
        hull_logVolume_compatibility.familySource.canonicalHull ∧
      hullOperator.logVolume
          (hull_logVolume_compatibility.familySource.possibleRegion
            (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2))) =
        hullOperator.logVolume
          (hull_logVolume_compatibility.familySource.possibleRegion
            (strictFiniteToyCore.equalityQuotientMap (0 : Fin 2)))
  ind1_hull_logVolume_eq :
    ∀ {choice₁ choice₂ : Fin 2},
      strictFiniteToyCore.ind1.step choice₁ choice₂ ->
        hullOperator.logVolume
            (hull_logVolume_compatibility.familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₁)) =
          hullOperator.logVolume
            (hull_logVolume_compatibility.familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₂))
  ind2_hull_logVolume_eq :
    ∀ {choice₁ choice₂ : Fin 2},
      strictFiniteToyCore.ind2.step choice₁ choice₂ ->
        hullOperator.logVolume
            (hull_logVolume_compatibility.familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₁)) =
          hullOperator.logVolume
            (hull_logVolume_compatibility.familySource.possibleRegion
              (strictFiniteToyCore.equalityQuotientMap choice₂))
  ind3_upper_semi_core_logVolume :
    strictFiniteToyCore.logVolume (0 : Fin 2) <=
      strictFiniteToyCore.logVolume (1 : Fin 2)
  ind3_strict_not_equalized :
    strictFiniteToyCore.ind3.step (0 : Fin 2) (1 : Fin 2) ∧
      strictFiniteToyCore.logVolume (0 : Fin 2) <
        strictFiniteToyCore.logVolume (1 : Fin 2) ∧
      (1 : Fin 2) ∉ strictFiniteToyCore.equalityOrbit (0 : Fin 2) ∧
      strictFiniteToyCore.equalityQuotientMap (0 : Fin 2) ≠
        strictFiniteToyCore.equalityQuotientMap (1 : Fin 2)

def strictFiniteToyTypedIndeterminacyNonvacuityAudit
    (target : Copy) :
    StrictFiniteToyTypedIndeterminacyNonvacuityAudit target :=
  { choice_nonempty := ⟨0⟩,
    actionLawAudit := strictFiniteToyCore.actionLawAudit,
    ind1_preserves_every_step := by
      intro choice₁ choice₂ hstep
      exact strictFiniteToyCore.ind1_preserves_logVolume hstep,
    ind2_preserves_every_step := by
      intro choice₁ choice₂ hstep
      exact strictFiniteToyCore.ind2_preserves_logVolume hstep,
    ind3_strict_step := Or.inr ⟨rfl, rfl⟩,
    ind3_strict_logVolume := by
      norm_num [strictFiniteToyLogVolume, strictFiniteToyCore],
    ind3_upper_for_strict_step := by
      exact strictFiniteToyCore.ind3_logVolume_le (Or.inr ⟨rfl, rfl⟩),
    ind3_strict_not_in_equalityOrbit :=
      strictFiniteToyInd3Step_not_in_equalityOrbit,
    ind3_strict_quotientMap_ne :=
      strictFiniteToyEqualityQuotientMap_ne,
    equalityQuotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact strictFiniteToyCore.equalityGenerators_ind3_false hstep,
    possible_image_compatibility := strictFiniteToyPossibleImageCompatibility target,
    equality_quotient_images := strictFiniteToyEqualityQuotientPossibleImages target }

def strictFiniteToyEqualityQuotientHullNonvacuityAudit
    (target : Copy)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    StrictFiniteToyEqualityQuotientHullNonvacuityAudit
      target hullOperator :=
  let compatibility :=
    strictFiniteToyEqualityQuotientHullLogVolumeCompatibility
      target hullOperator
  { typed_nonvacuity :=
      strictFiniteToyTypedIndeterminacyNonvacuityAudit target,
    hull_logVolume_compatibility := compatibility,
    pullback_endpoint := compatibility.possibleRegion_pullback_eq,
    self_hull_endpoint :=
      compatibility.hull_endpoint_of_equalityOrbit
        (strictFiniteToyCore.mem_equalityOrbit_self (0 : Fin 2)),
    ind1_hull_logVolume_eq := by
      intro choice₁ choice₂ hstep
      exact compatibility.ind1_logVolume_eq hstep,
    ind2_hull_logVolume_eq := by
      intro choice₁ choice₂ hstep
      exact compatibility.ind2_logVolume_eq hstep,
    ind3_upper_semi_core_logVolume := by
      exact strictFiniteToyCore.ind3_logVolume_le (Or.inr ⟨rfl, rfl⟩),
    ind3_strict_not_equalized :=
      ⟨Or.inr ⟨rfl, rfl⟩,
        by
          norm_num [strictFiniteToyLogVolume, strictFiniteToyCore],
        strictFiniteToyInd3Step_not_in_equalityOrbit,
        strictFiniteToyEqualityQuotientMap_ne⟩ }

theorem strictFiniteToyTypedIndeterminacyNonvacuityAudit_ind3_strict_not_equalized
    (target : Copy) :
    strictFiniteToyCore.ind3.step (0 : Fin 2) (1 : Fin 2) ∧
      strictFiniteToyCore.logVolume (0 : Fin 2) <
        strictFiniteToyCore.logVolume (1 : Fin 2) ∧
      (1 : Fin 2) ∉ strictFiniteToyCore.equalityOrbit (0 : Fin 2) ∧
      strictFiniteToyCore.equalityQuotientMap (0 : Fin 2) ≠
        strictFiniteToyCore.equalityQuotientMap (1 : Fin 2) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        strictFiniteToyCore.equalityGenerators.ind3_step choice₁ choice₂ -> False) :=
  ⟨(strictFiniteToyTypedIndeterminacyNonvacuityAudit target).ind3_strict_step,
    (strictFiniteToyTypedIndeterminacyNonvacuityAudit target).ind3_strict_logVolume,
    (strictFiniteToyTypedIndeterminacyNonvacuityAudit target).ind3_strict_not_in_equalityOrbit,
    (strictFiniteToyTypedIndeterminacyNonvacuityAudit target).ind3_strict_quotientMap_ne,
    (strictFiniteToyTypedIndeterminacyNonvacuityAudit target).equalityQuotient_no_ind3_generator⟩

theorem strictFiniteToyEqualityQuotientHullNonvacuityAudit_endpoint
    (target : Copy)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target)) :
    (∀ choice₀,
      (strictFiniteToyEqualityQuotientHullNonvacuityAudit
        target hullOperator).hull_logVolume_compatibility.familySource.possibleRegion
          (strictFiniteToyCore.equalityQuotientMap choice₀) =
        ((strictFiniteToyPossibleImageFamily target).region choice₀).toSet) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        strictFiniteToyCore.ind1.step choice₁ choice₂ ->
          hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullNonvacuityAudit
                target hullOperator).hull_logVolume_compatibility.familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₁)) =
            hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullNonvacuityAudit
                target hullOperator).hull_logVolume_compatibility.familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₂))) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        strictFiniteToyCore.ind2.step choice₁ choice₂ ->
          hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullNonvacuityAudit
                target hullOperator).hull_logVolume_compatibility.familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₁)) =
            hullOperator.logVolume
              ((strictFiniteToyEqualityQuotientHullNonvacuityAudit
                target hullOperator).hull_logVolume_compatibility.familySource.possibleRegion
                (strictFiniteToyCore.equalityQuotientMap choice₂))) ∧
      strictFiniteToyCore.logVolume (0 : Fin 2) <=
        strictFiniteToyCore.logVolume (1 : Fin 2) ∧
      strictFiniteToyCore.ind3.step (0 : Fin 2) (1 : Fin 2) ∧
      strictFiniteToyCore.logVolume (0 : Fin 2) <
        strictFiniteToyCore.logVolume (1 : Fin 2) ∧
      (1 : Fin 2) ∉ strictFiniteToyCore.equalityOrbit (0 : Fin 2) ∧
      strictFiniteToyCore.equalityQuotientMap (0 : Fin 2) ≠
        strictFiniteToyCore.equalityQuotientMap (1 : Fin 2) :=
  let audit :=
    strictFiniteToyEqualityQuotientHullNonvacuityAudit target hullOperator
  ⟨audit.pullback_endpoint,
    audit.ind1_hull_logVolume_eq,
    audit.ind2_hull_logVolume_eq,
    audit.ind3_upper_semi_core_logVolume,
    audit.ind3_strict_not_equalized.1,
    audit.ind3_strict_not_equalized.2.1,
    audit.ind3_strict_not_equalized.2.2.1,
    audit.ind3_strict_not_equalized.2.2.2⟩

end IUTStage1Theorem311TypedIndeterminacyCore

/--
Source-facing statement of the obligations still needed to promote an IUT Stage
1 source package to the public Stage 1 endpoint.

This is intentionally a proposition, not a constructor from source labels. A
future source-specific proof must supply these fields.
-/
structure IUTStage1SourceObligations
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  algorithm_certified : package.preLedger.output.Certified
  she_arrow_matches_certificate :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization

/--
Algorithmic-output component of the Theorem 3.11 source subclaims.

This isolates the opaque certificate for the multiradial algorithm output from
the later SHE-alignment datum.
-/
structure IUTStage1Theorem311AlgorithmicOutput
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  certified : package.preLedger.output.Certified

namespace IUTStage1Theorem311AlgorithmicOutput

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem algorithmOutputCertified
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package) :
    package.preLedger.output.Certified :=
  algorithmicOutput.certified

end IUTStage1Theorem311AlgorithmicOutput

/--
Hodge-theater/SHE-alignment component of the Theorem 3.11 source subclaims.

This isolates the datum that connects the common-container SHE arrow to the
structured SHE certificate stored in the pre-ledger data.
-/
structure IUTStage1Theorem311SHEAlignment
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  alignment :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she

namespace IUTStage1Theorem311SHEAlignment

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem hodgeTheaterSHEAlignment
    (sheAlignment : IUTStage1Theorem311SHEAlignment package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  sheAlignment.alignment

end IUTStage1Theorem311SHEAlignment

namespace IUTStage1Theorem311ToCorollary312PaperTrace

/-!
Lean-facing source map for the Theorem 3.11 to Corollary 3.12 corridor.

The declarations in this namespace are deliberately obligation records, not
primitive constants.  They name the remaining source-paper constructions that must be
supplied before the preferred finite-divisor vertical-`IQ` route is a closed
formalization of the IUT III Corollary 3.12 corridor.
-/

variable {source target : Copy} {index choice : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {targetCopy : Copy}

/--
IUT III, Theorem 3.11 source obligations before the Step (x)/(xi) handoff.

This groups the multiradial representation and the three remarks immediately
following Theorem 3.11.  The fields are intentionally named at the granularity
used by the paper trace: input-prime-strip construction, theta-pilot possible
images, and the multiradial representation that survives the typed
indeterminacy quotient.
-/
structure Theorem311AndRemarksObligations
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (images : RegionFamily targetCopy choice) where
  typed_indeterminacy_nonvacuity_witness_constructed : Prop
  theorem311_multiradial_representation_constructed : Prop
  remark3112_input_prime_strip_link_constructed : Prop
  remark3113_theta_pilot_possible_images_constructed : Prop
  remark3114_log_theta_lattice_procession_constructed : Prop
  possible_images_depend_on_equality_quotient :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      core images
  selected_q_region_is_theorem311_possible_image : Prop
  fl_cardinality_and_procession_label_transitions_constructed : Prop
  theorem311_hodge_she_ipl_apt_source_bridge_constructed : Prop

namespace Theorem311AndRemarksObligations

variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}
variable {images : RegionFamily targetCopy choice}

def RemainingPayloadAudit
    (obligations : Theorem311AndRemarksObligations core images) : Prop :=
  obligations.typed_indeterminacy_nonvacuity_witness_constructed ∧
    obligations.theorem311_multiradial_representation_constructed ∧
    obligations.remark3112_input_prime_strip_link_constructed ∧
    obligations.remark3113_theta_pilot_possible_images_constructed ∧
    obligations.remark3114_log_theta_lattice_procession_constructed ∧
    obligations.selected_q_region_is_theorem311_possible_image ∧
    obligations.fl_cardinality_and_procession_label_transitions_constructed ∧
    obligations.theorem311_hodge_she_ipl_apt_source_bridge_constructed

theorem typedIndeterminacyNonvacuityWitnessConstructed
    (obligations : Theorem311AndRemarksObligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.typed_indeterminacy_nonvacuity_witness_constructed :=
  audit.1

theorem typedIndeterminacyActionLawAudit
    (_obligations : Theorem311AndRemarksObligations core images) :
    core.ActionLawAudit :=
  core.actionLawAudit

theorem ind1_ind2_image_invariant
    (obligations : Theorem311AndRemarksObligations core images) :
    ∀ {choice₁ choice₂ : choice},
      core.equalityQuotient.relation choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ :=
  obligations.possible_images_depend_on_equality_quotient
    |>.equalityQuotient_image_invariant

theorem ind3_logVolume_upper
    (obligations : Theorem311AndRemarksObligations core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  obligations.possible_images_depend_on_equality_quotient
    |>.ind3_upper_from_core hstep

theorem ind3_upperSemiRelationAudit
    (_obligations : Theorem311AndRemarksObligations core images) :
    core.Ind3UpperSemiRelationAudit :=
  core.ind3UpperSemiRelationAudit

theorem equalityQuotient_no_ind3_generator
    (_obligations : Theorem311AndRemarksObligations core images) :
    ∀ {choice₁ choice₂ : choice},
      core.equalityGenerators.ind3_step choice₁ choice₂ -> False :=
  core.ind3UpperSemiRelationAudit
    |>.equalityQuotient_no_ind3_generator

end Theorem311AndRemarksObligations

/--
IUT III, Step (x) obligations on the finite-divisor/log-Kummer side.

The critical distinction is recorded in the first three fields: `(Ind1)` and
`(Ind2)` preserve procession-normalized log-volume, while `(Ind3)` supplies
only an upper-semi inequality.  The remaining fields name the packet,
Kummer/forgetting, and vertical-`IQ` constructions that feed the finite
Corollary 3.12 boundary.
-/
structure StepXFiniteDivisorObligations
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) where
  ind1_procession_normalized_logVolume_preserved :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        core.logVolume choice₁ = core.logVolume choice₂
  ind2_procession_normalized_logVolume_preserved :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        core.logVolume choice₁ = core.logVolume choice₂
  ind3_upper_semi_logVolume_inequality :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂
  ind3_upper_semi_relation_audit :
    core.Ind3UpperSemiRelationAudit
  finite_divisor_packet_source_constructed : Prop
  realified_frobenioid_log_kummer_source_constructed : Prop
  kummer_forgetting_compatibility_constructed : Prop
  vertical_iq_target_source_constructed : Prop
  packet_source_target_log_volume_calibration_constructed : Prop

namespace StepXFiniteDivisorObligations

variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}

def fromTypedCore
    (finite_divisor_packet_source_constructed : Prop)
    (realified_frobenioid_log_kummer_source_constructed : Prop)
    (kummer_forgetting_compatibility_constructed : Prop)
    (vertical_iq_target_source_constructed : Prop)
    (packet_source_target_log_volume_calibration_constructed : Prop) :
    StepXFiniteDivisorObligations core :=
  { ind1_procession_normalized_logVolume_preserved := by
      intro choice₁ choice₂ hstep
      exact core.ind1_preserves_logVolume hstep,
    ind2_procession_normalized_logVolume_preserved := by
      intro choice₁ choice₂ hstep
      exact core.ind2_preserves_logVolume hstep,
    ind3_upper_semi_logVolume_inequality := by
      intro choice₁ choice₂ hstep
      exact core.ind3_logVolume_le hstep,
    ind3_upper_semi_relation_audit :=
      core.ind3UpperSemiRelationAudit,
    finite_divisor_packet_source_constructed :=
      finite_divisor_packet_source_constructed,
    realified_frobenioid_log_kummer_source_constructed :=
      realified_frobenioid_log_kummer_source_constructed,
    kummer_forgetting_compatibility_constructed :=
      kummer_forgetting_compatibility_constructed,
    vertical_iq_target_source_constructed :=
      vertical_iq_target_source_constructed,
    packet_source_target_log_volume_calibration_constructed :=
      packet_source_target_log_volume_calibration_constructed }

end StepXFiniteDivisorObligations

/--
IUT III, Step (xi) and Remark 3.9.5 hull/determinant obligations.

This is the source-paper map underneath the constructed Remark 3.9.5 object
used by the current finite-divisor endpoint.  It names the remaining
holomorphic-hull, determinant, Ob3/Ob4, Ob5, Ob7, and q-to-theta log-volume
chain obligations separately.
-/
structure StepXIHullDeterminantObligations where
  remark395_holomorphic_hull_operator_constructed : Prop
  theorem311_possible_image_family_matches_hull_source : Prop
  selected_q_region_contained_in_possible_image_union : Prop
  ob1_ob2_hull_absorption_constructed : Prop
  ob3_ob4_adjusted_determinant_normalization_constructed : Prop
  ob5_quotient_determinant_compatibility_constructed : Prop
  ob7_prime_strip_log_kummer_compatibility_retained : Prop
  weighted_determinant_tensor_power_bound_constructed : Prop
  q_region_logVolume_le_thetaSigned_constructed : Prop

/--
IUT IV local-to-global `C_Theta` obligations underneath the current
additive-Haar local analytic source.

The fields name the remaining local analytic constructions from IUT IV,
Propositions 1.4 and 1.5, Theorem 1.10, and the global summation comparison
that proves the constructed canonical scale is bounded by `C_Theta`.
-/
structure IUTIVCThetaObligations where
  proposition14_distinguished_log_shell_inclusions_constructed : Prop
  proposition14_distinguished_numerical_bounds_constructed : Prop
  proposition14_nondistinguished_zero_log_volume_constructed : Prop
  proposition15_archimedean_metric_containment_constructed : Prop
  theorem110_arithmetic_divisor_source_constructed : Prop
  theorem110_distinguished_formula_to_gap_constructed : Prop
  theorem110_archimedean_formula_to_gap_constructed : Prop
  additive_haar_local_normalization_constructed : Prop
  finite_place_summed_stepxi_haar_bound_constructed : Prop
  finite_place_total_haar_defect_ge_one_constructed : Prop
  iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed : Prop
  ordered_real_plus_one_cancellation_constructed : Prop
  local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed :
    Prop
  finite_place_arithmetic_gap_constructed : Prop
  local_to_global_canonicalCThetaScale_le_cTheta_constructed : Prop

namespace IUTIVCThetaObligations

def LocalToGlobalArithmeticChainAudit
    (obligations : IUTIVCThetaObligations) : Prop :=
  obligations.finite_place_summed_stepxi_haar_bound_constructed ∧
    obligations.finite_place_total_haar_defect_ge_one_constructed ∧
    obligations.iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed ∧
    obligations.ordered_real_plus_one_cancellation_constructed ∧
    obligations.local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed ∧
    obligations.finite_place_arithmetic_gap_constructed ∧
    obligations.local_to_global_canonicalCThetaScale_le_cTheta_constructed

theorem finitePlaceSummedStepXIHaarBoundConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_summed_stepxi_haar_bound_constructed :=
  audit.1

theorem finitePlaceTotalHaarDefectGeOneConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_total_haar_defect_ge_one_constructed :=
  audit.2.1

theorem iutIVCThetaPlusOneEqArithmeticGapConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed :=
  audit.2.2.1

theorem orderedRealPlusOneCancellationConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.ordered_real_plus_one_cancellation_constructed :=
  audit.2.2.2.1

theorem localStepXITermMatchesIUTIVArithmeticUpperMinusMainConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed :=
  audit.2.2.2.2.1

theorem finitePlaceArithmeticGapConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_arithmetic_gap_constructed :=
  audit.2.2.2.2.2.1

theorem localToGlobalCanonicalCThetaScaleLeCThetaConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.local_to_global_canonicalCThetaScale_le_cTheta_constructed :=
  audit.2.2.2.2.2.2

end IUTIVCThetaObligations

/--
Preferred additive-Haar arithmetic-degree/p-adic formula obligations.

This refines the generic IUT IV `C_Theta` ledger at the currently preferred
finite-divisor endpoint.  It names the remaining source-paper constructions
below the strongest checked route: additive-Haar local analytic construction,
local arithmetic matching, formula splitting, p-adic prime-error splitting, and
the Step (xi) arithmetic-degree calibration.
-/
structure AdditiveHaarArithmeticDegreePadicObligations where
  theorem110_additive_haar_local_analytic_construction_constructed : Prop
  additive_haar_local_arithmetic_matching_constructed : Prop
  arithmetic_divisor_formula_split_constructed : Prop
  padic_prime_error_defect_main_split_constructed : Prop
  stepxi_arithmetic_degree_calibration_constructed : Prop
  localized_determinant_multiplicity_matches_iutiv_coefficient : Prop
  adjusted_raw_log_volume_matches_different_plus_conductor : Prop
  realified_packet_source_supplies_stepx_equalities : Prop
  constructed_ipl_choice_link_endpoint_threaded : Prop
  constructed_ipl_datum_certificate_alignment_threaded : Prop
  constructed_hodge_she_ipl_apt_structures_threaded : Prop
  constructed_she_apt_transport_guards_threaded : Prop
  constructed_ipl_she_apt_transport_law_audit_threaded : Prop
  strongest_additive_haar_endpoint_has_remaining_payload_audit : Prop

namespace AdditiveHaarArithmeticDegreePadicObligations

def RemainingPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations) : Prop :=
  obligations.theorem110_additive_haar_local_analytic_construction_constructed ∧
    obligations.additive_haar_local_arithmetic_matching_constructed ∧
    obligations.arithmetic_divisor_formula_split_constructed ∧
    obligations.padic_prime_error_defect_main_split_constructed ∧
    obligations.stepxi_arithmetic_degree_calibration_constructed ∧
    obligations.localized_determinant_multiplicity_matches_iutiv_coefficient ∧
    obligations.adjusted_raw_log_volume_matches_different_plus_conductor ∧
    obligations.realified_packet_source_supplies_stepx_equalities ∧
    obligations.constructed_ipl_choice_link_endpoint_threaded ∧
    obligations.constructed_ipl_datum_certificate_alignment_threaded ∧
    obligations.constructed_hodge_she_ipl_apt_structures_threaded ∧
    obligations.constructed_she_apt_transport_guards_threaded ∧
    obligations.constructed_ipl_she_apt_transport_law_audit_threaded ∧
    obligations.strongest_additive_haar_endpoint_has_remaining_payload_audit

theorem constructedIPLChoiceLinkEndpointThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_choice_link_endpoint_threaded := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, hthreaded, _, _, _, _, _⟩
  exact hthreaded

theorem constructedIPLCertificateAlignmentThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_datum_certificate_alignment_threaded := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, _, hthreaded, _, _, _, _⟩
  exact hthreaded

theorem constructedHodgeSHEIPLAPTStructuresThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_hodge_she_ipl_apt_structures_threaded := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, _, _, hthreaded, _, _, _⟩
  exact hthreaded

theorem constructedSHEAPTTransportGuardsThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_she_apt_transport_guards_threaded := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, _, _, _, hthreaded, _, _⟩
  exact hthreaded

theorem constructedIPLSHEAPTTransportLawAuditThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_she_apt_transport_law_audit_threaded := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hthreaded, _⟩
  exact hthreaded

theorem theorem110AdditiveHaarLocalAnalyticConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.theorem110_additive_haar_local_analytic_construction_constructed := by
  rcases audit with ⟨h, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact h

theorem additiveHaarLocalArithmeticMatchingConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_local_arithmetic_matching_constructed := by
  rcases audit with ⟨_, h, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact h

theorem arithmeticDivisorFormulaSplitConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.arithmetic_divisor_formula_split_constructed := by
  rcases audit with ⟨_, _, h, _, _, _, _, _, _, _, _, _, _, _⟩
  exact h

theorem padicPrimeErrorDefectMainSplitConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.padic_prime_error_defect_main_split_constructed := by
  rcases audit with ⟨_, _, _, h, _, _, _, _, _, _, _, _, _, _⟩
  exact h

theorem stepXIArithmeticDegreeCalibrationConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.stepxi_arithmetic_degree_calibration_constructed := by
  rcases audit with ⟨_, _, _, _, h, _, _, _, _, _, _, _, _, _⟩
  exact h

theorem localizedDeterminantMultiplicityMatchesIUTIVCoefficient
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.localized_determinant_multiplicity_matches_iutiv_coefficient := by
  rcases audit with ⟨_, _, _, _, _, h, _, _, _, _, _, _, _, _⟩
  exact h

theorem adjustedRawLogVolumeMatchesDifferentPlusConductor
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.adjusted_raw_log_volume_matches_different_plus_conductor := by
  rcases audit with ⟨_, _, _, _, _, _, h, _, _, _, _, _, _, _⟩
  exact h

theorem realifiedPacketSourceSuppliesStepXEqualities
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.realified_packet_source_supplies_stepx_equalities := by
  rcases audit with ⟨_, _, _, _, _, _, _, h, _, _, _, _, _, _⟩
  exact h

theorem strongestAdditiveHaarEndpointHasRemainingPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.strongest_additive_haar_endpoint_has_remaining_payload_audit := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  exact h

end AdditiveHaarArithmeticDegreePadicObligations

/--
Assembled paper-trace source obligation map for the Theorem 3.11 to
Corollary 3.12 corridor.

This is the declaration-level deliverable for the paper trace: every remaining
source obligation is assigned to Theorem 3.11/Remarks 3.11.2--3.11.4, Step
(x), Step (xi), or IUT IV.  The last two fields state the endpoint-level goal
of this milestone: the raw numeric bound and raw canonical-scale comparison
must disappear from the public endpoint once the obligations are constructed.
-/
structure Obligations
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    (images : RegionFamily targetCopy choice) where
  theorem311_and_remarks :
    Theorem311AndRemarksObligations core images
  stepX_finite_divisor :
    StepXFiniteDivisorObligations core
  stepXI_hull_determinant :
    StepXIHullDeterminantObligations
  iutIV_cTheta :
    IUTIVCThetaObligations
  additive_haar_arithmetic_degree_padic :
    AdditiveHaarArithmeticDegreePadicObligations
  closed_endpoint_removes_thetaSigned_le_cTheta_absLogQ_hypothesis : Prop
  closed_endpoint_removes_raw_canonicalCThetaScale_le_cTheta_hypothesis : Prop

namespace Obligations

variable {core : IUTStage1Theorem311TypedIndeterminacyCore choice}
variable {images : RegionFamily targetCopy choice}

def RemainingPayloadAudit
    (obligations : Obligations core images) : Prop :=
  obligations.theorem311_and_remarks.typed_indeterminacy_nonvacuity_witness_constructed ∧
    obligations.theorem311_and_remarks.theorem311_multiradial_representation_constructed ∧
    obligations.theorem311_and_remarks.remark3112_input_prime_strip_link_constructed ∧
    obligations.theorem311_and_remarks.remark3113_theta_pilot_possible_images_constructed ∧
    obligations.theorem311_and_remarks.remark3114_log_theta_lattice_procession_constructed ∧
    obligations.theorem311_and_remarks.selected_q_region_is_theorem311_possible_image ∧
    obligations.theorem311_and_remarks.fl_cardinality_and_procession_label_transitions_constructed ∧
    obligations.theorem311_and_remarks.theorem311_hodge_she_ipl_apt_source_bridge_constructed ∧
    obligations.stepX_finite_divisor.finite_divisor_packet_source_constructed ∧
    obligations.stepX_finite_divisor.realified_frobenioid_log_kummer_source_constructed ∧
    obligations.stepX_finite_divisor.kummer_forgetting_compatibility_constructed ∧
    obligations.stepX_finite_divisor.vertical_iq_target_source_constructed ∧
    obligations.stepX_finite_divisor.packet_source_target_log_volume_calibration_constructed ∧
    obligations.stepXI_hull_determinant.remark395_holomorphic_hull_operator_constructed ∧
    obligations.stepXI_hull_determinant.theorem311_possible_image_family_matches_hull_source ∧
    obligations.stepXI_hull_determinant.selected_q_region_contained_in_possible_image_union ∧
    obligations.stepXI_hull_determinant.ob1_ob2_hull_absorption_constructed ∧
    obligations.stepXI_hull_determinant.ob3_ob4_adjusted_determinant_normalization_constructed ∧
    obligations.stepXI_hull_determinant.ob5_quotient_determinant_compatibility_constructed ∧
    obligations.stepXI_hull_determinant.ob7_prime_strip_log_kummer_compatibility_retained ∧
    obligations.stepXI_hull_determinant.weighted_determinant_tensor_power_bound_constructed ∧
    obligations.stepXI_hull_determinant.q_region_logVolume_le_thetaSigned_constructed ∧
    obligations.iutIV_cTheta.proposition14_distinguished_log_shell_inclusions_constructed ∧
    obligations.iutIV_cTheta.proposition14_distinguished_numerical_bounds_constructed ∧
    obligations.iutIV_cTheta.proposition14_nondistinguished_zero_log_volume_constructed ∧
    obligations.iutIV_cTheta.proposition15_archimedean_metric_containment_constructed ∧
    obligations.iutIV_cTheta.theorem110_arithmetic_divisor_source_constructed ∧
    obligations.iutIV_cTheta.theorem110_distinguished_formula_to_gap_constructed ∧
    obligations.iutIV_cTheta.theorem110_archimedean_formula_to_gap_constructed ∧
    obligations.iutIV_cTheta.additive_haar_local_normalization_constructed ∧
    obligations.iutIV_cTheta.finite_place_summed_stepxi_haar_bound_constructed ∧
    obligations.iutIV_cTheta.finite_place_total_haar_defect_ge_one_constructed ∧
    obligations.iutIV_cTheta.iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed ∧
    obligations.iutIV_cTheta.ordered_real_plus_one_cancellation_constructed ∧
    (IUTIVCThetaObligations.local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed
      obligations.iutIV_cTheta) ∧
    obligations.iutIV_cTheta.finite_place_arithmetic_gap_constructed ∧
    obligations.iutIV_cTheta.local_to_global_canonicalCThetaScale_le_cTheta_constructed ∧
    obligations.additive_haar_arithmetic_degree_padic.RemainingPayloadAudit ∧
    obligations.closed_endpoint_removes_thetaSigned_le_cTheta_absLogQ_hypothesis ∧
    obligations.closed_endpoint_removes_raw_canonicalCThetaScale_le_cTheta_hypothesis

theorem ind3_upper_semi_not_equality_payload
    (obligations : Obligations core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  obligations.stepX_finite_divisor.ind3_upper_semi_logVolume_inequality hstep

theorem theorem311_action_law_audit
    (_obligations : Obligations core images) :
    core.ActionLawAudit :=
  core.actionLawAudit

theorem ind3_upper_semi_relation_audit
    (obligations : Obligations core images) :
    core.Ind3UpperSemiRelationAudit :=
  obligations.stepX_finite_divisor.ind3_upper_semi_relation_audit

theorem ind3_upper_semi_step_audit
    (obligations : Obligations core images)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.Ind3UpperSemiStepAudit choice₁ choice₂ :=
  obligations.ind3_upper_semi_relation_audit
    |>.upper_semi_step_audit hstep

theorem equalityQuotient_no_ind3_generator
    (obligations : Obligations core images) :
    ∀ {choice₁ choice₂ : choice},
      core.equalityGenerators.ind3_step choice₁ choice₂ -> False :=
  obligations.ind3_upper_semi_relation_audit
    |>.equalityQuotient_no_ind3_generator

end Obligations

end IUTStage1Theorem311ToCorollary312PaperTrace
end Stage1
end Iut
