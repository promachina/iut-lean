/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Gaussian

/-!
Hodge/SHE and local packet support data for the Stage 1 corridor.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps square-weighted full-label transport audits, labelled capsule-family and
packet-normalization support, local Hodge-descent/SHE object data, direct-summand
local tensor actions, and upper-semi compatibility states.  The Theorem 3.11,
IPL, Step (xi), and endpoint-route declarations remain in
`Iut.Stage1.IUTStage1Source` for now.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

/--
Audit that square-weighted full-label summands survive a Hodge-theater/descent
bridge along an explicit coordinate equivalence.

This record does not construct the bridge.  It states exactly what a future
Hodge-theater/log-link argument must supply before one may compare transported
`j^2`-weighted summands: preservation of the full-label log-volume branch,
preservation of the square weight, and preservation of the total weight.
-/
structure IUTStage1ZModSquareWeightedFullLabelTransportAudit
    (l : PrimeGeFive) where
  bridge : IUTStage1HodgeTheaterDescentBridgeData
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  sourceProfile : IUTStage1ZModSquareWeightProfile l
  targetProfile : IUTStage1ZModSquareWeightProfile l
  sourceLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  targetLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  fullLabelLogVolume_preserved :
    ∀ j : ZMod l.value,
      targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)
  squareWeight_preserved :
    ∀ j : ZMod l.value,
      targetProfile.weight (coordinateEquiv j) =
        sourceProfile.weight j
  weightTotal_preserved :
    targetProfile.weightTotal = sourceProfile.weightTotal

namespace IUTStage1ZModSquareWeightedFullLabelTransportAudit

variable {l : PrimeGeFive}

def sourceNumerator
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    Real :=
  Finset.univ.sum fun j : ZMod l.value =>
    audit.sourceProfile.weight j *
      audit.sourceLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

def targetTransportedNumerator
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    Real :=
  Finset.univ.sum fun j : ZMod l.value =>
    audit.targetProfile.weight (audit.coordinateEquiv j) *
      audit.targetLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (audit.coordinateEquiv j))

noncomputable def sourceAverage
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    Real :=
  audit.sourceNumerator / audit.sourceProfile.weightTotal

noncomputable def targetTransportedAverage
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    Real :=
  audit.targetTransportedNumerator / audit.targetProfile.weightTotal

theorem histories_not_identified
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.bridge.domainTheater.side ≠ audit.bridge.codomainTheater.side :=
  audit.bridge.histories_not_identified

theorem transportedFullLabelLogVolume_preserved
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    (j : ZMod l.value) :
    audit.targetLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (audit.coordinateEquiv j)) =
      audit.sourceLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  audit.fullLabelLogVolume_preserved j

theorem transportedSquareWeight_preserved
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    (j : ZMod l.value) :
    audit.targetProfile.weight (audit.coordinateEquiv j) =
      audit.sourceProfile.weight j :=
  audit.squareWeight_preserved j

theorem coordinateSquarePreserving
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
  IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
      (l := l) audit.coordinateEquiv :=
  IUTStage1ZModSquareWeightProfile.coordinateSquarePreserving_of_squareWeight_preserved
    audit.sourceProfile audit.targetProfile audit.squareWeight_preserved

theorem coordinateEquiv_apply_eq
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    (j : ZMod l.value) :
    audit.coordinateEquiv j = j :=
  IUTStage1ZModSquareWeightProfile.coordinateSquarePreserving_apply_eq
    audit.coordinateSquarePreserving j

theorem coordinateEquiv_eq_refl
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.coordinateEquiv = Equiv.refl (ZMod l.value) :=
  IUTStage1ZModSquareWeightProfile.coordinateSquarePreserving_eq_refl
    audit.coordinateSquarePreserving

theorem coordinateEquiv_ne_neg
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.coordinateEquiv ≠ Equiv.neg (ZMod l.value) := by
  intro h
  exact IUTStage1ZModSquareWeightProfile.not_coordinateSquarePreserving_neg
    (by
      rw [← h]
      exact audit.coordinateSquarePreserving)

theorem targetTransportedSummand_eq_sourceSummand
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    (j : ZMod l.value) :
    audit.targetProfile.weight (audit.coordinateEquiv j) *
      audit.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (audit.coordinateEquiv j)) =
      audit.sourceProfile.weight j *
        audit.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [audit.transportedSquareWeight_preserved j,
    audit.transportedFullLabelLogVolume_preserved j]

theorem targetTransportedNumerator_eq_sourceNumerator
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.targetTransportedNumerator = audit.sourceNumerator := by
  unfold targetTransportedNumerator sourceNumerator
  exact Finset.sum_congr rfl (by
    intro j _hj
    exact audit.targetTransportedSummand_eq_sourceSummand j)

theorem targetTransportedAverage_eq_sourceAverage
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.targetTransportedAverage = audit.sourceAverage := by
  unfold targetTransportedAverage sourceAverage
  rw [audit.targetTransportedNumerator_eq_sourceNumerator,
    audit.weightTotal_preserved]

noncomputable def targetTransportedWeightedLogVolume
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    IUTStage1WeightedLabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume := fun j =>
      audit.targetLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (audit.coordinateEquiv j)),
    weight := fun j => audit.targetProfile.weight (audit.coordinateEquiv j),
    weightTotal := audit.targetProfile.weightTotal,
    positive_weightTotal := audit.targetProfile.positive_weightTotal,
    weightTotal_eq_sum := by
      rw [audit.targetProfile.weightTotal_eq_sum]
      exact
        (Fintype.sum_equiv audit.coordinateEquiv
          (fun j : ZMod l.value =>
            audit.targetProfile.weight (audit.coordinateEquiv j))
          audit.targetProfile.weight
          (fun _j => rfl)).symm,
    weightedAverageLogVolume := audit.targetTransportedAverage,
    weighted_average_eq := rfl }

theorem targetTransportedWeightedLogVolume_weight_nonnegative
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    (j : ZMod l.value) :
    0 <= audit.targetTransportedWeightedLogVolume.weight j :=
  audit.targetProfile.weight_nonnegative (audit.coordinateEquiv j)

theorem targetTransportedWeightedLogVolume_average_eq
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l) :
    audit.targetTransportedWeightedLogVolume.weightedAverageLogVolume =
      audit.targetTransportedAverage :=
  rfl

theorem targetTransportedAverage_le_of_forall_targetFullLabel_le
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    {c : Real}
    (hpointwise :
      ∀ j : ZMod l.value,
        audit.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (audit.coordinateEquiv j)) <= c) :
    audit.targetTransportedAverage <= c := by
  rw [← audit.targetTransportedWeightedLogVolume_average_eq]
  exact
    audit.targetTransportedWeightedLogVolume.weightedAverage_le_const_of_forall_le
      audit.targetTransportedWeightedLogVolume_weight_nonnegative
      hpointwise

theorem targetTransportedAverage_le_of_weighted_target_summand_le
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    {c : Real}
    (hsummand :
      ∀ j : ZMod l.value,
        audit.targetProfile.weight (audit.coordinateEquiv j) *
            audit.targetLogVolume.fullLabelLogVolume
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (audit.coordinateEquiv j)) <=
          audit.targetProfile.weight (audit.coordinateEquiv j) * c) :
    audit.targetTransportedAverage <= c := by
  rw [← audit.targetTransportedWeightedLogVolume_average_eq]
  exact
    audit.targetTransportedWeightedLogVolume
      |>.weightedAverage_le_const_of_weighted_summand_le
        hsummand

theorem targetTransportedAverage_le_of_forall_nonzero_targetFullLabel_le
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    {c : Real}
    (hpointwise :
      ∀ j : ZMod l.value,
        audit.coordinateEquiv j ≠ 0 ->
          audit.targetLogVolume.fullLabelLogVolume
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (audit.coordinateEquiv j)) <= c) :
    audit.targetTransportedAverage <= c := by
  exact audit.targetTransportedAverage_le_of_weighted_target_summand_le
    (by
      intro j
      by_cases hzero : audit.coordinateEquiv j = 0
      · rw [hzero, audit.targetProfile.weight_eq_square_val]
        simp
      · exact mul_le_mul_of_nonneg_left
          (hpointwise j hzero)
          (audit.targetProfile.weight_nonnegative (audit.coordinateEquiv j)))

theorem sourceAverage_le_of_forall_targetFullLabel_le
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    {c : Real}
    (hpointwise :
      ∀ j : ZMod l.value,
        audit.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (audit.coordinateEquiv j)) <= c) :
    audit.sourceAverage <= c := by
  rw [← audit.targetTransportedAverage_eq_sourceAverage]
  exact audit.targetTransportedAverage_le_of_forall_targetFullLabel_le
    hpointwise

theorem sourceAverage_le_of_forall_nonzero_targetFullLabel_le
    (audit : IUTStage1ZModSquareWeightedFullLabelTransportAudit l)
    {c : Real}
    (hpointwise :
      ∀ j : ZMod l.value,
        audit.coordinateEquiv j ≠ 0 ->
          audit.targetLogVolume.fullLabelLogVolume
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (audit.coordinateEquiv j)) <= c) :
    audit.sourceAverage <= c := by
  rw [← audit.targetTransportedAverage_eq_sourceAverage]
  exact audit.targetTransportedAverage_le_of_forall_nonzero_targetFullLabel_le
    hpointwise

end IUTStage1ZModSquareWeightedFullLabelTransportAudit

namespace IUTStage1CapsuleFamilyLogVolume

variable {kind : IUTStage1PlaceKind}

theorem total_eq
    (data : IUTStage1CapsuleFamilyLogVolume kind) :
    data.totalLogVolume = Finset.univ.sum data.capsuleLogVolume :=
  data.total_eq_sum

theorem normalized_eq
    (data : IUTStage1CapsuleFamilyLogVolume kind) :
    data.normalizedLogVolume =
      data.totalLogVolume / (data.capsuleCount : Real) :=
  data.normalized_eq_average

theorem capsuleCount_pos
    (data : IUTStage1CapsuleFamilyLogVolume kind) :
    0 < data.capsuleCount :=
  data.positive_capsule_count

def toProcessionNormalizedLogVolume
    (data : IUTStage1CapsuleFamilyLogVolume kind) :
    IUTStage1ProcessionNormalizedLogVolume kind :=
  { localObject := data.localObject,
    capsuleCount := data.capsuleCount,
    positive_capsule_count := data.positive_capsule_count,
    totalLogVolume := data.totalLogVolume,
    normalizedLogVolume := data.normalizedLogVolume,
    normalized_eq_average := data.normalized_eq_average }

theorem toProcession_total_eq
    (data : IUTStage1CapsuleFamilyLogVolume kind) :
    data.toProcessionNormalizedLogVolume.totalLogVolume =
      Finset.univ.sum data.capsuleLogVolume :=
  data.total_eq

end IUTStage1CapsuleFamilyLogVolume

namespace IUTStage1CapsuleLogVolumeObject

variable {kind : IUTStage1PlaceKind}

theorem logVolume_eq
    (capsule : IUTStage1CapsuleLogVolumeObject kind) :
    capsule.logVolume = capsule.localObject.finiteLogVolume :=
  capsule.log_volume_eq

end IUTStage1CapsuleLogVolumeObject

/--
`F_l`-labelled procession-normalized capsule log-volumes.

Step (x) of the proof of IUT III, Corollary 3.12 uses procession-normalized
mono-analytic log-volumes obtained by averaging over the labels
`j ∈ F_l`.  This source object replaces an anonymous capsule count by the
actual finite label set `ZMod l.value`; the total log-volume is the finite sum
over this label set, and the normalized value is the average obtained by
dividing by `l`.
-/
structure IUTStage1ZModLabelledCapsuleFamilyLogVolume
    (l : PrimeGeFive) (kind : IUTStage1PlaceKind) where
  localObject : IUTStage1FiniteLocalLogVolumeObject kind
  capsule : ZMod l.value -> IUTStage1CapsuleLogVolumeObject kind
  capsule_local_object_eq :
    ∀ j : ZMod l.value, (capsule j).localObject = localObject
  totalLogVolume : Real
  total_eq_sum :
    totalLogVolume =
      Finset.univ.sum fun j : ZMod l.value => (capsule j).logVolume
  normalizedLogVolume : Real
  normalized_eq_average :
    normalizedLogVolume = totalLogVolume / (l.value : Real)

namespace IUTStage1ZModLabelledCapsuleFamilyLogVolume

variable {l : PrimeGeFive} {kind : IUTStage1PlaceKind}

def capsuleLogVolume
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    ZMod l.value -> Real :=
  fun j => (data.capsule j).logVolume

theorem capsuleLocalObject_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (j : ZMod l.value) :
    (data.capsule j).localObject = data.localObject :=
  data.capsule_local_object_eq j

theorem total_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    data.totalLogVolume =
      Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume :=
  data.total_eq_sum

theorem normalized_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    data.normalizedLogVolume =
      data.totalLogVolume / (l.value : Real) :=
  data.normalized_eq_average

theorem normalized_eq_zmod_average
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    data.normalizedLogVolume =
      (Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume) /
        (l.value : Real) := by
  rw [data.normalized_eq, data.total_eq]

def toLabelAveraged
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume := data.capsuleLogVolume,
    averageLogVolume := data.normalizedLogVolume,
    average_eq := by
      rw [data.normalized_eq_zmod_average, ZMod.card]
      rfl }

theorem toLabelAveraged_averageLogVolume
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    data.toLabelAveraged.averageLogVolume = data.normalizedLogVolume :=
  rfl

def constantFromLocalObject
    (localObject : IUTStage1FiniteLocalLogVolumeObject kind) :
    IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind :=
  { localObject := localObject,
    capsule := fun _ =>
      { capsuleLabel := "ZMod packet-local canonical capsule",
        localObject := localObject,
        logVolume := localObject.finiteLogVolume,
        log_volume_eq := rfl },
    capsule_local_object_eq := by
      intro _j
      rfl,
    totalLogVolume := localObject.finiteLogVolume * (l.value : Real),
    total_eq_sum := by
      simp [ZMod.card, mul_comm],
    normalizedLogVolume := localObject.finiteLogVolume,
    normalized_eq_average := by
      have hl : (l.value : Real) ≠ 0 := by
        exact_mod_cast l.ne_zero
      field_simp [hl] }

theorem constantFromLocalObject_localObject
    (localObject : IUTStage1FiniteLocalLogVolumeObject kind) :
    (constantFromLocalObject (l := l) localObject).localObject =
      localObject :=
  rfl

theorem constantFromLocalObject_normalizedLogVolume
    (localObject : IUTStage1FiniteLocalLogVolumeObject kind) :
    (constantFromLocalObject (l := l) localObject).normalizedLogVolume =
      localObject.finiteLogVolume :=
  rfl

theorem zmodTranslation_total_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t : ZMod l.value) :
    (Finset.univ.sum fun j : ZMod l.value =>
      (data.capsule (zmodLabelTranslate l t j)).logVolume) =
      Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume :=
  IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodTranslation_sum_eq
    (l := l) t data.capsuleLogVolume

theorem zmodUnitAffine_total_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (Finset.univ.sum fun j : ZMod l.value =>
      (data.capsule
        (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))).logVolume) =
      Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume :=
  IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffine_sum_eq
    (l := l) a t data.capsuleLogVolume

theorem zmodTranslation_average_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t : ZMod l.value) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      (data.capsule (zmodLabelTranslate l t j)).logVolume) /
        (l.value : Real)) = data.normalizedLogVolume := by
  rw [data.zmodTranslation_total_eq t]
  exact data.normalized_eq_zmod_average.symm

theorem zmodUnitAffine_average_eq
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      (data.capsule
        (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))).logVolume) /
        (l.value : Real)) = data.normalizedLogVolume := by
  rw [data.zmodUnitAffine_total_eq a t]
  exact data.normalized_eq_zmod_average.symm

noncomputable def translatedLabelAveraged
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t : ZMod l.value) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume :=
      fun j : ZMod l.value =>
        (data.capsule (zmodLabelTranslate l t j)).logVolume,
    averageLogVolume := data.normalizedLogVolume,
    average_eq := by
      rw [ZMod.card]
      exact (data.zmodTranslation_average_eq t).symm }

noncomputable def doubleTranslatedLabelAveraged
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t₁ t₂ : ZMod l.value) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume :=
      fun j : ZMod l.value =>
        (data.capsule
          (zmodLabelTranslate l t₂ (zmodLabelTranslate l t₁ j))).logVolume,
    averageLogVolume := data.normalizedLogVolume,
    average_eq := by
      rw [ZMod.card]
      have hsum :
          (Finset.univ.sum fun j : ZMod l.value =>
            (data.capsule
              (zmodLabelTranslate l t₂ (zmodLabelTranslate l t₁ j))).logVolume) =
            Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume := by
        calc
          (Finset.univ.sum fun j : ZMod l.value =>
            (data.capsule
              (zmodLabelTranslate l t₂ (zmodLabelTranslate l t₁ j))).logVolume) =
              Finset.univ.sum fun j : ZMod l.value =>
                (data.capsule (zmodLabelTranslate l t₂ j)).logVolume :=
            IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodTranslation_sum_eq
              (l := l) t₁
              (fun j : ZMod l.value =>
                (data.capsule (zmodLabelTranslate l t₂ j)).logVolume)
          _ = Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume :=
            data.zmodTranslation_total_eq t₂
      rw [hsum]
      exact data.normalized_eq_zmod_average }

theorem translatedLabelAveraged_averageLogVolume
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t : ZMod l.value) :
    (data.translatedLabelAveraged t).averageLogVolume =
      data.normalizedLogVolume :=
  rfl

theorem doubleTranslatedLabelAveraged_averageLogVolume
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t₁ t₂ : ZMod l.value) :
    (data.doubleTranslatedLabelAveraged t₁ t₂).averageLogVolume =
      data.normalizedLogVolume :=
  rfl

theorem const_le_normalizedLogVolume_of_capsule_le
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    {c : Real}
    (hcapsule : ∀ j : ZMod l.value, c <= (data.capsule j).logVolume) :
    c <= data.normalizedLogVolume := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  exact
    IUTStage1LabelAveragedProcessionLogVolume.const_le_average_of_forall_le
      data.toLabelAveraged hcapsule

theorem normalizedLogVolume_le_const_of_capsule_le
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    {c : Real}
    (hcapsule : ∀ j : ZMod l.value, (data.capsule j).logVolume <= c) :
    data.normalizedLogVolume <= c := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  exact
    IUTStage1LabelAveragedProcessionLogVolume.average_le_const_of_forall_le
      data.toLabelAveraged hcapsule

theorem capsuleLogVolume_eq_localObjectFinite
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (j : ZMod l.value) :
    (data.capsule j).logVolume = data.localObject.finiteLogVolume := by
  calc
    (data.capsule j).logVolume =
        (data.capsule j).localObject.finiteLogVolume :=
      (data.capsule j).logVolume_eq
    _ = data.localObject.finiteLogVolume := by
      rw [data.capsule_local_object_eq j]

theorem normalizedLogVolume_eq_localObjectFinite
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind) :
    data.normalizedLogVolume = data.localObject.finiteLogVolume := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  have haverage :
      data.toLabelAveraged.averageLogVolume =
        (IUTStage1LabelAveragedProcessionLogVolume.constant
          (label := ZMod l.value) data.localObject.finiteLogVolume).averageLogVolume :=
    IUTStage1LabelAveragedProcessionLogVolume.average_eq_of_pointwise
      (data₁ := data.toLabelAveraged)
      (data₂ := IUTStage1LabelAveragedProcessionLogVolume.constant
        (label := ZMod l.value) data.localObject.finiteLogVolume)
      (fun j => data.capsuleLogVolume_eq_localObjectFinite j)
  simpa [IUTStage1LabelAveragedProcessionLogVolume.constant] using haverage

theorem zmod_labelled_procession_endpoint
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t : ZMod l.value) :
    data.totalLogVolume =
        (Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume) ∧
      data.normalizedLogVolume =
        (Finset.univ.sum fun j : ZMod l.value => (data.capsule j).logVolume) /
          (l.value : Real) ∧
      ((Finset.univ.sum fun j : ZMod l.value =>
        (data.capsule (zmodLabelTranslate l t j)).logVolume) /
          (l.value : Real)) = data.normalizedLogVolume :=
  ⟨data.total_eq, data.normalized_eq_zmod_average,
    data.zmodTranslation_average_eq t⟩

/--
Step (x) finite-label indeterminacy endpoint.

Two successive `F_l` label translations preserve the procession-normalized
average by finite reindexing.  A pointwise upper bound after these translations
therefore gives the one-sided `(Ind3)` upper bound for the original average.
-/
theorem zmod_labelled_translation_indeterminacy_endpoint
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    (t₁ t₂ : ZMod l.value)
    {ind3UpperBound : Real}
    (hind3 :
      ∀ j : ZMod l.value,
        (data.capsule
          (zmodLabelTranslate l t₂ (zmodLabelTranslate l t₁ j))).logVolume <=
          ind3UpperBound) :
    (data.translatedLabelAveraged t₁).averageLogVolume =
        data.normalizedLogVolume ∧
      (data.doubleTranslatedLabelAveraged t₁ t₂).averageLogVolume =
        data.normalizedLogVolume ∧
      (data.doubleTranslatedLabelAveraged t₁ t₂).averageLogVolume <=
        ind3UpperBound ∧
      data.normalizedLogVolume <= ind3UpperBound := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  have hafter2 :
      (data.doubleTranslatedLabelAveraged t₁ t₂).averageLogVolume <=
        ind3UpperBound :=
    IUTStage1LabelAveragedProcessionLogVolume.average_le_const_of_forall_le
      (data.doubleTranslatedLabelAveraged t₁ t₂) hind3
  exact
    ⟨data.translatedLabelAveraged_averageLogVolume t₁,
      data.doubleTranslatedLabelAveraged_averageLogVolume t₁ t₂,
      hafter2,
      by
        rw [← data.doubleTranslatedLabelAveraged_averageLogVolume t₁ t₂]
        exact hafter2⟩

end IUTStage1ZModLabelledCapsuleFamilyLogVolume

/--
Container estimate for one capsule log-volume entry.

The local object used by the estimate must match the local object carried by
the capsule entry.
-/
structure IUTStage1CapsuleEntryContainerEstimate
    {kind : IUTStage1PlaceKind}
    (targetSigned : Real)
    (capsule : IUTStage1CapsuleLogVolumeObject kind) where
  objectEstimate :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned capsule.logVolume
  localObject_eq_capsuleLocalObject :
    objectEstimate.localObject = capsule.localObject

namespace IUTStage1CapsuleEntryContainerEstimate

variable {kind : IUTStage1PlaceKind}
variable {targetSigned : Real}
variable {capsule : IUTStage1CapsuleLogVolumeObject kind}

theorem targetSigned_le_capsuleLogVolume
    (estimate :
      IUTStage1CapsuleEntryContainerEstimate targetSigned capsule) :
    targetSigned <= capsule.logVolume :=
  estimate.objectEstimate.targetSigned_le_localLogVolume

theorem localObject_eq_capsuleLocalObject'
    (estimate :
      IUTStage1CapsuleEntryContainerEstimate targetSigned capsule) :
    estimate.objectEstimate.localObject = capsule.localObject :=
  estimate.localObject_eq_capsuleLocalObject

def transportCapsule
    (estimate :
      IUTStage1CapsuleEntryContainerEstimate targetSigned capsule)
    (newCapsule : IUTStage1CapsuleLogVolumeObject kind)
    (hlog : newCapsule.logVolume = capsule.logVolume)
    (hobject : estimate.objectEstimate.localObject = newCapsule.localObject) :
    IUTStage1CapsuleEntryContainerEstimate targetSigned newCapsule :=
  { objectEstimate := estimate.objectEstimate.transportLocalLogVolume hlog,
    localObject_eq_capsuleLocalObject := hobject }

end IUTStage1CapsuleEntryContainerEstimate

/-- Container estimates for every entry of a typed capsule family. -/
structure IUTStage1TypedCapsuleFamilyContainerEstimate
    {kind : IUTStage1PlaceKind}
    (targetSigned : Real)
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) where
  capsuleEntryEstimate :
    ∀ i : Fin data.capsuleCount,
      IUTStage1CapsuleEntryContainerEstimate targetSigned (data.capsule i)

namespace IUTStage1TypedCapsuleFamilyLogVolume

variable {kind : IUTStage1PlaceKind}

theorem capsuleLocalObject_eq
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind)
    (i : Fin data.capsuleCount) :
    (data.capsule i).localObject = data.localObject :=
  data.capsule_local_object_eq i

theorem total_eq
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    data.totalLogVolume =
      Finset.univ.sum fun i => (data.capsule i).logVolume :=
  data.total_eq_sum

theorem normalized_eq
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    data.normalizedLogVolume =
      data.totalLogVolume / (data.capsuleCount : Real) :=
  data.normalized_eq_average

theorem capsuleCount_pos
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    0 < data.capsuleCount :=
  data.positive_capsule_count

def toCapsuleFamilyLogVolume
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    IUTStage1CapsuleFamilyLogVolume kind :=
  { localObject := data.localObject,
    capsuleCount := data.capsuleCount,
    positive_capsule_count := data.positive_capsule_count,
    capsuleLogVolume := fun i => (data.capsule i).logVolume,
    totalLogVolume := data.totalLogVolume,
    total_eq_sum := data.total_eq_sum,
    normalizedLogVolume := data.normalizedLogVolume,
    normalized_eq_average := data.normalized_eq_average }

theorem toCapsuleFamily_total_eq
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    data.toCapsuleFamilyLogVolume.totalLogVolume =
      Finset.univ.sum data.toCapsuleFamilyLogVolume.capsuleLogVolume :=
  data.toCapsuleFamilyLogVolume.total_eq

def toLabelAveragedCapsuleLogVolume
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) :
    IUTStage1LabelAveragedProcessionLogVolume (Fin data.capsuleCount) :=
  { normalizedLogVolume := fun i => (data.capsule i).logVolume,
    averageLogVolume := data.normalizedLogVolume,
    average_eq := by
      calc
        data.normalizedLogVolume =
            data.totalLogVolume / (data.capsuleCount : Real) :=
          data.normalized_eq
        _ =
            (Finset.univ.sum fun i => (data.capsule i).logVolume) /
              (data.capsuleCount : Real) := by
          rw [data.total_eq]
        _ =
            (Finset.univ.sum fun i => (data.capsule i).logVolume) /
              (Fintype.card (Fin data.capsuleCount) : Real) := by
          simp }

theorem const_le_normalizedLogVolume_of_capsule_le
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind)
    {c : Real}
    (hcapsule : ∀ i : Fin data.capsuleCount, c <= (data.capsule i).logVolume) :
    c <= data.normalizedLogVolume := by
  let averaged := data.toLabelAveragedCapsuleLogVolume
  haveI : Nonempty (Fin data.capsuleCount) :=
    ⟨⟨0, data.capsuleCount_pos⟩⟩
  exact
    IUTStage1LabelAveragedProcessionLogVolume.const_le_average_of_forall_le
      averaged hcapsule

end IUTStage1TypedCapsuleFamilyLogVolume

namespace IUTStage1TypedCapsuleFamilyContainerEstimate

variable {kind : IUTStage1PlaceKind}
variable {targetSigned : Real}
variable {data : IUTStage1TypedCapsuleFamilyLogVolume kind}

theorem targetSigned_le_capsuleLogVolume
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate targetSigned data)
    (i : Fin data.capsuleCount) :
    targetSigned <= (data.capsule i).logVolume :=
  (estimate.capsuleEntryEstimate i).targetSigned_le_capsuleLogVolume

theorem targetSigned_le_normalizedLogVolume
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate targetSigned data) :
    targetSigned <= data.normalizedLogVolume :=
  data.const_le_normalizedLogVolume_of_capsule_le
    estimate.targetSigned_le_capsuleLogVolume

end IUTStage1TypedCapsuleFamilyContainerEstimate

/--
An action on the indexed capsules of a typed capsule family that preserves each
individual capsule log-volume.

This is a conservative proxy for the local tensor-factor symmetries of
Theorem 3.11 `(Ind2)`: the action may replace capsule representatives, but it
does not change the finite index type, local object, or per-capsule log-volume.
-/
structure IUTStage1TypedCapsuleFamilyLogVolumeAction
    {kind : IUTStage1PlaceKind}
    (data : IUTStage1TypedCapsuleFamilyLogVolume kind) where
  capsule : Fin data.capsuleCount -> IUTStage1CapsuleLogVolumeObject kind
  capsule_local_object_eq :
    ∀ i : Fin data.capsuleCount, (capsule i).localObject = data.localObject
  logVolume_eq :
    ∀ i : Fin data.capsuleCount,
      (capsule i).logVolume = (data.capsule i).logVolume

namespace IUTStage1TypedCapsuleFamilyLogVolumeAction

variable {kind : IUTStage1PlaceKind}
variable {data : IUTStage1TypedCapsuleFamilyLogVolume kind}

def transformedFamily
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data) :
    IUTStage1TypedCapsuleFamilyLogVolume kind :=
  { localObject := data.localObject,
    capsuleCount := data.capsuleCount,
    positive_capsule_count := data.positive_capsule_count,
    capsule := action.capsule,
    capsule_local_object_eq := action.capsule_local_object_eq,
    totalLogVolume := data.totalLogVolume,
    total_eq_sum := by
      rw [data.total_eq_sum]
      exact Finset.sum_congr rfl
        (by
          intro i _hi
          exact (action.logVolume_eq i).symm),
    normalizedLogVolume := data.normalizedLogVolume,
    normalized_eq_average := data.normalized_eq_average }

theorem transformedFamily_capsuleCount
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data) :
    action.transformedFamily.capsuleCount = data.capsuleCount :=
  rfl

theorem transformedFamily_totalLogVolume
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data) :
    action.transformedFamily.totalLogVolume = data.totalLogVolume :=
  rfl

theorem transformedFamily_normalizedLogVolume
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data) :
    action.transformedFamily.normalizedLogVolume =
      data.normalizedLogVolume :=
  rfl

theorem transformedFamily_total_eq_sum
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data) :
    action.transformedFamily.totalLogVolume =
      Finset.univ.sum fun i =>
        (action.transformedFamily.capsule i).logVolume :=
  action.transformedFamily.total_eq

def transformedContainerEstimate
    {targetSigned : Real}
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate targetSigned data) :
    IUTStage1TypedCapsuleFamilyContainerEstimate
      targetSigned action.transformedFamily :=
  { capsuleEntryEstimate := by
      intro i
      exact
        (estimate.capsuleEntryEstimate i).transportCapsule
          (action.transformedFamily.capsule i)
          (action.logVolume_eq i)
          (by
            calc
              (estimate.capsuleEntryEstimate i).objectEstimate.localObject =
                  (data.capsule i).localObject :=
                (estimate.capsuleEntryEstimate i).localObject_eq_capsuleLocalObject'
              _ = data.localObject :=
                data.capsuleLocalObject_eq i
              _ = (action.transformedFamily.capsule i).localObject :=
                (action.capsule_local_object_eq i).symm) }

theorem transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    {targetSigned : Real}
    (action : IUTStage1TypedCapsuleFamilyLogVolumeAction data)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate targetSigned data) :
    targetSigned <= action.transformedFamily.normalizedLogVolume :=
  let transformedEstimate := action.transformedContainerEstimate estimate
  transformedEstimate.targetSigned_le_normalizedLogVolume

end IUTStage1TypedCapsuleFamilyLogVolumeAction

/--
The two local tensor symmetry sources singled out in Theorem 3.11 `(Ind2)`.
-/
inductive IUTStage1TensorSummandSymmetryKind where
  | nonarchimedeanIsm
  | archimedeanOrderTwo
deriving DecidableEq, Repr

namespace IUTStage1TensorSummandSymmetryKind

/--
Canonical local tensor symmetry label attached to the two typed `(Ind2)`
local tensor-factor actions.

The label is still an identifier, but this fixes the bridge between the paper
side action kind (`Ism` or order-two) and the local tensor symmetry coordinate.
-/
def toLocalTensorSymmetryId :
    IUTStage1TensorSummandSymmetryKind -> LocalTensorSymmetryId
  | nonarchimedeanIsm => { label := "nonarchimedean-Ism" }
  | archimedeanOrderTwo => { label := "archimedean-order-two" }

end IUTStage1TensorSummandSymmetryKind

/-- A direct summand representative tied to a capsule log-volume object. -/
structure IUTStage1TensorDirectSummandObject
    (kind : IUTStage1PlaceKind) where
  summandLabel : String
  localObject : IUTStage1FiniteLocalLogVolumeObject kind
  capsule : IUTStage1CapsuleLogVolumeObject kind
  capsule_local_object_eq : capsule.localObject = localObject

/--
Direct summand data indexed by the same finite type as a typed capsule family.

The shared index type is intentional: it records the current formalization
invariant that local tensor direct summands and capsule entries are counted
together, while avoiding an invalid identification of independently supplied
finite sets.
-/
structure IUTStage1TensorDirectSummandFamily
    {kind : IUTStage1PlaceKind}
    (capsuleFamily : IUTStage1TypedCapsuleFamilyLogVolume kind) where
  symmetryKind : IUTStage1TensorSummandSymmetryKind
  summand :
    Fin capsuleFamily.capsuleCount ->
      IUTStage1TensorDirectSummandObject kind
  summand_local_object_eq :
    ∀ i : Fin capsuleFamily.capsuleCount,
      (summand i).localObject = capsuleFamily.localObject
  summand_capsule_eq :
    ∀ i : Fin capsuleFamily.capsuleCount,
      (summand i).capsule = capsuleFamily.capsule i

namespace IUTStage1TensorDirectSummandObject

variable {kind : IUTStage1PlaceKind}

theorem capsuleLocalObject_eq
    (summand : IUTStage1TensorDirectSummandObject kind) :
    summand.capsule.localObject = summand.localObject :=
  summand.capsule_local_object_eq

theorem logVolume_eq_capsule
    (summand : IUTStage1TensorDirectSummandObject kind) :
    summand.capsule.logVolume = summand.localObject.finiteLogVolume := by
  calc
    summand.capsule.logVolume =
        summand.capsule.localObject.finiteLogVolume :=
      summand.capsule.logVolume_eq
    _ = summand.localObject.finiteLogVolume := by
      rw [summand.capsuleLocalObject_eq]

end IUTStage1TensorDirectSummandObject

namespace IUTStage1TensorDirectSummandFamily

variable {kind : IUTStage1PlaceKind}
variable {capsuleFamily : IUTStage1TypedCapsuleFamilyLogVolume kind}

theorem summandLocalObject_eq
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily)
    (i : Fin capsuleFamily.capsuleCount) :
    (family.summand i).localObject = capsuleFamily.localObject :=
  family.summand_local_object_eq i

theorem summandCapsule_eq
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily)
    (i : Fin capsuleFamily.capsuleCount) :
    (family.summand i).capsule = capsuleFamily.capsule i :=
  family.summand_capsule_eq i

theorem summandCapsuleLogVolume_eq
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily)
    (i : Fin capsuleFamily.capsuleCount) :
    (family.summand i).capsule.logVolume =
      (capsuleFamily.capsule i).logVolume := by
  rw [family.summandCapsule_eq i]

end IUTStage1TensorDirectSummandFamily

/--
Action on direct summand representatives that induces an action on capsule
representatives.
-/
structure IUTStage1TensorDirectSummandFamilyAction
    {kind : IUTStage1PlaceKind}
    {capsuleFamily : IUTStage1TypedCapsuleFamilyLogVolume kind}
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily) where
  transformedSummand :
    Fin capsuleFamily.capsuleCount ->
      IUTStage1TensorDirectSummandObject kind
  transformed_capsule_local_object_eq :
    ∀ i : Fin capsuleFamily.capsuleCount,
      (transformedSummand i).capsule.localObject = capsuleFamily.localObject
  transformed_capsule_logVolume_eq :
    ∀ i : Fin capsuleFamily.capsuleCount,
      (transformedSummand i).capsule.logVolume =
        (capsuleFamily.capsule i).logVolume

namespace IUTStage1TensorDirectSummandFamilyAction

variable {kind : IUTStage1PlaceKind}
variable {capsuleFamily : IUTStage1TypedCapsuleFamilyLogVolume kind}
variable {family : IUTStage1TensorDirectSummandFamily capsuleFamily}

def toCapsuleAction
    (action : IUTStage1TensorDirectSummandFamilyAction family) :
    IUTStage1TypedCapsuleFamilyLogVolumeAction capsuleFamily :=
  { capsule := fun i => (action.transformedSummand i).capsule,
    capsule_local_object_eq :=
      action.transformed_capsule_local_object_eq,
    logVolume_eq :=
      action.transformed_capsule_logVolume_eq }

theorem toCapsuleAction_totalLogVolume
    (action : IUTStage1TensorDirectSummandFamilyAction family) :
    action.toCapsuleAction.transformedFamily.totalLogVolume =
      capsuleFamily.totalLogVolume :=
  action.toCapsuleAction.transformedFamily_totalLogVolume

theorem toCapsuleAction_normalizedLogVolume
    (action : IUTStage1TensorDirectSummandFamilyAction family) :
    action.toCapsuleAction.transformedFamily.normalizedLogVolume =
      capsuleFamily.normalizedLogVolume :=
  action.toCapsuleAction.transformedFamily_normalizedLogVolume

def transformedContainerEstimate
    {targetSigned : Real}
    (action : IUTStage1TensorDirectSummandFamilyAction family)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned capsuleFamily) :
    IUTStage1TypedCapsuleFamilyContainerEstimate
      targetSigned action.toCapsuleAction.transformedFamily :=
  action.toCapsuleAction.transformedContainerEstimate estimate

theorem transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    {targetSigned : Real}
    (action : IUTStage1TensorDirectSummandFamilyAction family)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned capsuleFamily) :
    targetSigned <= action.toCapsuleAction.transformedFamily.normalizedLogVolume :=
  let capsuleAction := action.toCapsuleAction
  capsuleAction.transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    estimate

end IUTStage1TensorDirectSummandFamilyAction

/--
Nonarchimedean `Ism` action surface for Theorem 3.11 `(Ind2)`.

The actual `Ism` group is not yet constructed; this record isolates the
nonarchimedean case and requires the associated direct-summand action.
-/
structure IUTStage1NonarchimedeanIsmDirectSummandAction
    {capsuleFamily :
      IUTStage1TypedCapsuleFamilyLogVolume
        IUTStage1PlaceKind.nonarchimedean}
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily) where
  place : IUTStage1PlaceId IUTStage1PlaceKind.nonarchimedean
  symmetry_kind_eq :
    family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm
  action : IUTStage1TensorDirectSummandFamilyAction family

/--
Archimedean order-two action surface for Theorem 3.11 `(Ind2)`.

The actual order-two automorphism is not yet constructed; this record isolates
the archimedean case and requires the associated direct-summand action.
-/
structure IUTStage1ArchimedeanOrderTwoDirectSummandAction
    {capsuleFamily :
      IUTStage1TypedCapsuleFamilyLogVolume
        IUTStage1PlaceKind.archimedean}
    (family : IUTStage1TensorDirectSummandFamily capsuleFamily) where
  place : IUTStage1PlaceId IUTStage1PlaceKind.archimedean
  symmetry_kind_eq :
    family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo
  action : IUTStage1TensorDirectSummandFamilyAction family

namespace IUTStage1NonarchimedeanIsmDirectSummandAction

variable
  {capsuleFamily :
    IUTStage1TypedCapsuleFamilyLogVolume
      IUTStage1PlaceKind.nonarchimedean}
variable {family : IUTStage1TensorDirectSummandFamily capsuleFamily}

def toDirectSummandAction
    (data : IUTStage1NonarchimedeanIsmDirectSummandAction family) :
    IUTStage1TensorDirectSummandFamilyAction family :=
  data.action

theorem symmetryKind_eq
    (data : IUTStage1NonarchimedeanIsmDirectSummandAction family) :
    family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm :=
  data.symmetry_kind_eq

theorem capsuleTotalLogVolume_eq
    (data : IUTStage1NonarchimedeanIsmDirectSummandAction family) :
    data.toDirectSummandAction.toCapsuleAction.transformedFamily.totalLogVolume =
      capsuleFamily.totalLogVolume :=
  data.toDirectSummandAction.toCapsuleAction_totalLogVolume

theorem transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    {targetSigned : Real}
    (data : IUTStage1NonarchimedeanIsmDirectSummandAction family)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned capsuleFamily) :
    targetSigned <=
      data.toDirectSummandAction.toCapsuleAction.transformedFamily.normalizedLogVolume :=
  let action := data.toDirectSummandAction
  action.transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    estimate

end IUTStage1NonarchimedeanIsmDirectSummandAction

namespace IUTStage1ArchimedeanOrderTwoDirectSummandAction

variable
  {capsuleFamily :
    IUTStage1TypedCapsuleFamilyLogVolume IUTStage1PlaceKind.archimedean}
variable {family : IUTStage1TensorDirectSummandFamily capsuleFamily}

def toDirectSummandAction
    (data : IUTStage1ArchimedeanOrderTwoDirectSummandAction family) :
    IUTStage1TensorDirectSummandFamilyAction family :=
  data.action

theorem symmetryKind_eq
    (data : IUTStage1ArchimedeanOrderTwoDirectSummandAction family) :
    family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo :=
  data.symmetry_kind_eq

theorem capsuleTotalLogVolume_eq
    (data : IUTStage1ArchimedeanOrderTwoDirectSummandAction family) :
    data.toDirectSummandAction.toCapsuleAction.transformedFamily.totalLogVolume =
      capsuleFamily.totalLogVolume :=
  data.toDirectSummandAction.toCapsuleAction_totalLogVolume

theorem transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    {targetSigned : Real}
    (data : IUTStage1ArchimedeanOrderTwoDirectSummandAction family)
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned capsuleFamily) :
    targetSigned <=
      data.toDirectSummandAction.toCapsuleAction.transformedFamily.normalizedLogVolume :=
  let action := data.toDirectSummandAction
  action.transformedContainerEstimate_targetSigned_le_normalizedLogVolume
    estimate

end IUTStage1ArchimedeanOrderTwoDirectSummandAction

/-- A nonarchimedean `Ism` action entry in a place-family collection. -/
structure IUTStage1NonarchimedeanIsmActionEntry where
  capsuleFamily :
    IUTStage1TypedCapsuleFamilyLogVolume
      IUTStage1PlaceKind.nonarchimedean
  family : IUTStage1TensorDirectSummandFamily capsuleFamily
  action : IUTStage1NonarchimedeanIsmDirectSummandAction family

/-- An archimedean order-two action entry in a place-family collection. -/
structure IUTStage1ArchimedeanOrderTwoActionEntry where
  capsuleFamily :
    IUTStage1TypedCapsuleFamilyLogVolume IUTStage1PlaceKind.archimedean
  family : IUTStage1TensorDirectSummandFamily capsuleFamily
  action : IUTStage1ArchimedeanOrderTwoDirectSummandAction family

namespace IUTStage1NonarchimedeanIsmActionEntry

def place
    (entry : IUTStage1NonarchimedeanIsmActionEntry) :
    IUTStage1PlaceId IUTStage1PlaceKind.nonarchimedean :=
  entry.action.place

def toDirectSummandAction
    (entry : IUTStage1NonarchimedeanIsmActionEntry) :
    IUTStage1TensorDirectSummandFamilyAction entry.family :=
  entry.action.toDirectSummandAction

theorem symmetryKind_eq
    (entry : IUTStage1NonarchimedeanIsmActionEntry) :
    entry.family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm :=
  entry.action.symmetryKind_eq

theorem capsuleTotalLogVolume_eq
    (entry : IUTStage1NonarchimedeanIsmActionEntry) :
    entry.toDirectSummandAction.toCapsuleAction.transformedFamily.totalLogVolume =
      entry.capsuleFamily.totalLogVolume :=
  entry.action.capsuleTotalLogVolume_eq

end IUTStage1NonarchimedeanIsmActionEntry

namespace IUTStage1ArchimedeanOrderTwoActionEntry

def place
    (entry : IUTStage1ArchimedeanOrderTwoActionEntry) :
    IUTStage1PlaceId IUTStage1PlaceKind.archimedean :=
  entry.action.place

def toDirectSummandAction
    (entry : IUTStage1ArchimedeanOrderTwoActionEntry) :
    IUTStage1TensorDirectSummandFamilyAction entry.family :=
  entry.action.toDirectSummandAction

theorem symmetryKind_eq
    (entry : IUTStage1ArchimedeanOrderTwoActionEntry) :
    entry.family.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo :=
  entry.action.symmetryKind_eq

theorem capsuleTotalLogVolume_eq
    (entry : IUTStage1ArchimedeanOrderTwoActionEntry) :
    entry.toDirectSummandAction.toCapsuleAction.transformedFamily.totalLogVolume =
      entry.capsuleFamily.totalLogVolume :=
  entry.action.capsuleTotalLogVolume_eq

end IUTStage1ArchimedeanOrderTwoActionEntry

/--
Collection of `(Ind2)` local tensor-factor action data over the two place
families distinguished in Theorem 3.11.
-/
structure IUTStage1Ind2PlaceFamilyActionData where
  nonarchimedeanActions : List IUTStage1NonarchimedeanIsmActionEntry
  archimedeanActions : List IUTStage1ArchimedeanOrderTwoActionEntry

namespace IUTStage1Ind2PlaceFamilyActionData

def nonarchimedeanCount
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    Nat :=
  data.nonarchimedeanActions.length

def archimedeanCount
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    Nat :=
  data.archimedeanActions.length

def totalActionCount
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    Nat :=
  data.nonarchimedeanCount + data.archimedeanCount

theorem totalActionCount_eq
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    data.totalActionCount =
      data.nonarchimedeanActions.length + data.archimedeanActions.length :=
  rfl

def actionCountForKind
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    IUTStage1PlaceKind -> Nat
  | IUTStage1PlaceKind.nonarchimedean => data.nonarchimedeanCount
  | IUTStage1PlaceKind.archimedean => data.archimedeanCount

theorem actionCountForKind_nonarchimedean
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    data.actionCountForKind IUTStage1PlaceKind.nonarchimedean =
      data.nonarchimedeanActions.length :=
  rfl

theorem actionCountForKind_archimedean
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    data.actionCountForKind IUTStage1PlaceKind.archimedean =
      data.archimedeanActions.length :=
  rfl

def nonarchimedeanPlaces
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    List (IUTStage1PlaceId IUTStage1PlaceKind.nonarchimedean) :=
  data.nonarchimedeanActions.map
    IUTStage1NonarchimedeanIsmActionEntry.place

def archimedeanPlaces
    (data : IUTStage1Ind2PlaceFamilyActionData) :
    List (IUTStage1PlaceId IUTStage1PlaceKind.archimedean) :=
  data.archimedeanActions.map
    IUTStage1ArchimedeanOrderTwoActionEntry.place

end IUTStage1Ind2PlaceFamilyActionData

/--
Audit identifying the nonarchimedean `(Ind2)` action places with an explicit
fiber of places above a base place.
-/
structure IUTStage1NonarchimedeanInd2PlaceFiberAudit
    (data : IUTStage1Ind2PlaceFamilyActionData) where
  fiber : IUTStage1PlaceFiber IUTStage1PlaceKind.nonarchimedean
  places_eq : data.nonarchimedeanPlaces = fiber.places

/--
Audit identifying the archimedean `(Ind2)` action places with an explicit fiber
of places above a base place.
-/
structure IUTStage1ArchimedeanInd2PlaceFiberAudit
    (data : IUTStage1Ind2PlaceFamilyActionData) where
  fiber : IUTStage1PlaceFiber IUTStage1PlaceKind.archimedean
  places_eq : data.archimedeanPlaces = fiber.places

namespace IUTStage1NonarchimedeanInd2PlaceFiberAudit

variable {data : IUTStage1Ind2PlaceFamilyActionData}

theorem actionCount_eq_fiberCardinality
    (audit : IUTStage1NonarchimedeanInd2PlaceFiberAudit data) :
    data.nonarchimedeanCount = audit.fiber.cardinality := by
  rw [IUTStage1Ind2PlaceFamilyActionData.nonarchimedeanCount]
  unfold IUTStage1PlaceFiber.cardinality
  rw [← audit.places_eq]
  simp [IUTStage1Ind2PlaceFamilyActionData.nonarchimedeanPlaces]

end IUTStage1NonarchimedeanInd2PlaceFiberAudit

namespace IUTStage1ArchimedeanInd2PlaceFiberAudit

variable {data : IUTStage1Ind2PlaceFamilyActionData}

theorem actionCount_eq_fiberCardinality
    (audit : IUTStage1ArchimedeanInd2PlaceFiberAudit data) :
    data.archimedeanCount = audit.fiber.cardinality := by
  rw [IUTStage1Ind2PlaceFamilyActionData.archimedeanCount]
  unfold IUTStage1PlaceFiber.cardinality
  rw [← audit.places_eq]
  simp [IUTStage1Ind2PlaceFamilyActionData.archimedeanPlaces]

end IUTStage1ArchimedeanInd2PlaceFiberAudit

/-- Local nonarchimedean inclusion datum from the upper-semi-compatibility step. -/
structure IUTStage1NonarchimedeanInclusionData where
  place : IUTStage1PlaceId IUTStage1PlaceKind.nonarchimedean
  sourceObject : IUTStage1LocalObjectId IUTStage1PlaceKind.nonarchimedean
  targetObject : IUTStage1LocalObjectId IUTStage1PlaceKind.nonarchimedean
  sourceLogVolume :
    IUTStage1FiniteLocalLogVolumeObject IUTStage1PlaceKind.nonarchimedean
  targetLogVolume :
    IUTStage1FiniteLocalLogVolumeObject IUTStage1PlaceKind.nonarchimedean
  placeLabel : String
  sourceLabel : String
  targetLabel : String
  source_place_eq : sourceObject.place = place
  target_place_eq : targetObject.place = place
  source_log_volume_object_eq : sourceLogVolume.localObject.object = sourceObject
  target_log_volume_object_eq : targetLogVolume.localObject.object = targetObject
  source_logVolume_le_target_logVolume :
    sourceLogVolume.finiteLogVolume <= targetLogVolume.finiteLogVolume
  inclusionValid : Prop
  inclusion_valid : inclusionValid

/-- Local archimedean surjection datum from the upper-semi-compatibility step. -/
structure IUTStage1ArchimedeanSurjectionData where
  place : IUTStage1PlaceId IUTStage1PlaceKind.archimedean
  sourceObject : IUTStage1LocalObjectId IUTStage1PlaceKind.archimedean
  targetObject : IUTStage1LocalObjectId IUTStage1PlaceKind.archimedean
  sourceLogVolume :
    IUTStage1FiniteLocalLogVolumeObject IUTStage1PlaceKind.archimedean
  targetLogVolume :
    IUTStage1FiniteLocalLogVolumeObject IUTStage1PlaceKind.archimedean
  placeLabel : String
  sourceLabel : String
  targetLabel : String
  source_place_eq : sourceObject.place = place
  target_place_eq : targetObject.place = place
  source_log_volume_object_eq : sourceLogVolume.localObject.object = sourceObject
  target_log_volume_object_eq : targetLogVolume.localObject.object = targetObject
  target_logVolume_le_source_logVolume :
    targetLogVolume.finiteLogVolume <= sourceLogVolume.finiteLogVolume
  surjectionValid : Prop
  surjection_valid : surjectionValid

/--
One-sided log-volume compatibility datum for the upper-semi step.

The relation is intentionally an inequality, not definitional equality, because
the source discussion of upper semi-compatibility is precisely one-sided.
-/
structure IUTStage1LogVolumeCompatibilityData where
  sourceLogVolume : Real
  targetLogVolume : Real
  source_le_target : sourceLogVolume <= targetLogVolume

/--
Procession state used by the Theorem 3.11 `(Ind1)` model.

Automorphisms of the procession may change representative data, but the
procession label and column are the invariants retained by the current
formalization layer.
-/
structure IUTStage1ProcessionState where
  procession : ProcessionPrimeStripId
  column : Int
  representative : String

/--
Local tensor-packet state used by the Theorem 3.11 `(Ind2)` model.

The current layer records the symmetry orbit and the number of direct summands
without formalizing the local tensor packet itself.
-/
structure IUTStage1LocalTensorState where
  symmetry : LocalTensorSymmetryId
  directSummandCount : Nat
  representative : String

/--
Local tensor-packet state equipped with typed capsule log-volume data.

This is the first source-facing connection between the `(Ind2)` local
tensor-factor coordinate and the Proposition 3.9 capsule/log-volume
normalization.  The equality of direct summands and capsule count is recorded
as data because the underlying tensor-packet construction is not yet
formalized.
-/
structure IUTStage1LocalTensorPacketLogVolumeState
    (kind : IUTStage1PlaceKind) where
  tensorState : IUTStage1LocalTensorState
  localObject : IUTStage1FiniteLocalLogVolumeObject kind
  capsuleFamily : IUTStage1TypedCapsuleFamilyLogVolume kind
  direct_summand_count_eq_capsuleCount :
    tensorState.directSummandCount = capsuleFamily.capsuleCount
  capsule_family_localObject_eq :
    capsuleFamily.localObject = localObject

/--
Local tensor-packet state that also carries the direct summand family
responsible for the packet's capsule action surface.
-/
structure IUTStage1LocalTensorDirectSummandPacketState
    (kind : IUTStage1PlaceKind) where
  packetState : IUTStage1LocalTensorPacketLogVolumeState kind
  summandFamily :
    IUTStage1TensorDirectSummandFamily packetState.capsuleFamily

/--
Compatibility asserting that the normalized capsule-family log-volume of a
local tensor packet is the finite log-volume of its local object.

This is kept separate from `IUTStage1LocalTensorPacketLogVolumeState`: the base
state records that the capsule family is attached to the same local object,
while this certificate records the stronger real-line/log-volume
identification needed by packet-normalized container estimates.
-/
structure IUTStage1LocalTensorPacketNormalizedCompatibility
    {kind : IUTStage1PlaceKind}
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) where
  normalizedLogVolume_eq_localObject :
    state.capsuleFamily.normalizedLogVolume =
      state.localObject.finiteLogVolume

/-- Source classification for packet-normalized real-line identifications. -/
inductive IUTStage1PacketNormalizedIdentificationSource where
  | directPacketNormalization
  | ind2TransportedPacketNormalization
  | zmodLabelledProcessionAverage
  | logKummerVerticalIQCompatibility
  | separateRealLineIdentification
deriving DecidableEq

/-- Source classification for identifying cusp/zero log-volumes with the
packet local object's finite log-volume. -/
inductive IUTStage1LocalObjectLogVolumeIdentificationSource where
  | directLocalObjectConstruction
  | packetNormalizationAndLocalObjectCompatibility
  | separateRealLineIdentification
deriving DecidableEq

/-- Source classification for packet-local-object cusp/zero estimates. -/
inductive IUTStage1PacketLocalObjectEstimateSource where
  | directLocalCuspConstruction
  | ind2TransportedLocalCuspConstruction
  | separateLocalObjectEstimate
deriving DecidableEq

/-- Source classification for the bridge from the `ZMod l` averaged normalized
log-volume family to packet-normalized capsule-family values. -/
inductive IUTStage1ZModPacketNormalizedBridgeSource where
  | directLabelPacketNormalization
  | ind12TransportedLabelPacketNormalization
  | separateAveragingIdentification
deriving DecidableEq

/-- Source classification for identifying the `ZMod l` label family with the
packet local object's finite log-volume. -/
inductive IUTStage1ZModPacketLocalObjectBridgeSource where
  | directLocalLabelObjectConstruction
  | ind12TransportedLocalLabelObjectConstruction
  | hodgeTheaterDescentPacketTransport
  | separateLocalObjectIdentification
deriving DecidableEq

/--
Higher-level source classification for a bridge from the insulated cusp/zero
route to a packet-comparison route.

This distinguishes a merely constant `ZMod` comparison from a future
Hodge-theater/descent/indeterminacy bridge.
-/
inductive IUTStage1InsulatedCuspZeroBridgeSource where
  | directPacketNormalization
  | labelwiseZModPacketEquality
  | constantZModPacketFamily
  | hodgeTheaterDescentIndeterminacy
  | separateRealLineIdentification
deriving DecidableEq

/--
Per-audited local-object transport data for a Hodge-descent packet bridge.

The record keeps the zero-column checkpoint and history guard next to the local
object equalities that transport the insulated zero and nonzero cusp-class
objects to the packet local object.
-/
structure IUTStage1HodgeDescentLocalObjectTransportData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  checkpoint_eq_fourth_triangle :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint
  histories_not_identified :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side
  zero_transports_to_packet : zeroObject = packetObject
  cuspClass_transports_to_packet :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      cuspClassObject label = packetObject

/--
One local object operation in the Hodge-descent route.

This record names the descent operation from the Hodge-descent bridge data and
connects one source local object to one packet-side target local object.
-/
structure IUTStage1HodgeDescentLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (sourceObject packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  descent : AlgorithmicOutput.DescentOperationId
  descent_eq_hodgeData : descent = hodgeData.descent
  checkpoint_eq_fourth_triangle :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint
  histories_not_identified :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side
  source_transports_to_packet : sourceObject = packetObject

/--
Zero/cusp-class family of local object operations for a Hodge-descent packet
transport.
-/
structure IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  zeroOperation :
    IUTStage1HodgeDescentLocalObjectOperationData
      hodgeData zeroObject packetObject
  cuspClassOperation :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData (cuspClassObject label) packetObject

/--
Source/target roles for local objects in the Hodge-descent packet transport.
-/
inductive IUTStage1HodgeDescentLocalObjectRole where
  | zeroColumnSHEInput
  | cuspClassHodgeArakelovEvaluation
  | packetDescentTarget
deriving DecidableEq, Repr

/--
Local descent operation with the source and target object roles made explicit.
-/
structure IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (sourceObject packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  operation :
    IUTStage1HodgeDescentLocalObjectOperationData
      hodgeData sourceObject packetObject
  sourceRole : IUTStage1HodgeDescentLocalObjectRole
  targetRole : IUTStage1HodgeDescentLocalObjectRole
  target_role_eq_packet :
    targetRole = IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget

/--
Role-marked zero/cusp local descent-operation family.
-/
structure IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  zeroOperation :
    IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
      hodgeData zeroObject packetObject
  zero_source_role :
    zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput
  cuspClassOperation :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
        hodgeData (cuspClassObject label) packetObject
  cuspClass_source_role :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      (cuspClassOperation label).sourceRole =
        IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation

/--
Source object for the zero-column/SHE input side of a Hodge-descent local
transport.
-/
structure IUTStage1ZeroColumnSHELocalObjectData
    {kind : IUTStage1PlaceKind}
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (object : IUTStage1FiniteLocalLogVolumeObject kind) where
  checkpoint_eq_fourth_triangle :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint
  histories_not_identified :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side

/--
Source object for a nonzero cusp-class local Hodge-Arakelov evaluation input.
-/
structure IUTStage1CuspClassHodgeArakelovLocalObjectData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (label : (zmodSignAction l).SignLabelQuotient)
    (object : IUTStage1FiniteLocalLogVolumeObject kind) where
  checkpoint_eq_fourth_triangle :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint
  histories_not_identified :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side

/--
Target object on the packet side after Hodge descent.
-/
structure IUTStage1PacketDescentTargetLocalObjectData
    {kind : IUTStage1PlaceKind}
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (object : IUTStage1FiniteLocalLogVolumeObject kind) where
  descent : AlgorithmicOutput.DescentOperationId
  descent_eq_hodgeData : descent = hodgeData.descent
  checkpoint_eq_fourth_triangle :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint
  histories_not_identified :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side

/--
Role-marked zero/cusp local descent-operation family whose source and target
objects are identified with source-specific 0-column, Hodge-Arakelov, and packet
descent target data.
-/
structure IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  zeroSource :
    IUTStage1ZeroColumnSHELocalObjectData hodgeData zeroObject
  cuspClassSource :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1CuspClassHodgeArakelovLocalObjectData
        l hodgeData label (cuspClassObject label)
  packetTarget :
    IUTStage1PacketDescentTargetLocalObjectData hodgeData packetObject
  zeroOperation :
    IUTStage1HodgeDescentLocalObjectOperationData
      hodgeData zeroObject packetObject
  cuspClassOperation :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData (cuspClassObject label) packetObject

/--
Hodge-Arakelov cusp-class source object with explicit `ZMod l` label
provenance.

The coordinate is required to be nonzero because the cusp-class label lives in
the sign quotient of nonzero labels.
-/
structure IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (label : (zmodSignAction l).SignLabelQuotient)
    (object : IUTStage1FiniteLocalLogVolumeObject kind) where
  source :
    IUTStage1CuspClassHodgeArakelovLocalObjectData
      l hodgeData label object
  cuspLabelModel : IUTStage1FLZModCuspLabelClassModel l
  coordinate : ZMod l.value
  coordinate_ne_zero : coordinate ≠ 0
  label_eq_coordinate :
    label = zmodSignLabelFromCoordinate l coordinate coordinate_ne_zero

/--
Source-marked zero/cusp local operation data whose cusp-class sources are
tracked by explicit `ZMod l` sign-label coordinates.
-/
structure IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  zeroSource :
    IUTStage1ZeroColumnSHELocalObjectData hodgeData zeroObject
  cuspClassSource :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label (cuspClassObject label)
  packetTarget :
    IUTStage1PacketDescentTargetLocalObjectData hodgeData packetObject
  zeroOperation :
    IUTStage1HodgeDescentLocalObjectOperationData
      hodgeData zeroObject packetObject
  cuspClassOperation :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData (cuspClassObject label) packetObject

/--
Square-weight transport data that are not supplied by local-object Hodge descent
alone.

The local-object packet transport records zero/cusp local objects and their
descent to a packet object.  It does not by itself contain the coordinate and
weight-preservation data required by
`IUTStage1StructuredSHESquareWeightTransportObligations`.
-/
inductive IUTStage1SquareWeightTransportMissingDatum where
  | coordinateEquiv
  | sourceProfile
  | targetProfile
  | sourceLogVolume
  | targetLogVolume
  | fullLabelLogVolumePreservation
  | squareWeightPreservation
  | weightTotalPreservation
deriving DecidableEq, Repr, Fintype

namespace IUTStage1SquareWeightTransportMissingDatum

def all : Finset IUTStage1SquareWeightTransportMissingDatum :=
  Finset.univ

theorem coordinateEquiv_mem_all :
    coordinateEquiv ∈ all := by
  simp [all]

theorem sourceProfile_mem_all :
    sourceProfile ∈ all := by
  simp [all]

theorem targetProfile_mem_all :
    targetProfile ∈ all := by
  simp [all]

theorem sourceLogVolume_mem_all :
    sourceLogVolume ∈ all := by
  simp [all]

theorem targetLogVolume_mem_all :
    targetLogVolume ∈ all := by
  simp [all]

theorem fullLabelLogVolumePreservation_mem_all :
    fullLabelLogVolumePreservation ∈ all := by
  simp [all]

theorem squareWeightPreservation_mem_all :
    squareWeightPreservation ∈ all := by
  simp [all]

theorem weightTotalPreservation_mem_all :
    weightTotalPreservation ∈ all := by
  simp [all]

end IUTStage1SquareWeightTransportMissingDatum

/--
Real comparison datum still needed when the square-weighted average route is
used to feed the final Theta-source bound.

This is deliberately separate from the pointwise square/full-label transport
missing data: even after local bounds give `qSigned <= squareWeightedAverage`,
one still needs an explicit real inequality comparing that weighted average to
the Theta-source average.
-/
inductive IUTStage1WeightedThetaComparisonMissingDatum where
  | weightedAverage_le_thetaAverage
deriving DecidableEq, Repr, Fintype

namespace IUTStage1WeightedThetaComparisonMissingDatum

def all : Finset IUTStage1WeightedThetaComparisonMissingDatum :=
  Finset.univ

def comparisonLevel
    (_datum : IUTStage1WeightedThetaComparisonMissingDatum) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.hullLogVolume

theorem comparisonLevel_eq_hullLogVolume
    (datum : IUTStage1WeightedThetaComparisonMissingDatum) :
    datum.comparisonLevel =
      IUTStage1SquareComparisonLevel.hullLogVolume :=
  rfl

theorem comparisonLevel_ne_pointwiseRepresentative
    (datum : IUTStage1WeightedThetaComparisonMissingDatum) :
    datum.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_aggregateRepresentative
    (datum : IUTStage1WeightedThetaComparisonMissingDatum) :
    datum.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.aggregateRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem comparisonLevel_ne_balancedSignCompatible
    (datum : IUTStage1WeightedThetaComparisonMissingDatum) :
    datum.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.balancedSignCompatible :=
  IUTStage1SquareComparisonLevel.hull_ne_balanced

theorem weightedAverage_le_thetaAverage_mem_all :
    weightedAverage_le_thetaAverage ∈ all := by
  simp [all]

end IUTStage1WeightedThetaComparisonMissingDatum

/--
Source label for the supplied weighted-theta real comparison.

This is not a proof by itself.  It records which source-facing part of the
IUT III 3.11-to-3.12 corridor is being used to justify the real inequality
between the square-weighted average and the Theta-source average.
-/
inductive IUTStage1WeightedThetaComparisonSource where
  | threeElevenFiveToCorollary312
  | inputPrimeStripLink
  | separateAnalyticComparison
deriving DecidableEq, Repr

namespace IUTStage1WeightedThetaComparisonSource

def comparisonLevel
    (_source : IUTStage1WeightedThetaComparisonSource) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.hullLogVolume

theorem comparisonLevel_eq_hullLogVolume
    (source : IUTStage1WeightedThetaComparisonSource) :
    source.comparisonLevel =
      IUTStage1SquareComparisonLevel.hullLogVolume :=
  rfl

theorem comparisonLevel_ne_pointwiseRepresentative
    (source : IUTStage1WeightedThetaComparisonSource) :
    source.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_aggregateRepresentative
    (source : IUTStage1WeightedThetaComparisonSource) :
    source.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.aggregateRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem comparisonLevel_ne_balancedSignCompatible
    (source : IUTStage1WeightedThetaComparisonSource) :
    source.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.balancedSignCompatible :=
  IUTStage1SquareComparisonLevel.hull_ne_balanced

end IUTStage1WeightedThetaComparisonSource

/--
Primitive preservation data required by the fully factored structured-SHE
square/full-label obligation record, but not supplied by local-object Hodge
descent alone.
-/
inductive IUTStage1FactoredSquareFullLabelMissingDatum where
  | coordinateSquarePreservation
  | fullLabelMapPreservation
  | fullLabelValuePreservation
deriving DecidableEq, Repr, Fintype

namespace IUTStage1FactoredSquareFullLabelMissingDatum

def all : Finset IUTStage1FactoredSquareFullLabelMissingDatum :=
  Finset.univ

theorem coordinateSquarePreservation_mem_all :
    coordinateSquarePreservation ∈ all := by
  simp [all]

theorem fullLabelMapPreservation_mem_all :
    fullLabelMapPreservation ∈ all := by
  simp [all]

theorem fullLabelValuePreservation_mem_all :
    fullLabelValuePreservation ∈ all := by
  simp [all]

end IUTStage1FactoredSquareFullLabelMissingDatum

/--
Transport data that preserves only the zero/nonzero/sign-quotient full-label
map.

This is intentionally weaker than the factored square/full-label preservation
interface: it carries no coordinate-square preservation and no log-volume value
preservation.
-/
structure IUTStage1FullLabelMapOnlyTransport
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  fullLabelMap_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) coordinateEquiv

namespace IUTStage1FullLabelMapOnlyTransport

variable {l : PrimeGeFive}

def neg (l : PrimeGeFive) :
    IUTStage1FullLabelMapOnlyTransport l :=
  { coordinateEquiv := Equiv.neg (ZMod l.value),
    fullLabelMap_preserved :=
      IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_neg }

def missingFactoredSquareFullLabelData
    (_transport : IUTStage1FullLabelMapOnlyTransport l) :
    Finset IUTStage1FactoredSquareFullLabelMissingDatum :=
  { IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation,
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation }

theorem fullLabelMapPreserved
    (transport : IUTStage1FullLabelMapOnlyTransport l) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) transport.coordinateEquiv :=
  transport.fullLabelMap_preserved

theorem coordinateSquarePreservation_missing
    (transport : IUTStage1FullLabelMapOnlyTransport l) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      transport.missingFactoredSquareFullLabelData := by
  simp [missingFactoredSquareFullLabelData]

theorem fullLabelValuePreservation_missing
    (transport : IUTStage1FullLabelMapOnlyTransport l) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      transport.missingFactoredSquareFullLabelData := by
  simp [missingFactoredSquareFullLabelData]

end IUTStage1FullLabelMapOnlyTransport

/--
Transport data that preserves the sign-quotient full-label map and the square
map inside `ZMod l.value`, but not the real representative square profile.

This records the distinction between finite-field square compatibility and the
real `j.val ^ 2` weights used in the current Corollary 3.12 audit target.
-/
structure IUTStage1FullLabelModularSquareOnlyTransport
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  fullLabelMap_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) coordinateEquiv
  coordinateModularSquare_preserved :
    IUTStage1ZModSquareWeightProfile.CoordinateModularSquarePreserving
      (l := l) coordinateEquiv

namespace IUTStage1FullLabelModularSquareOnlyTransport

variable {l : PrimeGeFive}

def neg (l : PrimeGeFive) :
    IUTStage1FullLabelModularSquareOnlyTransport l :=
  { coordinateEquiv := Equiv.neg (ZMod l.value),
    fullLabelMap_preserved :=
      IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_neg,
    coordinateModularSquare_preserved :=
      IUTStage1ZModSquareWeightProfile.coordinateModularSquarePreserving_neg }

def missingFactoredSquareFullLabelData
    (_transport : IUTStage1FullLabelModularSquareOnlyTransport l) :
    Finset IUTStage1FactoredSquareFullLabelMissingDatum :=
  { IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation,
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation }

theorem fullLabelMapPreserved
    (transport : IUTStage1FullLabelModularSquareOnlyTransport l) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) transport.coordinateEquiv :=
  transport.fullLabelMap_preserved

theorem coordinateModularSquarePreserved
    (transport : IUTStage1FullLabelModularSquareOnlyTransport l) :
    IUTStage1ZModSquareWeightProfile.CoordinateModularSquarePreserving
      (l := l) transport.coordinateEquiv :=
  transport.coordinateModularSquare_preserved

theorem coordinateSquarePreservation_missing
    (transport : IUTStage1FullLabelModularSquareOnlyTransport l) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      transport.missingFactoredSquareFullLabelData := by
  simp [missingFactoredSquareFullLabelData]

theorem fullLabelValuePreservation_missing
    (transport : IUTStage1FullLabelModularSquareOnlyTransport l) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      transport.missingFactoredSquareFullLabelData := by
  simp [missingFactoredSquareFullLabelData]

theorem neg_not_representativeSummand_constant_one_preserved
    (l : PrimeGeFive) :
    ¬ ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) ((neg l).coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j := by
  simpa [neg] using
    IUTStage1ZModSquareWeightProfile.not_representativeSummand_constant_one_preserved_neg
      (l := l)

open IUTStage1ZModSquareWeightProfile in
theorem neg_representativeSummand_constant_one_total_preserved
    (l : PrimeGeFive) :
    (Finset.univ.sum fun j : ZMod l.value =>
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
          (l := l) (1 : Real)) ((neg l).coordinateEquiv j)) =
      Finset.univ.sum fun j : ZMod l.value =>
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j := by
  simpa [neg] using
    representativeSummand_constant_one_total_preserved_neg (l := l)

theorem neg_total_preserved_and_pointwise_fails
    (l : PrimeGeFive) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
          (l := l) (1 : Real)) ((neg l).coordinateEquiv j)) =
      Finset.univ.sum fun j : ZMod l.value =>
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j) ∧
      ¬ ∀ j : ZMod l.value,
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) ((neg l).coordinateEquiv j) =
          IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) j :=
  ⟨neg_representativeSummand_constant_one_total_preserved l,
    neg_not_representativeSummand_constant_one_preserved l⟩

end IUTStage1FullLabelModularSquareOnlyTransport

/--
Balanced-square/full-label transport data.

This is an alternate sign-compatible branch: it uses the balanced square profile
`valMinAbs.natAbs ^ 2`, not the representative-valued Corollary 3.12 audit
profile `j.val ^ 2`.
-/
structure IUTStage1BalancedSquareFullLabelTransport
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  sourceLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  targetLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  coordinateBalancedSquare_preserved :
    IUTStage1ZModSquareWeightProfile.CoordinateBalancedSquarePreserving
      (l := l) coordinateEquiv
  fullLabelMap_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) coordinateEquiv
  fullLabelValue_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
      sourceLogVolume targetLogVolume

namespace IUTStage1BalancedSquareFullLabelTransport

variable {l : PrimeGeFive}

def comparisonLevel
    (_transport : IUTStage1BalancedSquareFullLabelTransport l) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.balancedSignCompatible

theorem comparisonLevel_ne_pointwiseRepresentative
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    transport.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  IUTStage1SquareComparisonLevel.balanced_ne_pointwise

def negSelf
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    IUTStage1BalancedSquareFullLabelTransport l :=
  { coordinateEquiv := Equiv.neg (ZMod l.value),
    sourceLogVolume := logVolume,
    targetLogVolume := logVolume,
    coordinateBalancedSquare_preserved :=
      IUTStage1ZModSquareWeightProfile.coordinateBalancedSquarePreserving_neg,
    fullLabelMap_preserved :=
      IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_neg,
    fullLabelValue_preserved :=
      IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelLogVolumeValuePreserving_refl
        logVolume }

theorem balancedSquareWeight_preserved
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.balancedSquareWeight
          (l := l) (transport.coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.balancedSquareWeight
          (l := l) j :=
  transport.coordinateBalancedSquare_preserved

theorem fullLabelLogVolume_preserved
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    ∀ j : ZMod l.value,
      transport.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (transport.coordinateEquiv j)) =
        transport.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  by
    intro j
    rw [transport.fullLabelMap_preserved j]
    exact transport.fullLabelValue_preserved
      (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem balancedSummand_preserved
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.balancedSquareWeight
          (l := l) (transport.coordinateEquiv j) *
        transport.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (transport.coordinateEquiv j)) =
      IUTStage1ZModSquareWeightProfile.balancedSquareWeight
          (l := l) j *
        transport.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  rw [transport.balancedSquareWeight_preserved j,
    transport.fullLabelLogVolume_preserved j]

theorem balancedFullLabelWeightedSummand_preserved
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.balancedFullLabelWeightedSummand
          (l := l) transport.targetLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (transport.coordinateEquiv j)) =
        IUTStage1ZModSquareWeightProfile.balancedFullLabelWeightedSummand
          (l := l) transport.sourceLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  IUTStage1ZModSquareWeightProfile.balancedFullLabelWeightedSummand_preserved_of_fullLabelMap
      transport.fullLabelMap_preserved
      transport.sourceLogVolume
      transport.targetLogVolume
      transport.fullLabelValue_preserved

def balancedWeightTotal
    (_transport : IUTStage1BalancedSquareFullLabelTransport l) :
    Real :=
  Finset.univ.sum fun j : ZMod l.value =>
    IUTStage1ZModSquareWeightProfile.balancedSquareWeight (l := l) j

def sourceBalancedNumerator
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    Real :=
  Finset.univ.sum fun j : ZMod l.value =>
    IUTStage1ZModSquareWeightProfile.balancedSquareWeight (l := l) j *
      transport.sourceLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

def targetTransportedBalancedNumerator
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    Real :=
  Finset.univ.sum fun j : ZMod l.value =>
    IUTStage1ZModSquareWeightProfile.balancedSquareWeight
        (l := l) (transport.coordinateEquiv j) *
      transport.targetLogVolume.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (transport.coordinateEquiv j))

noncomputable def sourceBalancedAverage
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    Real :=
  transport.sourceBalancedNumerator / transport.balancedWeightTotal

noncomputable def targetTransportedBalancedAverage
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    Real :=
  transport.targetTransportedBalancedNumerator /
    transport.balancedWeightTotal

theorem targetTransportedBalancedNumerator_eq_sourceBalancedNumerator
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    transport.targetTransportedBalancedNumerator =
      transport.sourceBalancedNumerator := by
  unfold targetTransportedBalancedNumerator sourceBalancedNumerator
  exact Finset.sum_congr rfl (by
    intro j _hj
    exact transport.balancedSummand_preserved j)

theorem targetTransportedBalancedAverage_eq_sourceBalancedAverage
    (transport : IUTStage1BalancedSquareFullLabelTransport l) :
    transport.targetTransportedBalancedAverage =
      transport.sourceBalancedAverage := by
  unfold targetTransportedBalancedAverage sourceBalancedAverage
  rw [transport.targetTransportedBalancedNumerator_eq_sourceBalancedNumerator]

theorem negSelf_not_representativeSummand_constant_one_preserved
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    ¬ ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real))
          ((negSelf logVolume).coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real))
          j := by
  simpa [negSelf] using
    IUTStage1ZModSquareWeightProfile.not_representativeSummand_constant_one_preserved_neg
      (l := l)

theorem negSelf_balanced_preserved_and_representative_fails
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    (∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.balancedSquareWeight
          (l := l) ((negSelf logVolume).coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.balancedSquareWeight (l := l) j) ∧
      ¬ ∀ j : ZMod l.value,
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real))
            ((negSelf logVolume).coordinateEquiv j) =
          IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real))
            j :=
  ⟨(negSelf logVolume).balancedSquareWeight_preserved,
    negSelf_not_representativeSummand_constant_one_preserved logVolume⟩

theorem negSelf_gaussian_balanced_preserved_and_representative_fails
    (evaluation :
      IUTStage1ZModSquareWeightProfile.GaussianMonoidDegreeEvaluation l)
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    (∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            ((negSelf logVolume).coordinateEquiv j)) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      (∀ j : ZMod l.value,
        IUTStage1ZModSquareWeightProfile.balancedSquareWeight
            (l := l) ((negSelf logVolume).coordinateEquiv j) =
          IUTStage1ZModSquareWeightProfile.balancedSquareWeight
            (l := l) j) ∧
      ¬ ∀ j : ZMod l.value,
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real))
            ((negSelf logVolume).coordinateEquiv j) =
          IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real))
            j := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · simp [negSelf, hj]
    · simpa [negSelf] using
        evaluation.gaussianDegree_neg_fromCoordinate_eq j hj
  · exact (negSelf logVolume).balancedSquareWeight_preserved
  · exact negSelf_not_representativeSummand_constant_one_preserved logVolume

end IUTStage1BalancedSquareFullLabelTransport

/--
Boundary object showing what the local-object Hodge-descent packet layer supplies
before square-weight preservation data are added.

It carries the existing local-object transport data and exposes the packet
equalities, while the `missingSquareWeightData` checklist records the extra
coordinate/profile/preservation data still needed to construct the
structured-SHE square-weight transport obligations.
-/
structure IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
    {kind : IUTStage1PlaceKind}
    (l : PrimeGeFive)
    (hodgeData : IUTStage1HodgeTheaterDescentBridgeData)
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (packetObject : IUTStage1FiniteLocalLogVolumeObject kind) where
  localObjectTransport :
    IUTStage1HodgeDescentLocalObjectTransportData
      l hodgeData zeroObject cuspClassObject packetObject

namespace IUTStage1LocalObjectHodgeDescentSquareWeightBoundary

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def missingSquareWeightData
    (_boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    Finset IUTStage1SquareWeightTransportMissingDatum :=
  IUTStage1SquareWeightTransportMissingDatum.all

def missingFactoredSquareFullLabelData
    (_boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    Finset IUTStage1FactoredSquareFullLabelMissingDatum :=
  IUTStage1FactoredSquareFullLabelMissingDatum.all

theorem zero_transports_to_packet
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    zeroObject = packetObject :=
  boundary.localObjectTransport.zero_transports_to_packet

theorem cuspClass_transports_to_packet
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    cuspClassObject label = packetObject :=
  boundary.localObjectTransport.cuspClass_transports_to_packet label

theorem zero_finiteLogVolume_eq_packet
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    zeroObject.finiteLogVolume = packetObject.finiteLogVolume := by
  rw [boundary.zero_transports_to_packet]

theorem cuspClass_finiteLogVolume_eq_packet
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (cuspClassObject label).finiteLogVolume = packetObject.finiteLogVolume := by
  rw [boundary.cuspClass_transports_to_packet label]

theorem zero_finiteLogVolume_eq_cuspClass
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject.finiteLogVolume =
      (cuspClassObject label).finiteLogVolume := by
  rw [boundary.zero_finiteLogVolume_eq_packet,
    boundary.cuspClass_finiteLogVolume_eq_packet label]

theorem histories_not_identified
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    hodgeData.domainTheater.side ≠ hodgeData.codomainTheater.side :=
  boundary.localObjectTransport.histories_not_identified

theorem coordinateEquiv_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1SquareWeightTransportMissingDatum.coordinateEquiv ∈
      boundary.missingSquareWeightData :=
  IUTStage1SquareWeightTransportMissingDatum.coordinateEquiv_mem_all

theorem fullLabelLogVolumePreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1SquareWeightTransportMissingDatum.fullLabelLogVolumePreservation ∈
      boundary.missingSquareWeightData :=
  IUTStage1SquareWeightTransportMissingDatum.fullLabelLogVolumePreservation_mem_all

theorem squareWeightPreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1SquareWeightTransportMissingDatum.squareWeightPreservation ∈
      boundary.missingSquareWeightData :=
  IUTStage1SquareWeightTransportMissingDatum.squareWeightPreservation_mem_all

theorem weightTotalPreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1SquareWeightTransportMissingDatum.weightTotalPreservation ∈
      boundary.missingSquareWeightData :=
  IUTStage1SquareWeightTransportMissingDatum.weightTotalPreservation_mem_all

theorem coordinateSquarePreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation_mem_all

theorem fullLabelMapPreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation_mem_all

theorem fullLabelValuePreservation_missing
    (boundary :
      IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation_mem_all

end IUTStage1LocalObjectHodgeDescentSquareWeightBoundary

namespace IUTStage1HodgeDescentLocalObjectTransportData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

theorem zero_transports_to_packet'
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject) :
    zeroObject = packetObject :=
  data.zero_transports_to_packet

theorem cuspClass_transports_to_packet'
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    cuspClassObject label = packetObject :=
  data.cuspClass_transports_to_packet label

theorem zero_eq_cuspClass
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject = cuspClassObject label :=
  data.zero_transports_to_packet.trans
    (data.cuspClass_transports_to_packet label).symm

theorem zero_finiteLogVolume_eq_packet
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject) :
    zeroObject.finiteLogVolume = packetObject.finiteLogVolume := by
  rw [data.zero_transports_to_packet]

theorem cuspClass_finiteLogVolume_eq_packet
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (cuspClassObject label).finiteLogVolume = packetObject.finiteLogVolume := by
  rw [data.cuspClass_transports_to_packet label]

theorem zero_finiteLogVolume_eq_cuspClass
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject.finiteLogVolume =
      (cuspClassObject label).finiteLogVolume := by
  rw [data.zero_finiteLogVolume_eq_packet,
    data.cuspClass_finiteLogVolume_eq_packet label]

theorem checkpoint_eq_fourthTriangle
    (data :
      IUTStage1HodgeDescentLocalObjectTransportData
        l hodgeData zeroObject cuspClassObject packetObject) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.checkpoint_eq_fourth_triangle

end IUTStage1HodgeDescentLocalObjectTransportData

namespace IUTStage1HodgeDescentLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {sourceObject packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

theorem descent_eq
    (data :
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    data.descent = hodgeData.descent :=
  data.descent_eq_hodgeData

theorem checkpoint_eq_fourthTriangle
    (data :
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.checkpoint_eq_fourth_triangle

theorem source_transports_to_packet'
    (data :
      IUTStage1HodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    sourceObject = packetObject :=
  data.source_transports_to_packet

end IUTStage1HodgeDescentLocalObjectOperationData

namespace IUTStage1HodgeDescentCuspZeroLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def toLocalObjectTransportData
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1HodgeDescentLocalObjectTransportData
      l hodgeData zeroObject cuspClassObject packetObject :=
  { checkpoint_eq_fourth_triangle :=
      data.zeroOperation.checkpoint_eq_fourthTriangle,
    histories_not_identified :=
      data.zeroOperation.histories_not_identified,
    zero_transports_to_packet :=
      data.zeroOperation.source_transports_to_packet',
    cuspClass_transports_to_packet := fun label =>
      (data.cuspClassOperation label).source_transports_to_packet' }

theorem zero_transports_to_packet
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    zeroObject = packetObject :=
  data.zeroOperation.source_transports_to_packet'

theorem cuspClass_transports_to_packet
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    cuspClassObject label = packetObject :=
  (data.cuspClassOperation label).source_transports_to_packet'

theorem zero_eq_cuspClass
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject = cuspClassObject label :=
  data.toLocalObjectTransportData.zero_eq_cuspClass label

theorem zeroOperation_descent_eq_hodgeData
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.zeroOperation.descent = hodgeData.descent :=
  data.zeroOperation.descent_eq

theorem cuspClassOperation_descent_eq_hodgeData
    (data :
      IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (data.cuspClassOperation label).descent = hodgeData.descent :=
  (data.cuspClassOperation label).descent_eq

end IUTStage1HodgeDescentCuspZeroLocalObjectOperationData

namespace IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {sourceObject packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def toLocalObjectOperationData
    (data :
      IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    IUTStage1HodgeDescentLocalObjectOperationData
      hodgeData sourceObject packetObject :=
  data.operation

theorem source_transports_to_packet
    (data :
      IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    sourceObject = packetObject :=
  data.operation.source_transports_to_packet'

theorem targetRole_eq_packet
    (data :
      IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    data.targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  data.target_role_eq_packet

theorem descent_eq_hodgeData
    (data :
      IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData
        hodgeData sourceObject packetObject) :
    data.operation.descent = hodgeData.descent :=
  data.operation.descent_eq

end IUTStage1RoleMarkedHodgeDescentLocalObjectOperationData

namespace IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def toCuspZeroLocalObjectOperationData
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
      l hodgeData zeroObject cuspClassObject packetObject :=
  { zeroOperation := data.zeroOperation.toLocalObjectOperationData,
    cuspClassOperation := fun label =>
      (data.cuspClassOperation label).toLocalObjectOperationData }

def toLocalObjectTransportData
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1HodgeDescentLocalObjectTransportData
      l hodgeData zeroObject cuspClassObject packetObject :=
  data.toCuspZeroLocalObjectOperationData.toLocalObjectTransportData

theorem zeroSourceRole_eq
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput :=
  data.zero_source_role

theorem cuspClassSourceRole_eq
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (data.cuspClassOperation label).sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation :=
  data.cuspClass_source_role label

theorem zeroTargetRole_eq_packet
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.zeroOperation.targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  data.zeroOperation.targetRole_eq_packet

theorem cuspClassTargetRole_eq_packet
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (data.cuspClassOperation label).targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  (data.cuspClassOperation label).targetRole_eq_packet

theorem zero_eq_cuspClass
    (data :
      IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject = cuspClassObject label :=
  data.toCuspZeroLocalObjectOperationData.zero_eq_cuspClass label

end IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData

namespace IUTStage1ZeroColumnSHELocalObjectData

variable {kind : IUTStage1PlaceKind}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {object : IUTStage1FiniteLocalLogVolumeObject kind}

theorem checkpoint_eq_fourthTriangle
    (data : IUTStage1ZeroColumnSHELocalObjectData hodgeData object) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.checkpoint_eq_fourth_triangle

end IUTStage1ZeroColumnSHELocalObjectData

namespace IUTStage1CuspClassHodgeArakelovLocalObjectData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {label : (zmodSignAction l).SignLabelQuotient}
variable {object : IUTStage1FiniteLocalLogVolumeObject kind}

theorem checkpoint_eq_fourthTriangle
    (data :
      IUTStage1CuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.checkpoint_eq_fourth_triangle

end IUTStage1CuspClassHodgeArakelovLocalObjectData

namespace IUTStage1PacketDescentTargetLocalObjectData

variable {kind : IUTStage1PlaceKind}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {object : IUTStage1FiniteLocalLogVolumeObject kind}

theorem descent_eq
    (data : IUTStage1PacketDescentTargetLocalObjectData hodgeData object) :
    data.descent = hodgeData.descent :=
  data.descent_eq_hodgeData

theorem checkpoint_eq_fourthTriangle
    (data : IUTStage1PacketDescentTargetLocalObjectData hodgeData object) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.checkpoint_eq_fourth_triangle

end IUTStage1PacketDescentTargetLocalObjectData

namespace IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def toRoleMarkedCuspZeroLocalObjectOperationData
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
      l hodgeData zeroObject cuspClassObject packetObject :=
  { zeroOperation :=
      { operation := data.zeroOperation,
        sourceRole :=
          IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput,
        targetRole :=
          IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget,
        target_role_eq_packet := rfl },
    zero_source_role := rfl,
    cuspClassOperation := fun label =>
      { operation := data.cuspClassOperation label,
        sourceRole :=
          IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation,
        targetRole :=
          IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget,
        target_role_eq_packet := rfl },
    cuspClass_source_role := fun _label => rfl }

def toCuspZeroLocalObjectOperationData
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1HodgeDescentCuspZeroLocalObjectOperationData
      l hodgeData zeroObject cuspClassObject packetObject :=
  { zeroOperation := data.zeroOperation,
    cuspClassOperation := data.cuspClassOperation }

theorem zeroSource_checkpoint_eq_fourthTriangle
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  data.zeroSource.checkpoint_eq_fourthTriangle

theorem packetTarget_descent_eq_hodgeData
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.packetTarget.descent = hodgeData.descent :=
  data.packetTarget.descent_eq

theorem cuspClassSource_checkpoint_eq_fourthTriangle
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    hodgeData.zeroColumnCheckpoint = fourthTriangleHDDSHECheckpoint :=
  (data.cuspClassSource label).checkpoint_eq_fourthTriangle

theorem zero_eq_cuspClass
    (data :
      IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject = cuspClassObject label :=
  data.toCuspZeroLocalObjectOperationData.zero_eq_cuspClass label

end IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData

namespace IUTStage1ZModCuspClassHodgeArakelovLocalObjectData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {label : (zmodSignAction l).SignLabelQuotient}
variable {object : IUTStage1FiniteLocalLogVolumeObject kind}

def toCuspClassHodgeArakelovLocalObjectData
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    IUTStage1CuspClassHodgeArakelovLocalObjectData
      l hodgeData label object :=
  data.source

theorem label_eq_zmodCoordinate
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    label = zmodSignLabelFromCoordinate l data.coordinate data.coordinate_ne_zero :=
  data.label_eq_coordinate

theorem label_eq_negCoordinate
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    label =
      zmodSignLabelFromCoordinate l (-data.coordinate)
        (zmod_neg_ne_zero_of_ne_zero l data.coordinate_ne_zero) := by
  calc
    label = zmodSignLabelFromCoordinate l data.coordinate data.coordinate_ne_zero :=
      data.label_eq_zmodCoordinate
    _ = zmodSignLabelFromCoordinate l (-data.coordinate)
          (zmod_neg_ne_zero_of_ne_zero l data.coordinate_ne_zero) :=
      (zmodSignLabelFromCoordinate_neg_eq l data.coordinate data.coordinate_ne_zero).symm

theorem label_eq_canonical_of_coordinate_eq_one
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object)
    (hcoord : data.coordinate = (1 : ZMod l.value)) :
    label = zmodCanonicalSignLabelQuotient l := by
  have hnonzero_one : (1 : ZMod l.value) ≠ 0 := by
    simpa [hcoord] using data.coordinate_ne_zero
  have hnonzero_one_eq :
      hnonzero_one = (zmodOneNonzeroLabel l).2 := by
    apply Subsingleton.elim
  calc
    label = zmodSignLabelFromCoordinate l data.coordinate data.coordinate_ne_zero :=
      data.label_eq_zmodCoordinate
    _ = zmodSignLabelFromCoordinate l (1 : ZMod l.value) hnonzero_one := by
      simp [hcoord]
    _ = zmodSignLabelFromCoordinate l (1 : ZMod l.value)
          (zmodOneNonzeroLabel l).2 := by
      rw [hnonzero_one_eq]
    _ = zmodCanonicalSignLabelQuotient l :=
      zmodSignLabelFromCoordinate_one_eq_canonical l

theorem coordinate_ne_zero'
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    data.coordinate ≠ 0 :=
  data.coordinate_ne_zero

theorem cuspLabelModel_localLabCuspModel_eq_zmod
    (data :
      IUTStage1ZModCuspClassHodgeArakelovLocalObjectData
        l hodgeData label object) :
    data.cuspLabelModel.local_lab_cusp_model = zmodLocalLabCuspModel l :=
  data.cuspLabelModel.localLabCuspModel_eq_zmod

end IUTStage1ZModCuspClassHodgeArakelovLocalObjectData

namespace IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData

variable {kind : IUTStage1PlaceKind}
variable {l : PrimeGeFive}
variable {hodgeData : IUTStage1HodgeTheaterDescentBridgeData}
variable {zeroObject : IUTStage1FiniteLocalLogVolumeObject kind}
variable
  {cuspClassObject :
    (zmodSignAction l).SignLabelQuotient ->
      IUTStage1FiniteLocalLogVolumeObject kind}
variable {packetObject : IUTStage1FiniteLocalLogVolumeObject kind}

def toSourceMarkedCuspZeroLocalObjectOperationData
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1SourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
      l hodgeData zeroObject cuspClassObject packetObject :=
  { zeroSource := data.zeroSource,
    cuspClassSource := fun label =>
      (data.cuspClassSource label).toCuspClassHodgeArakelovLocalObjectData,
    packetTarget := data.packetTarget,
    zeroOperation := data.zeroOperation,
    cuspClassOperation := data.cuspClassOperation }

def toRoleMarkedCuspZeroLocalObjectOperationData
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    IUTStage1RoleMarkedHodgeDescentCuspZeroLocalObjectOperationData
      l hodgeData zeroObject cuspClassObject packetObject :=
  let sourceMarked := data.toSourceMarkedCuspZeroLocalObjectOperationData
  sourceMarked.toRoleMarkedCuspZeroLocalObjectOperationData

theorem cuspClassLabel_eq_zmodCoordinate
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        (data.cuspClassSource label).coordinate
        (data.cuspClassSource label).coordinate_ne_zero :=
  (data.cuspClassSource label).label_eq_zmodCoordinate

theorem cuspClassLabel_eq_negCoordinate
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        (-(data.cuspClassSource label).coordinate)
        (zmod_neg_ne_zero_of_ne_zero l
          (data.cuspClassSource label).coordinate_ne_zero) :=
  (data.cuspClassSource label).label_eq_negCoordinate

theorem cuspClassLabel_eq_canonical_of_coordinate_eq_one
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient)
    (hcoord :
      (data.cuspClassSource label).coordinate = (1 : ZMod l.value)) :
    label = zmodCanonicalSignLabelQuotient l :=
  (data.cuspClassSource label).label_eq_canonical_of_coordinate_eq_one hcoord

def fullLabelLocalObject
    (_data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : IUTStage1ZModCuspFullLabel l) :
    IUTStage1FiniteLocalLogVolumeObject kind :=
  IUTStage1ZModCuspFullLabel.localObject zeroObject cuspClassObject label

theorem fullLabelLocalObject_zero
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.fullLabelLocalObject IUTStage1ZModCuspFullLabel.zero =
      zeroObject :=
  rfl

theorem fullLabelLocalObject_nonzero
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    data.fullLabelLocalObject (IUTStage1ZModCuspFullLabel.nonzero label) =
      cuspClassObject label :=
  rfl

theorem fullLabelLocalObject_transports_to_packet
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : IUTStage1ZModCuspFullLabel l) :
    data.fullLabelLocalObject label = packetObject := by
  cases label with
  | zero =>
      exact data.zeroOperation.source_transports_to_packet'
  | nonzero label =>
      exact (data.cuspClassOperation label).source_transports_to_packet'

theorem fullLabelLocalObject_fromCoordinate_zero
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject) :
    data.fullLabelLocalObject
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (0 : ZMod l.value)) =
      zeroObject := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  rfl

theorem fullLabelLocalObject_fromCoordinate_nonzero
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (j : ZMod l.value) (hj : j ≠ 0) :
    data.fullLabelLocalObject (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      cuspClassObject (zmodSignLabelFromCoordinate l j hj) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
  rfl

theorem cuspClassCoordinate_ne_zero
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    (data.cuspClassSource label).coordinate ≠ 0 :=
  (data.cuspClassSource label).coordinate_ne_zero'

theorem zero_eq_cuspClass
    (data :
      IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData
        l hodgeData zeroObject cuspClassObject packetObject)
    (label : (zmodSignAction l).SignLabelQuotient) :
    zeroObject = cuspClassObject label :=
  data.toSourceMarkedCuspZeroLocalObjectOperationData.zero_eq_cuspClass label

end IUTStage1ZModSourceMarkedHodgeDescentCuspZeroLocalObjectOperationData

/--
Local packet-normalized compatibility together with a source classification.
-/
structure IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
    {kind : IUTStage1PlaceKind}
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) where
  compatibility :
    IUTStage1LocalTensorPacketNormalizedCompatibility state
  identification_source : IUTStage1PacketNormalizedIdentificationSource

/--
Direct packet-normalization data expressed as a finite capsule-sum average.

This is more concrete than a bare equality with the `normalizedLogVolume` field:
it identifies the local object's finite log-volume with the average of the
packet's capsule log-volumes.
-/
structure IUTStage1DirectPacketNormalizationData
    {kind : IUTStage1PlaceKind}
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) where
  localObject_finiteLogVolume_eq_capsuleSumAverage :
    state.localObject.finiteLogVolume =
      (Finset.univ.sum fun i =>
          (state.capsuleFamily.capsule i).logVolume) /
        (state.capsuleFamily.capsuleCount : Real)

/--
Upper semi-compatibility state used by the Theorem 3.11 `(Ind3)` model.

The booleans record whether the local comparison is modeled by the two source
features singled out in the statement of Theorem 3.11: natural inclusions at
nonarchimedean places and natural surjections at archimedean places.
-/
structure IUTStage1UpperSemiCompatibilityState where
  logThetaColumn : LogThetaColumnId
  compatibility : UpperSemiCompatibilityId
  nonarchimedeanInclusions : List IUTStage1NonarchimedeanInclusionData
  archimedeanSurjections : List IUTStage1ArchimedeanSurjectionData
  logVolumeCompatibility : IUTStage1LogVolumeCompatibilityData
  hasNonarchimedeanInclusions : Bool
  hasArchimedeanSurjections : Bool
  logVolumeCompatible : Prop
  log_volume_compatible : logVolumeCompatible

/--
Compatibility between `(Ind2)` place-family action data and the `(Ind3)`
upper-semi place-family data.

This record checks that the places carrying nonarchimedean `Ism` actions are
the same places appearing in the nonarchimedean inclusion data, and similarly
for archimedean order-two actions and archimedean surjections.
-/
structure IUTStage1Ind2UpperSemiPlaceFamilyCompatibility where
  ind2Actions : IUTStage1Ind2PlaceFamilyActionData
  upperSemiState : IUTStage1UpperSemiCompatibilityState
  nonarchimedean_places_eq :
    ind2Actions.nonarchimedeanPlaces =
      upperSemiState.nonarchimedeanInclusions.map fun data => data.place
  archimedean_places_eq :
    ind2Actions.archimedeanPlaces =
      upperSemiState.archimedeanSurjections.map fun data => data.place

namespace IUTStage1Ind2UpperSemiPlaceFamilyCompatibility

theorem nonarchimedeanPlaces_eq
    (data : IUTStage1Ind2UpperSemiPlaceFamilyCompatibility) :
    data.ind2Actions.nonarchimedeanPlaces =
      data.upperSemiState.nonarchimedeanInclusions.map fun entry =>
        entry.place :=
  data.nonarchimedean_places_eq

theorem archimedeanPlaces_eq
    (data : IUTStage1Ind2UpperSemiPlaceFamilyCompatibility) :
    data.ind2Actions.archimedeanPlaces =
      data.upperSemiState.archimedeanSurjections.map fun entry =>
        entry.place :=
  data.archimedean_places_eq

theorem logVolumeCompatible
    (data : IUTStage1Ind2UpperSemiPlaceFamilyCompatibility) :
    data.upperSemiState.logVolumeCompatible :=
  data.upperSemiState.log_volume_compatible

theorem logVolumeUpperBound
    (data : IUTStage1Ind2UpperSemiPlaceFamilyCompatibility) :
    data.upperSemiState.logVolumeCompatibility.sourceLogVolume <=
      data.upperSemiState.logVolumeCompatibility.targetLogVolume :=
  data.upperSemiState.logVolumeCompatibility.source_le_target

/--
Remark 3.12.2(iii) upper-semi place-family endpoint.

The log-link juggling responsible for `(Ind3)` is recorded here as the same
nonarchimedean/archimedean place families as `(Ind2)`, together with the
one-sided log-volume comparison of the upper-semi state.
-/
theorem remark3122_logLinkJuggling_upperSemi_endpoint
    (data : IUTStage1Ind2UpperSemiPlaceFamilyCompatibility) :
    data.ind2Actions.nonarchimedeanPlaces =
        (data.upperSemiState.nonarchimedeanInclusions.map fun entry =>
          entry.place) ∧
      data.ind2Actions.archimedeanPlaces =
        (data.upperSemiState.archimedeanSurjections.map fun entry =>
          entry.place) ∧
      data.upperSemiState.logVolumeCompatible ∧
      data.upperSemiState.logVolumeCompatibility.sourceLogVolume <=
        data.upperSemiState.logVolumeCompatibility.targetLogVolume :=
  ⟨data.nonarchimedeanPlaces_eq,
    data.archimedeanPlaces_eq,
    data.logVolumeCompatible,
    data.logVolumeUpperBound⟩

end IUTStage1Ind2UpperSemiPlaceFamilyCompatibility

namespace IUTStage1NonarchimedeanInclusionData

theorem sourcePlaceMatches
    (data : IUTStage1NonarchimedeanInclusionData) :
    data.sourceObject.place = data.place :=
  data.source_place_eq

theorem targetPlaceMatches
    (data : IUTStage1NonarchimedeanInclusionData) :
    data.targetObject.place = data.place :=
  data.target_place_eq

theorem sourceLogVolumeObjectMatches
    (data : IUTStage1NonarchimedeanInclusionData) :
    data.sourceLogVolume.localObject.object = data.sourceObject :=
  data.source_log_volume_object_eq

theorem targetLogVolumeObjectMatches
    (data : IUTStage1NonarchimedeanInclusionData) :
    data.targetLogVolume.localObject.object = data.targetObject :=
  data.target_log_volume_object_eq

theorem logVolume_le
    (data : IUTStage1NonarchimedeanInclusionData) :
    data.sourceLogVolume.finiteLogVolume <=
      data.targetLogVolume.finiteLogVolume :=
  data.source_logVolume_le_target_logVolume

theorem valid (data : IUTStage1NonarchimedeanInclusionData) :
    data.inclusionValid :=
  data.inclusion_valid

end IUTStage1NonarchimedeanInclusionData

namespace IUTStage1ArchimedeanSurjectionData

theorem sourcePlaceMatches
    (data : IUTStage1ArchimedeanSurjectionData) :
    data.sourceObject.place = data.place :=
  data.source_place_eq

theorem targetPlaceMatches
    (data : IUTStage1ArchimedeanSurjectionData) :
    data.targetObject.place = data.place :=
  data.target_place_eq

theorem sourceLogVolumeObjectMatches
    (data : IUTStage1ArchimedeanSurjectionData) :
    data.sourceLogVolume.localObject.object = data.sourceObject :=
  data.source_log_volume_object_eq

theorem targetLogVolumeObjectMatches
    (data : IUTStage1ArchimedeanSurjectionData) :
    data.targetLogVolume.localObject.object = data.targetObject :=
  data.target_log_volume_object_eq

theorem logVolume_le
    (data : IUTStage1ArchimedeanSurjectionData) :
    data.targetLogVolume.finiteLogVolume <=
      data.sourceLogVolume.finiteLogVolume :=
  data.target_logVolume_le_source_logVolume

theorem valid (data : IUTStage1ArchimedeanSurjectionData) :
    data.surjectionValid :=
  data.surjection_valid

end IUTStage1ArchimedeanSurjectionData

namespace IUTStage1LogVolumeCompatibilityData

theorem upperBound (data : IUTStage1LogVolumeCompatibilityData) :
    data.sourceLogVolume <= data.targetLogVolume :=
  data.source_le_target

end IUTStage1LogVolumeCompatibilityData

namespace IUTStage1ProcessionState

set_option linter.style.longLine false in
/--
Concrete procession transport between procession states.

The `F_l`-shifted theta-pilot choice already fixes the log-theta column.  This
transport records the remaining procession data: the D-prime-strip procession
identifier and the chosen representative.
-/
structure ProcessionTransport
    (state₁ state₂ : IUTStage1ProcessionState) : Prop where
  procession_eq : state₁.procession = state₂.procession
  representative_eq : state₁.representative = state₂.representative

theorem ProcessionTransport.ofEq
    {state₁ state₂ : IUTStage1ProcessionState}
    (h : state₁ = state₂) :
    ProcessionTransport state₁ state₂ := by
  cases h
  exact ⟨rfl, rfl⟩

theorem same_procession_of_eq
    {state₁ state₂ : IUTStage1ProcessionState}
    (h : state₁ = state₂) :
    state₁.procession = state₂.procession := by
  cases h
  rfl

theorem same_column_of_eq
    {state₁ state₂ : IUTStage1ProcessionState}
    (h : state₁ = state₂) :
    state₁.column = state₂.column := by
  cases h
  rfl

theorem ProcessionTransport.eq_of_column_eq
    {state₁ state₂ : IUTStage1ProcessionState}
    (transport : ProcessionTransport state₁ state₂)
    (column_eq : state₁.column = state₂.column) :
    state₁ = state₂ := by
  cases state₁ with
  | mk procession₁ column₁ representative₁ =>
  cases state₂ with
  | mk procession₂ column₂ representative₂ =>
  cases transport.procession_eq
  cases column_eq
  cases transport.representative_eq
  rfl

end IUTStage1ProcessionState

namespace IUTStage1LocalTensorState

set_option linter.style.longLine false in
/--
Source certificate that a local tensor state carries the canonical
nonarchimedean `Ism` symmetry label.
-/
structure NonarchimedeanIsmSymmetrySource
    (state : IUTStage1LocalTensorState) : Prop where
  symmetry_eq :
    state.symmetry =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm.toLocalTensorSymmetryId

set_option linter.style.longLine false in
/--
Source certificate that a local tensor state carries the canonical archimedean
order-two symmetry label.
-/
structure ArchimedeanOrderTwoSymmetrySource
    (state : IUTStage1LocalTensorState) : Prop where
  symmetry_eq :
    state.symmetry =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo.toLocalTensorSymmetryId

set_option linter.style.longLine false in
theorem NonarchimedeanIsmSymmetrySource.symmetry_eq_of
    {state₁ state₂ : IUTStage1LocalTensorState}
    (source₁ : NonarchimedeanIsmSymmetrySource state₁)
    (source₂ : NonarchimedeanIsmSymmetrySource state₂) :
    state₁.symmetry = state₂.symmetry := by
  rw [source₁.symmetry_eq, source₂.symmetry_eq]

set_option linter.style.longLine false in
theorem ArchimedeanOrderTwoSymmetrySource.symmetry_eq_of
    {state₁ state₂ : IUTStage1LocalTensorState}
    (source₁ : ArchimedeanOrderTwoSymmetrySource state₁)
    (source₂ : ArchimedeanOrderTwoSymmetrySource state₂) :
    state₁.symmetry = state₂.symmetry := by
  rw [source₁.symmetry_eq, source₂.symmetry_eq]

set_option linter.style.longLine false in
/--
Concrete direct-summand symmetry between local tensor states.

The paper-side `(Ind2)` symmetry should preserve the number of direct summands.
At this boundary the preservation is witnessed by an equivalence of the finite
summand index sets, rather than by an equality of natural numbers.
-/
structure DirectSummandSymmetry
    (state₁ state₂ : IUTStage1LocalTensorState) : Prop where
  symmetry_eq : state₁.symmetry = state₂.symmetry
  summandEquiv_nonempty :
    Nonempty (Fin state₁.directSummandCount ≃ Fin state₂.directSummandCount)

theorem same_summand_count_of_eq
    {state₁ state₂ : IUTStage1LocalTensorState}
    (h : state₁ = state₂) :
    state₁.directSummandCount = state₂.directSummandCount := by
  cases h
  rfl

theorem DirectSummandSymmetry.directSummandCount_eq
    {state₁ state₂ : IUTStage1LocalTensorState}
    (symmetry : DirectSummandSymmetry state₁ state₂) :
    state₁.directSummandCount = state₂.directSummandCount := by
  rcases symmetry.summandEquiv_nonempty with ⟨summandEquiv⟩
  calc
    state₁.directSummandCount =
        Fintype.card (Fin state₁.directSummandCount) :=
      (Fintype.card_fin state₁.directSummandCount).symm
    _ = Fintype.card (Fin state₂.directSummandCount) :=
      Fintype.card_congr summandEquiv
    _ = state₂.directSummandCount :=
      Fintype.card_fin state₂.directSummandCount

set_option linter.style.longLine false in
/--
Packet-level direct-summand symmetry.

This is lower than `DirectSummandSymmetry`: the equivalence is supplied on the
capsule/direct-summand packet index sets, while the two local tensor states are
identified with the tensor states carried by those packets.  The packet records
then convert capsule-count equivalence into direct-summand-count equivalence.
-/
def DirectSummandPacketSymmetry
    (state₁ state₂ : IUTStage1LocalTensorState) : Prop :=
  ∃ (kind : IUTStage1PlaceKind)
    (sourcePacket : IUTStage1LocalTensorPacketLogVolumeState kind)
    (targetPacket : IUTStage1LocalTensorPacketLogVolumeState kind),
    sourcePacket.tensorState = state₁ ∧
      targetPacket.tensorState = state₂ ∧
      state₁.symmetry = state₂.symmetry ∧
      Nonempty
        (Fin sourcePacket.capsuleFamily.capsuleCount ≃
          Fin targetPacket.capsuleFamily.capsuleCount)

set_option linter.style.longLine false in
theorem DirectSummandPacketSymmetry.directSummandCount_eq
    {state₁ state₂ : IUTStage1LocalTensorState}
    (packetSymmetry : DirectSummandPacketSymmetry state₁ state₂) :
    state₁.directSummandCount = state₂.directSummandCount := by
  rcases packetSymmetry with
    ⟨kind, sourcePacket, targetPacket, hsourceTensor, htargetTensor,
      _hsymmetry, hcapsuleEquiv⟩
  rcases hcapsuleEquiv with ⟨capsuleEquiv⟩
  have hsource :
      state₁.directSummandCount = sourcePacket.capsuleFamily.capsuleCount := by
    calc
      state₁.directSummandCount = sourcePacket.tensorState.directSummandCount :=
        (congrArg IUTStage1LocalTensorState.directSummandCount
          hsourceTensor).symm
      _ = sourcePacket.capsuleFamily.capsuleCount :=
        sourcePacket.direct_summand_count_eq_capsuleCount
  have htarget :
      state₂.directSummandCount = targetPacket.capsuleFamily.capsuleCount := by
    calc
      state₂.directSummandCount = targetPacket.tensorState.directSummandCount :=
        (congrArg IUTStage1LocalTensorState.directSummandCount
          htargetTensor).symm
      _ = targetPacket.capsuleFamily.capsuleCount :=
        targetPacket.direct_summand_count_eq_capsuleCount
  calc
    state₁.directSummandCount = sourcePacket.capsuleFamily.capsuleCount :=
      hsource
    _ = Fintype.card (Fin sourcePacket.capsuleFamily.capsuleCount) :=
      (Fintype.card_fin sourcePacket.capsuleFamily.capsuleCount).symm
    _ = Fintype.card (Fin targetPacket.capsuleFamily.capsuleCount) :=
      Fintype.card_congr capsuleEquiv
    _ = targetPacket.capsuleFamily.capsuleCount :=
      Fintype.card_fin targetPacket.capsuleFamily.capsuleCount
    _ = state₂.directSummandCount :=
      htarget.symm

set_option linter.style.longLine false in
theorem DirectSummandPacketSymmetry.toDirectSummandSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (packetSymmetry : DirectSummandPacketSymmetry state₁ state₂) :
    DirectSummandSymmetry state₁ state₂ := by
  rcases packetSymmetry with
    ⟨kind, sourcePacket, targetPacket, hsourceTensor, htargetTensor,
      hsymmetry, hcapsuleEquiv⟩
  rcases hcapsuleEquiv with ⟨capsuleEquiv⟩
  refine
    { symmetry_eq := hsymmetry,
      summandEquiv_nonempty := ?_ }
  have hsource :
      state₁.directSummandCount = sourcePacket.capsuleFamily.capsuleCount := by
    calc
      state₁.directSummandCount = sourcePacket.tensorState.directSummandCount :=
        (congrArg IUTStage1LocalTensorState.directSummandCount
          hsourceTensor).symm
      _ = sourcePacket.capsuleFamily.capsuleCount :=
        sourcePacket.direct_summand_count_eq_capsuleCount
  have htarget :
      state₂.directSummandCount = targetPacket.capsuleFamily.capsuleCount := by
    calc
      state₂.directSummandCount = targetPacket.tensorState.directSummandCount :=
        (congrArg IUTStage1LocalTensorState.directSummandCount
          htargetTensor).symm
      _ = targetPacket.capsuleFamily.capsuleCount :=
        targetPacket.direct_summand_count_eq_capsuleCount
  exact
    ⟨(Equiv.cast (congrArg Fin hsource)).trans
      (capsuleEquiv.trans
        (Equiv.cast (congrArg Fin htarget.symm)))⟩

set_option linter.style.longLine false in
/--
Direct-summand-action packet symmetry.

This is lower than `DirectSummandPacketSymmetry`: instead of supplying a raw
equivalence of capsule index sets, the source supplies direct-summand packet
states and an action on the source summand family whose induced capsule-family
action is the target capsule family.  Since a direct-summand-family action keeps
the source finite index type, Lean derives the capsule-index equivalence.
-/
def DirectSummandActionPacketSymmetry
    (state₁ state₂ : IUTStage1LocalTensorState) : Prop :=
  ∃ (kind : IUTStage1PlaceKind)
    (sourcePacket : IUTStage1LocalTensorDirectSummandPacketState kind)
    (targetPacket : IUTStage1LocalTensorDirectSummandPacketState kind),
    sourcePacket.packetState.tensorState = state₁ ∧
      targetPacket.packetState.tensorState = state₂ ∧
      state₁.symmetry = state₂.symmetry ∧
      ∃ action : IUTStage1TensorDirectSummandFamilyAction
          sourcePacket.summandFamily,
        targetPacket.packetState.capsuleFamily =
          action.toCapsuleAction.transformedFamily

set_option linter.style.longLine false in
theorem DirectSummandActionPacketSymmetry.toDirectSummandPacketSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (actionSymmetry : DirectSummandActionPacketSymmetry state₁ state₂) :
    DirectSummandPacketSymmetry state₁ state₂ := by
  rcases actionSymmetry with
    ⟨kind, sourcePacket, targetPacket, hsourceTensor, htargetTensor,
      hsymmetry, action, htargetCapsuleFamily⟩
  refine
    ⟨kind, sourcePacket.packetState, targetPacket.packetState,
      hsourceTensor, htargetTensor, hsymmetry, ?_⟩
  have htargetCount :
      targetPacket.packetState.capsuleFamily.capsuleCount =
        action.toCapsuleAction.transformedFamily.capsuleCount :=
    congrArg IUTStage1TypedCapsuleFamilyLogVolume.capsuleCount
      htargetCapsuleFamily
  have hactionCount :
      action.toCapsuleAction.transformedFamily.capsuleCount =
        sourcePacket.packetState.capsuleFamily.capsuleCount :=
    action.toCapsuleAction.transformedFamily_capsuleCount
  have hcount :
      sourcePacket.packetState.capsuleFamily.capsuleCount =
        targetPacket.packetState.capsuleFamily.capsuleCount :=
    (htargetCount.trans hactionCount).symm
  exact ⟨Equiv.cast (congrArg Fin hcount)⟩

set_option linter.style.longLine false in
theorem DirectSummandActionPacketSymmetry.toDirectSummandSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (actionSymmetry : DirectSummandActionPacketSymmetry state₁ state₂) :
    DirectSummandSymmetry state₁ state₂ :=
  actionSymmetry.toDirectSummandPacketSymmetry.toDirectSummandSymmetry

set_option linter.style.longLine false in
/--
Typed `(Ind2)` direct-summand action packet symmetry.

This is lower than `DirectSummandActionPacketSymmetry`: the action is no longer
an arbitrary direct-summand-family action.  It must be one of the two typed
local tensor-factor symmetries singled out in Theorem 3.11, namely the
nonarchimedean `Ism` action or the archimedean order-two action.
-/
def Ind2ActionPacketSymmetry
    (state₁ state₂ : IUTStage1LocalTensorState) : Prop :=
  (∃ (sourcePacket :
        IUTStage1LocalTensorDirectSummandPacketState
          IUTStage1PlaceKind.nonarchimedean)
      (targetPacket :
        IUTStage1LocalTensorDirectSummandPacketState
          IUTStage1PlaceKind.nonarchimedean),
      sourcePacket.packetState.tensorState = state₁ ∧
        targetPacket.packetState.tensorState = state₂ ∧
        state₁.symmetry = state₂.symmetry ∧
        ∃ action :
          IUTStage1NonarchimedeanIsmDirectSummandAction
            sourcePacket.summandFamily,
          targetPacket.packetState.capsuleFamily =
            action.toDirectSummandAction.toCapsuleAction.transformedFamily) ∨
    (∃ (sourcePacket :
          IUTStage1LocalTensorDirectSummandPacketState
            IUTStage1PlaceKind.archimedean)
        (targetPacket :
          IUTStage1LocalTensorDirectSummandPacketState
            IUTStage1PlaceKind.archimedean),
        sourcePacket.packetState.tensorState = state₁ ∧
          targetPacket.packetState.tensorState = state₂ ∧
          state₁.symmetry = state₂.symmetry ∧
          ∃ action :
            IUTStage1ArchimedeanOrderTwoDirectSummandAction
              sourcePacket.summandFamily,
            targetPacket.packetState.capsuleFamily =
              action.toDirectSummandAction.toCapsuleAction.transformedFamily)

set_option linter.style.longLine false in
theorem Ind2ActionPacketSymmetry.toDirectSummandActionPacketSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (ind2Symmetry : Ind2ActionPacketSymmetry state₁ state₂) :
    DirectSummandActionPacketSymmetry state₁ state₂ := by
  rcases ind2Symmetry with hnonarch | harch
  · rcases hnonarch with
      ⟨sourcePacket, targetPacket, hsourceTensor, htargetTensor,
        hsymmetry, action, htargetCapsuleFamily⟩
    exact
      ⟨IUTStage1PlaceKind.nonarchimedean, sourcePacket, targetPacket,
        hsourceTensor, htargetTensor, hsymmetry,
        action.toDirectSummandAction, htargetCapsuleFamily⟩
  · rcases harch with
      ⟨sourcePacket, targetPacket, hsourceTensor, htargetTensor,
        hsymmetry, action, htargetCapsuleFamily⟩
    exact
      ⟨IUTStage1PlaceKind.archimedean, sourcePacket, targetPacket,
        hsourceTensor, htargetTensor, hsymmetry,
        action.toDirectSummandAction, htargetCapsuleFamily⟩

set_option linter.style.longLine false in
theorem Ind2ActionPacketSymmetry.toDirectSummandPacketSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (ind2Symmetry : Ind2ActionPacketSymmetry state₁ state₂) :
    DirectSummandPacketSymmetry state₁ state₂ :=
  ind2Symmetry.toDirectSummandActionPacketSymmetry.toDirectSummandPacketSymmetry

set_option linter.style.longLine false in
theorem Ind2ActionPacketSymmetry.toDirectSummandSymmetry
    {state₁ state₂ : IUTStage1LocalTensorState}
    (ind2Symmetry : Ind2ActionPacketSymmetry state₁ state₂) :
    DirectSummandSymmetry state₁ state₂ :=
  ind2Symmetry.toDirectSummandActionPacketSymmetry.toDirectSummandSymmetry

end IUTStage1LocalTensorState

namespace IUTStage1LocalTensorPacketLogVolumeState

variable {kind : IUTStage1PlaceKind}

def toLocalTensorState
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    IUTStage1LocalTensorState :=
  state.tensorState

def toTypedCapsuleFamilyLogVolume
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    IUTStage1TypedCapsuleFamilyLogVolume kind :=
  state.capsuleFamily

theorem directSummandCount_eq_capsuleCount
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    state.tensorState.directSummandCount =
      state.capsuleFamily.capsuleCount :=
  state.direct_summand_count_eq_capsuleCount

theorem directSummandCount_pos
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    0 < state.tensorState.directSummandCount := by
  rw [state.direct_summand_count_eq_capsuleCount]
  exact state.capsuleFamily.capsuleCount_pos

theorem capsuleFamilyLocalObject_eq
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    state.capsuleFamily.localObject = state.localObject :=
  state.capsule_family_localObject_eq

theorem capsule_totalLogVolume_eq_sum
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    state.capsuleFamily.totalLogVolume =
      Finset.univ.sum fun i => (state.capsuleFamily.capsule i).logVolume :=
  state.capsuleFamily.total_eq

theorem capsule_normalizedLogVolume_eq
    (state : IUTStage1LocalTensorPacketLogVolumeState kind) :
    state.capsuleFamily.normalizedLogVolume =
      state.capsuleFamily.totalLogVolume /
        (state.capsuleFamily.capsuleCount : Real) :=
  state.capsuleFamily.normalized_eq

end IUTStage1LocalTensorPacketLogVolumeState

namespace IUTStage1LocalTensorPacketNormalizedCompatibility

variable {kind : IUTStage1PlaceKind}
variable {state : IUTStage1LocalTensorPacketLogVolumeState kind}

theorem localObject_finiteLogVolume_eq_normalizedLogVolume
    (compat : IUTStage1LocalTensorPacketNormalizedCompatibility state) :
    state.localObject.finiteLogVolume =
      state.capsuleFamily.normalizedLogVolume :=
  compat.normalizedLogVolume_eq_localObject.symm

theorem normalizedLogVolume_eq_capsuleAverage
    (compat : IUTStage1LocalTensorPacketNormalizedCompatibility state) :
    state.localObject.finiteLogVolume =
      state.capsuleFamily.totalLogVolume /
        (state.capsuleFamily.capsuleCount : Real) := by
  calc
    state.localObject.finiteLogVolume =
        state.capsuleFamily.normalizedLogVolume :=
      compat.localObject_finiteLogVolume_eq_normalizedLogVolume
    _ =
        state.capsuleFamily.totalLogVolume /
          (state.capsuleFamily.capsuleCount : Real) :=
      state.capsule_normalizedLogVolume_eq

end IUTStage1LocalTensorPacketNormalizedCompatibility

namespace IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility

variable {kind : IUTStage1PlaceKind}
variable {state : IUTStage1LocalTensorPacketLogVolumeState kind}

def ofDirectPacketNormalization
    (compat : IUTStage1LocalTensorPacketNormalizedCompatibility state) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state :=
  { compatibility := compat,
    identification_source :=
      IUTStage1PacketNormalizedIdentificationSource.directPacketNormalization }

def ofInd2TransportedPacketNormalization
    (compat : IUTStage1LocalTensorPacketNormalizedCompatibility state) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state :=
  { compatibility := compat,
    identification_source :=
      IUTStage1PacketNormalizedIdentificationSource.ind2TransportedPacketNormalization }

def ofSeparateRealLineIdentification
    (compat : IUTStage1LocalTensorPacketNormalizedCompatibility state) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state :=
  { compatibility := compat,
    identification_source :=
      IUTStage1PacketNormalizedIdentificationSource.separateRealLineIdentification }

theorem localObject_finiteLogVolume_eq_normalizedLogVolume
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state) :
    state.localObject.finiteLogVolume =
      state.capsuleFamily.normalizedLogVolume :=
  classified.compatibility.localObject_finiteLogVolume_eq_normalizedLogVolume

theorem normalizedLogVolume_eq_capsuleAverage
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state) :
    state.localObject.finiteLogVolume =
      state.capsuleFamily.totalLogVolume /
        (state.capsuleFamily.capsuleCount : Real) :=
  classified.compatibility.normalizedLogVolume_eq_capsuleAverage

end IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility

namespace IUTStage1DirectPacketNormalizationData

variable {kind : IUTStage1PlaceKind}
variable {state : IUTStage1LocalTensorPacketLogVolumeState kind}

theorem localObject_finiteLogVolume_eq_capsuleAverage
    (data : IUTStage1DirectPacketNormalizationData state) :
    state.localObject.finiteLogVolume =
      state.capsuleFamily.totalLogVolume /
        (state.capsuleFamily.capsuleCount : Real) := by
  calc
    state.localObject.finiteLogVolume =
        (Finset.univ.sum fun i =>
            (state.capsuleFamily.capsule i).logVolume) /
          (state.capsuleFamily.capsuleCount : Real) :=
      data.localObject_finiteLogVolume_eq_capsuleSumAverage
    _ =
        state.capsuleFamily.totalLogVolume /
          (state.capsuleFamily.capsuleCount : Real) := by
      rw [state.capsule_totalLogVolume_eq_sum]

def toPacketNormalizedCompatibility
    (data : IUTStage1DirectPacketNormalizationData state) :
    IUTStage1LocalTensorPacketNormalizedCompatibility state :=
  { normalizedLogVolume_eq_localObject := by
      calc
        state.capsuleFamily.normalizedLogVolume =
            state.capsuleFamily.totalLogVolume /
              (state.capsuleFamily.capsuleCount : Real) :=
          state.capsule_normalizedLogVolume_eq
        _ = state.localObject.finiteLogVolume :=
          data.localObject_finiteLogVolume_eq_capsuleAverage.symm }

def toClassifiedPacketNormalizedCompatibility
    (data : IUTStage1DirectPacketNormalizationData state) :
    IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility state :=
  IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.ofDirectPacketNormalization
    data.toPacketNormalizedCompatibility

theorem targetSigned_le_localObject_of_capsule_le
    (data : IUTStage1DirectPacketNormalizationData state)
    {targetSigned : Real}
    (hcapsule :
      ∀ i : Fin state.capsuleFamily.capsuleCount,
        targetSigned <= (state.capsuleFamily.capsule i).logVolume) :
    targetSigned <= state.localObject.finiteLogVolume := by
  have hnormalized :
      targetSigned <= state.capsuleFamily.normalizedLogVolume :=
    state.capsuleFamily.const_le_normalizedLogVolume_of_capsule_le hcapsule
  rw [data.toPacketNormalizedCompatibility.normalizedLogVolume_eq_localObject]
    at hnormalized
  exact hnormalized

theorem targetSigned_le_localObject_of_capsule_estimates
    (data : IUTStage1DirectPacketNormalizationData state)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned state.capsuleFamily) :
    targetSigned <= state.localObject.finiteLogVolume :=
  data.targetSigned_le_localObject_of_capsule_le
    estimate.targetSigned_le_capsuleLogVolume

def toLocalObjectContainerEstimateOfCapsuleEstimates
    (data : IUTStage1DirectPacketNormalizationData state)
    {targetSigned : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned state.capsuleFamily) :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned state.localObject.finiteLogVolume :=
  { localObject := state.localObject,
    localLogVolume_eq_object := rfl,
    object_container_estimate :=
      { containerLogVolume := state.localObject.finiteLogVolume,
        localLogVolume_eq_container := rfl,
        targetSigned_le_containerLogVolume :=
          data.targetSigned_le_localObject_of_capsule_estimates estimate } }

def toLocalObjectContainerEstimateOfIdentifiedLogVolume
    (data : IUTStage1DirectPacketNormalizationData state)
    {targetSigned localLogVolume : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned state.capsuleFamily)
    (hlog : localLogVolume = state.localObject.finiteLogVolume) :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned localLogVolume :=
  IUTStage1LocalObjectContainerLogVolumeEstimate.transportLocalLogVolume
    (data.toLocalObjectContainerEstimateOfCapsuleEstimates estimate) hlog

theorem identifiedLogVolumeEstimate_localObject
    (data : IUTStage1DirectPacketNormalizationData state)
    {targetSigned localLogVolume : Real}
    (estimate :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned state.capsuleFamily)
    (hlog : localLogVolume = state.localObject.finiteLogVolume) :
    (data.toLocalObjectContainerEstimateOfIdentifiedLogVolume
      estimate hlog).localObject = state.localObject :=
  rfl

end IUTStage1DirectPacketNormalizationData

namespace IUTStage1ZModLabelledCapsuleFamilyLogVolume

variable {l : PrimeGeFive} {kind : IUTStage1PlaceKind}

theorem normalizedLogVolume_eq_packetState_normalizedLogVolume
    (data : IUTStage1ZModLabelledCapsuleFamilyLogVolume l kind)
    {state : IUTStage1LocalTensorPacketLogVolumeState kind}
    (directNormalization : IUTStage1DirectPacketNormalizationData state)
    (localObject_eq_packetLocalObject :
      data.localObject = state.localObject) :
    data.normalizedLogVolume = state.capsuleFamily.normalizedLogVolume := by
  calc
    data.normalizedLogVolume = data.localObject.finiteLogVolume :=
      data.normalizedLogVolume_eq_localObjectFinite
    _ = state.localObject.finiteLogVolume := by
      rw [localObject_eq_packetLocalObject]
    _ = state.capsuleFamily.normalizedLogVolume :=
      directNormalization.toPacketNormalizedCompatibility
        |>.localObject_finiteLogVolume_eq_normalizedLogVolume

end IUTStage1ZModLabelledCapsuleFamilyLogVolume

namespace IUTStage1LocalTensorDirectSummandPacketState

variable {kind : IUTStage1PlaceKind}

def toLocalTensorPacketLogVolumeState
    (state : IUTStage1LocalTensorDirectSummandPacketState kind) :
    IUTStage1LocalTensorPacketLogVolumeState kind :=
  state.packetState

def toLocalTensorState
    (state : IUTStage1LocalTensorDirectSummandPacketState kind) :
    IUTStage1LocalTensorState :=
  state.packetState.tensorState

theorem directSummandCount_eq_capsuleCount
    (state : IUTStage1LocalTensorDirectSummandPacketState kind) :
    state.packetState.tensorState.directSummandCount =
      state.packetState.capsuleFamily.capsuleCount :=
  state.packetState.directSummandCount_eq_capsuleCount

theorem directSummandCount_pos
    (state : IUTStage1LocalTensorDirectSummandPacketState kind) :
    0 < state.packetState.tensorState.directSummandCount :=
  state.packetState.directSummandCount_pos

theorem summandCapsule_eq
    (state : IUTStage1LocalTensorDirectSummandPacketState kind)
    (i : Fin state.packetState.capsuleFamily.capsuleCount) :
    (state.summandFamily.summand i).capsule =
      state.packetState.capsuleFamily.capsule i :=
  state.summandFamily.summandCapsule_eq i

theorem summandCapsuleLogVolume_eq
    (state : IUTStage1LocalTensorDirectSummandPacketState kind)
    (i : Fin state.packetState.capsuleFamily.capsuleCount) :
    (state.summandFamily.summand i).capsule.logVolume =
      (state.packetState.capsuleFamily.capsule i).logVolume :=
  state.summandFamily.summandCapsuleLogVolume_eq i

set_option linter.style.longLine false in
/--
Transport of the typed direct-summand symmetry kind between two local tensor
packets.

This isolates the `(Ind2)` assertion that the target packet inherits the
source packet's local tensor-factor symmetry kind.
-/
structure SymmetryKindTransport
    (state₁ state₂ : IUTStage1LocalTensorDirectSummandPacketState kind) :
    Prop where
  target_symmetryKind_eq_source :
    state₂.summandFamily.symmetryKind = state₁.summandFamily.symmetryKind

set_option linter.style.longLine false in
theorem SymmetryKindTransport.target_symmetryKind_eq
    {state₁ state₂ : IUTStage1LocalTensorDirectSummandPacketState kind}
    (transport : SymmetryKindTransport state₁ state₂)
    {symmetryKind : IUTStage1TensorSummandSymmetryKind}
    (source_symmetryKind_eq :
      state₁.summandFamily.symmetryKind = symmetryKind) :
    state₂.summandFamily.symmetryKind = symmetryKind :=
  transport.target_symmetryKind_eq_source.trans source_symmetryKind_eq

set_option linter.style.longLine false in
/--
Source certificate tying a direct-summand packet's local tensor label to the
typed summand symmetry kind carried by its direct-summand family.

This is the local bridge from the paper-side `(Ind2)` action kind to the
previously untyped tensor-state symmetry coordinate.
-/
structure SymmetryLabelSource
    (state : IUTStage1LocalTensorDirectSummandPacketState kind) : Prop where
  symmetry_eq :
    state.packetState.tensorState.symmetry =
      state.summandFamily.symmetryKind.toLocalTensorSymmetryId

set_option linter.style.longLine false in
theorem SymmetryLabelSource.toNonarchimedeanIsmSymmetrySource
    {state :
      IUTStage1LocalTensorDirectSummandPacketState
        IUTStage1PlaceKind.nonarchimedean}
    (source : SymmetryLabelSource state)
    (symmetry_kind_eq :
      state.summandFamily.symmetryKind =
        IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm) :
    IUTStage1LocalTensorState.NonarchimedeanIsmSymmetrySource
      state.packetState.tensorState :=
  { symmetry_eq := by
      rw [source.symmetry_eq, symmetry_kind_eq] }

set_option linter.style.longLine false in
theorem SymmetryLabelSource.toArchimedeanOrderTwoSymmetrySource
    {state :
      IUTStage1LocalTensorDirectSummandPacketState
        IUTStage1PlaceKind.archimedean}
    (source : SymmetryLabelSource state)
    (symmetry_kind_eq :
      state.summandFamily.symmetryKind =
        IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo) :
    IUTStage1LocalTensorState.ArchimedeanOrderTwoSymmetrySource
      state.packetState.tensorState :=
  { symmetry_eq := by
      rw [source.symmetry_eq, symmetry_kind_eq] }

set_option linter.style.longLine false in
/--
Source-side transport package for the tensor symmetry label and the typed
direct-summand symmetry kind.

This lowers the previous boundary that carried two independent packet-label
certificates plus a separate target-kind transport.  It records a single
source-kind comparison: the source tensor label and target tensor label are
both read against the source packet's summand symmetry kind, and the target
summand symmetry kind is transported from the source.
-/
structure SymmetryLabelTransportSource
    (state₁ state₂ : IUTStage1LocalTensorDirectSummandPacketState kind) :
    Prop where
  source_symmetry_eq_sourceKind :
    state₁.packetState.tensorState.symmetry =
      state₁.summandFamily.symmetryKind.toLocalTensorSymmetryId
  target_symmetry_eq_sourceKind :
    state₂.packetState.tensorState.symmetry =
      state₁.summandFamily.symmetryKind.toLocalTensorSymmetryId
  target_symmetryKind_eq_source :
    state₂.summandFamily.symmetryKind = state₁.summandFamily.symmetryKind

namespace SymmetryLabelTransportSource

variable
  {state₁ state₂ : IUTStage1LocalTensorDirectSummandPacketState kind}

set_option linter.style.longLine false in
theorem target_symmetry_eq_targetKind
    (source : SymmetryLabelTransportSource state₁ state₂) :
    state₂.packetState.tensorState.symmetry =
      state₂.summandFamily.symmetryKind.toLocalTensorSymmetryId :=
  source.target_symmetry_eq_sourceKind.trans
    ((congrArg IUTStage1TensorSummandSymmetryKind.toLocalTensorSymmetryId
      source.target_symmetryKind_eq_source).symm)

def sourceLabelSource
    (source : SymmetryLabelTransportSource state₁ state₂) :
    SymmetryLabelSource state₁ :=
  { symmetry_eq := source.source_symmetry_eq_sourceKind }

def targetLabelSource
    (source : SymmetryLabelTransportSource state₁ state₂) :
    SymmetryLabelSource state₂ :=
  { symmetry_eq := source.target_symmetry_eq_targetKind }

def symmetryKindTransport
    (source : SymmetryLabelTransportSource state₁ state₂) :
    SymmetryKindTransport state₁ state₂ :=
  { target_symmetryKind_eq_source := source.target_symmetryKind_eq_source }

set_option linter.style.longLine false in
theorem source_symmetry_eq
    (source : SymmetryLabelTransportSource state₁ state₂) :
    source.sourceLabelSource.symmetry_eq =
      source.source_symmetry_eq_sourceKind :=
  rfl

set_option linter.style.longLine false in
theorem target_symmetry_eq
    (source : SymmetryLabelTransportSource state₁ state₂) :
    source.targetLabelSource.symmetry_eq =
      source.target_symmetry_eq_targetKind :=
  rfl

end SymmetryLabelTransportSource

end IUTStage1LocalTensorDirectSummandPacketState

/--
Container estimate for a real that is identified with the normalized
capsule-family log-volume of a local tensor packet.
-/
structure IUTStage1PacketNormalizedContainerEstimate
    {kind : IUTStage1PlaceKind}
    (packetState : IUTStage1LocalTensorDirectSummandPacketState kind)
    (targetSigned localLogVolume : Real) where
  objectEstimate :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned localLogVolume
  localObject_eq_packetLocalObject :
    objectEstimate.localObject = packetState.packetState.localObject
  localLogVolume_eq_packetNormalized :
    localLogVolume =
      packetState.packetState.capsuleFamily.normalizedLogVolume

namespace IUTStage1PacketNormalizedContainerEstimate

variable {kind : IUTStage1PlaceKind}
variable {packetState : IUTStage1LocalTensorDirectSummandPacketState kind}
variable {targetSigned localLogVolume : Real}

def toLocalObjectContainerEstimate
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned localLogVolume :=
  estimate.objectEstimate

theorem localObject_eq_packetLocalObject'
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    estimate.objectEstimate.localObject =
      packetState.packetState.localObject :=
  estimate.localObject_eq_packetLocalObject

theorem localLogVolume_eq_packetNormalized'
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    localLogVolume =
      packetState.packetState.capsuleFamily.normalizedLogVolume :=
  estimate.localLogVolume_eq_packetNormalized

def ofLocalObjectCompatibility
    (objectEstimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume)
    (hobject :
      objectEstimate.localObject =
        packetState.packetState.localObject)
    (compat :
      IUTStage1LocalTensorPacketNormalizedCompatibility
        packetState.packetState) :
    IUTStage1PacketNormalizedContainerEstimate
      packetState targetSigned localLogVolume :=
  { objectEstimate := objectEstimate,
    localObject_eq_packetLocalObject := hobject,
    localLogVolume_eq_packetNormalized := by
      calc
        localLogVolume =
            objectEstimate.localObject.finiteLogVolume :=
          objectEstimate.localLogVolume_eq_object
        _ =
            packetState.packetState.localObject.finiteLogVolume := by
          rw [hobject]
        _ =
            packetState.packetState.capsuleFamily.normalizedLogVolume :=
          compat.localObject_finiteLogVolume_eq_normalizedLogVolume }

def ofClassifiedLocalObjectCompatibility
    (objectEstimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume)
    (hobject :
      objectEstimate.localObject =
        packetState.packetState.localObject)
    (classified :
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        packetState.packetState) :
    IUTStage1PacketNormalizedContainerEstimate
      packetState targetSigned localLogVolume :=
  ofLocalObjectCompatibility objectEstimate hobject
    classified.compatibility

theorem targetSigned_le_localLogVolume
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    targetSigned <= localLogVolume :=
  estimate.objectEstimate.targetSigned_le_localLogVolume

theorem localLogVolume_eq_capsuleAverage
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    localLogVolume =
      packetState.packetState.capsuleFamily.totalLogVolume /
        (packetState.packetState.capsuleFamily.capsuleCount : Real) := by
  calc
    localLogVolume =
        packetState.packetState.capsuleFamily.normalizedLogVolume :=
      estimate.localLogVolume_eq_packetNormalized
    _ =
        packetState.packetState.capsuleFamily.totalLogVolume /
          (packetState.packetState.capsuleFamily.capsuleCount : Real) :=
      packetState.packetState.capsule_normalizedLogVolume_eq

theorem localLogVolume_eq_capsuleSumAverage
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume) :
    localLogVolume =
      (Finset.univ.sum fun i =>
          (packetState.packetState.capsuleFamily.capsule i).logVolume) /
        (packetState.packetState.capsuleFamily.capsuleCount : Real) := by
  calc
    localLogVolume =
        packetState.packetState.capsuleFamily.totalLogVolume /
          (packetState.packetState.capsuleFamily.capsuleCount : Real) :=
      estimate.localLogVolume_eq_capsuleAverage
    _ =
        (Finset.univ.sum fun i =>
            (packetState.packetState.capsuleFamily.capsule i).logVolume) /
          (packetState.packetState.capsuleFamily.capsuleCount : Real) := by
      rw [packetState.packetState.capsule_totalLogVolume_eq_sum]

theorem targetSigned_le_localLogVolume_of_capsule_le
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume)
    (hcapsule :
      ∀ i : Fin packetState.packetState.capsuleFamily.capsuleCount,
        targetSigned <=
          (packetState.packetState.capsuleFamily.capsule i).logVolume) :
    targetSigned <= localLogVolume := by
  rw [estimate.localLogVolume_eq_packetNormalized]
  exact
    packetState.packetState.capsuleFamily.const_le_normalizedLogVolume_of_capsule_le
      hcapsule

theorem targetSigned_le_localLogVolume_of_capsule_estimates
    (estimate :
      IUTStage1PacketNormalizedContainerEstimate
        packetState targetSigned localLogVolume)
    (capsuleEstimates :
      IUTStage1TypedCapsuleFamilyContainerEstimate
        targetSigned packetState.packetState.capsuleFamily) :
    targetSigned <= localLogVolume :=
  estimate.targetSigned_le_localLogVolume_of_capsule_le
    capsuleEstimates.targetSigned_le_capsuleLogVolume

end IUTStage1PacketNormalizedContainerEstimate

namespace IUTStage1UpperSemiCompatibilityState

set_option linter.style.longLine false in
/--
Concrete upper-semi transport between upper-semi compatibility states.

The theta-pilot fiber transport fixes the log-theta column after the canonical
`F_l` shift.  This transport records the remaining upper-semi data: the
compatibility identifier, place-family inclusion/surjection data, log-volume
compatibility datum, boolean guards, and the proposition being witnessed by the
compatibility proof.
-/
structure UpperSemiTransport
    (state₁ state₂ : IUTStage1UpperSemiCompatibilityState) : Prop where
  compatibility_eq : state₁.compatibility = state₂.compatibility
  nonarchimedeanInclusions_eq :
    state₁.nonarchimedeanInclusions = state₂.nonarchimedeanInclusions
  archimedeanSurjections_eq :
    state₁.archimedeanSurjections = state₂.archimedeanSurjections
  logVolumeCompatibility_eq :
    state₁.logVolumeCompatibility = state₂.logVolumeCompatibility
  hasNonarchimedeanInclusions_eq :
    state₁.hasNonarchimedeanInclusions = state₂.hasNonarchimedeanInclusions
  hasArchimedeanSurjections_eq :
    state₁.hasArchimedeanSurjections = state₂.hasArchimedeanSurjections
  logVolumeCompatible_eq :
    state₁.logVolumeCompatible = state₂.logVolumeCompatible

theorem UpperSemiTransport.ofEq
    {state₁ state₂ : IUTStage1UpperSemiCompatibilityState}
    (h : state₁ = state₂) :
    UpperSemiTransport state₁ state₂ := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem logVolumeCompatibleProof
    (state : IUTStage1UpperSemiCompatibilityState) :
    state.logVolumeCompatible :=
  state.log_volume_compatible

theorem same_logThetaColumn_of_eq
    {state₁ state₂ : IUTStage1UpperSemiCompatibilityState}
    (h : state₁ = state₂) :
    state₁.logThetaColumn = state₂.logThetaColumn := by
  cases h
  rfl

theorem same_compatibility_of_eq
    {state₁ state₂ : IUTStage1UpperSemiCompatibilityState}
    (h : state₁ = state₂) :
    state₁.compatibility = state₂.compatibility := by
  cases h
  rfl

theorem UpperSemiTransport.eq_of_logThetaColumn_eq
    {state₁ state₂ : IUTStage1UpperSemiCompatibilityState}
    (transport : UpperSemiTransport state₁ state₂)
    (logThetaColumn_eq :
      state₁.logThetaColumn = state₂.logThetaColumn) :
    state₁ = state₂ := by
  cases state₁ with
  | mk logThetaColumn₁ compatibility₁ nonarch₁ arch₁ logVolume₁
      hasNonarch₁ hasArch₁ compatible₁ proof₁ =>
  cases state₂ with
  | mk logThetaColumn₂ compatibility₂ nonarch₂ arch₂ logVolume₂
      hasNonarch₂ hasArch₂ compatible₂ proof₂ =>
  cases logThetaColumn_eq
  cases transport.compatibility_eq
  cases transport.nonarchimedeanInclusions_eq
  cases transport.archimedeanSurjections_eq
  cases transport.logVolumeCompatibility_eq
  cases transport.hasNonarchimedeanInclusions_eq
  cases transport.hasArchimedeanSurjections_eq
  cases transport.logVolumeCompatible_eq
  exact congrArg
    (fun proof =>
      IUTStage1UpperSemiCompatibilityState.mk logThetaColumn₁ compatibility₁
        nonarch₁ arch₁ logVolume₁ hasNonarch₁ hasArch₁ compatible₁ proof)
    (Subsingleton.elim proof₁ proof₂)

theorem logVolumeUpperBound
    (state : IUTStage1UpperSemiCompatibilityState) :
    state.logVolumeCompatibility.sourceLogVolume <=
      state.logVolumeCompatibility.targetLogVolume :=
  state.logVolumeCompatibility.upperBound

end IUTStage1UpperSemiCompatibilityState
end Stage1
end Iut
