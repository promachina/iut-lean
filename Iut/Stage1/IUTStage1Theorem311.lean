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
Concrete log-theta-lattice coordinate used by the Theorem 3.11 source layer.

The column and row are the `n,m` coordinates of the LGP-Gaussian
log-theta-lattice.  The `F_l` label is the finite label retained by the
procession layer of Remark 3.11.2.
-/
structure IUTStage1Theorem311LogThetaLatticeCoordinate
    (l : PrimeGeFive) where
  column : Int
  row : Int
  flLabel : ZMod l.value
  logThetaColumn : LogThetaColumnId

/--
Theta-pilot log-theta lattice coordinate after forgetting the finite
`F_l`-procession label.

This is the lattice part of the theta-pilot class: the column, row, and
log-theta column survive the `(Ind1)` label/procession ambiguity, while the
finite label is remembered only by a representative section.
-/
structure IUTStage1Theorem311ThetaPilotLatticeCoordinate where
  column : Int
  row : Int
  logThetaColumn : LogThetaColumnId

namespace IUTStage1Theorem311LogThetaLatticeCoordinate

variable {l : PrimeGeFive}

/-- Translate the finite `F_l` procession label while preserving the lattice node. -/
def translateFLLabel
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (t : ZMod l.value) :
    IUTStage1Theorem311LogThetaLatticeCoordinate l :=
  { column := coordinate.column,
    row := coordinate.row,
    flLabel := zmodLabelTranslate l t coordinate.flLabel,
    logThetaColumn := coordinate.logThetaColumn }

theorem translateFLLabel_zero
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    coordinate.translateFLLabel 0 = coordinate := by
  cases coordinate
  simp [translateFLLabel, zmodLabelTranslate_zero]

theorem translateFLLabel_add
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (t u : ZMod l.value) :
    coordinate.translateFLLabel (t + u) =
      (coordinate.translateFLLabel u).translateFLLabel t := by
  cases coordinate
  simp [translateFLLabel, zmodLabelTranslate_add]

/-- Forget the finite `F_l` label, retaining the theta-pilot lattice node. -/
def toThetaPilotLatticeCoordinate
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    IUTStage1Theorem311ThetaPilotLatticeCoordinate :=
  { column := coordinate.column,
    row := coordinate.row,
    logThetaColumn := coordinate.logThetaColumn }

theorem toThetaPilotLatticeCoordinate_translateFLLabel
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (t : ZMod l.value) :
    (coordinate.translateFLLabel t).toThetaPilotLatticeCoordinate =
      coordinate.toThetaPilotLatticeCoordinate := by
  rfl

set_option linter.style.longLine false in
/--
The finite `F_l` label correction between two coordinates over the same
theta-pilot lattice node is the additive torsor difference of their labels.
-/
theorem translateFLLabel_sub_eq_of_toThetaPilotLatticeCoordinate_eq
    {coordinate₁ coordinate₂ : IUTStage1Theorem311LogThetaLatticeCoordinate l}
    (hlattice :
      coordinate₁.toThetaPilotLatticeCoordinate =
        coordinate₂.toThetaPilotLatticeCoordinate) :
    coordinate₁.translateFLLabel
        (coordinate₂.flLabel - coordinate₁.flLabel) =
      coordinate₂ := by
  rcases coordinate₁ with ⟨column₁, row₁, flLabel₁, logThetaColumn₁⟩
  rcases coordinate₂ with ⟨column₂, row₂, flLabel₂, logThetaColumn₂⟩
  have hfields :
      column₁ = column₂ ∧ row₁ = row₂ ∧
        logThetaColumn₁ = logThetaColumn₂ := by
    simpa [toThetaPilotLatticeCoordinate] using hlattice
  rcases hfields with ⟨hcolumn, hrow, hlogThetaColumn⟩
  subst column₂
  subst row₂
  subst logThetaColumn₂
  simp [translateFLLabel, zmodLabelTranslate_eq_add, sub_eq_add_neg, add_assoc]

set_option linter.style.longLine false in
/--
Unique finite `F_l` translation aligning two concrete log-theta coordinates
over the same theta-pilot lattice node.

This is the coordinate-level form of the finite torsor assertion used in the
Theorem 3.11 procession layer: once the `F_l` label is forgotten, there is a
unique label correction that restores any chosen representative.
-/
theorem existsUnique_translateFLLabel_eq_of_toThetaPilotLatticeCoordinate_eq
    {coordinate₁ coordinate₂ : IUTStage1Theorem311LogThetaLatticeCoordinate l}
    (hlattice :
      coordinate₁.toThetaPilotLatticeCoordinate =
        coordinate₂.toThetaPilotLatticeCoordinate) :
    ∃! t : ZMod l.value, coordinate₁.translateFLLabel t = coordinate₂ := by
  refine ⟨coordinate₂.flLabel - coordinate₁.flLabel, ?_, ?_⟩
  · exact translateFLLabel_sub_eq_of_toThetaPilotLatticeCoordinate_eq hlattice
  · intro t ht
    have hlabel :
        zmodLabelTranslate l t coordinate₁.flLabel = coordinate₂.flLabel := by
      simpa [translateFLLabel] using
        congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.flLabel ht
    exact
      (zmodLabelTranslate_existsUnique l coordinate₁.flLabel coordinate₂.flLabel).unique
        hlabel
        (by simp [zmodLabelTranslate_eq_add, sub_eq_add_neg, add_assoc])

/-- Replace the finite `F_l` label while leaving the log-theta lattice node fixed. -/
def withFLLabel
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (label : ZMod l.value) :
    IUTStage1Theorem311LogThetaLatticeCoordinate l :=
  { column := coordinate.column,
    row := coordinate.row,
    flLabel := label,
    logThetaColumn := coordinate.logThetaColumn }

theorem withFLLabel_flLabel
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (label : ZMod l.value) :
    (coordinate.withFLLabel label).flLabel = label :=
  rfl

theorem withFLLabel_toThetaPilotLatticeCoordinate
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l)
    (label : ZMod l.value) :
    (coordinate.withFLLabel label).toThetaPilotLatticeCoordinate =
      coordinate.toThetaPilotLatticeCoordinate :=
  rfl

theorem withFLLabel_self
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    coordinate.withFLLabel coordinate.flLabel = coordinate := by
  cases coordinate
  rfl

set_option linter.style.longLine false in
theorem withFLLabel_eq_iff
    {base coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l}
    {label : ZMod l.value} :
    base.withFLLabel label = coordinate ↔
      base.toThetaPilotLatticeCoordinate =
          coordinate.toThetaPilotLatticeCoordinate ∧
        label = coordinate.flLabel := by
  rcases base with ⟨baseColumn, baseRow, baseLabel, baseLogThetaColumn⟩
  rcases coordinate with
    ⟨coordinateColumn, coordinateRow, coordinateLabel,
      coordinateLogThetaColumn⟩
  simp [withFLLabel, toThetaPilotLatticeCoordinate]
  tauto

end IUTStage1Theorem311LogThetaLatticeCoordinate

/--
Full `F_l` label procession source over a fixed log-theta lattice node.

Remark 3.11.2 emphasizes that the transition from labels to processions uses
all labels in `F_l`; no label may be omitted.  This source object records the
full `ZMod l` label family over one theta-pilot lattice node.  The finite labels
are arithmetic-holomorphic representatives, while the forgotten lattice node is
the naked procession index data used by the multiradial quotient.
-/
structure IUTStage1FLLabelProcessionSource
    (l : PrimeGeFive) where
  baseCoordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l

namespace IUTStage1FLLabelProcessionSource

variable {l : PrimeGeFive}

/-- The canonical full-label source over a fixed log-theta coordinate. -/
def ofCoordinate
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    IUTStage1FLLabelProcessionSource l :=
  { baseCoordinate := coordinate }

@[simp]
theorem ofCoordinate_baseCoordinate
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    (ofCoordinate coordinate).baseCoordinate = coordinate :=
  rfl

/-- The coordinate obtained by choosing a particular full `F_l` label. -/
def coordinate
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    IUTStage1Theorem311LogThetaLatticeCoordinate l :=
  source.baseCoordinate.withFLLabel label

theorem coordinate_flLabel
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    (source.coordinate label).flLabel = label :=
  rfl

theorem coordinate_toThetaPilotLatticeCoordinate
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    (source.coordinate label).toThetaPilotLatticeCoordinate =
      source.baseCoordinate.toThetaPilotLatticeCoordinate :=
  rfl

theorem coordinate_column
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    (source.coordinate label).column = source.baseCoordinate.column :=
  rfl

theorem coordinate_row
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    (source.coordinate label).row = source.baseCoordinate.row :=
  rfl

theorem coordinate_logThetaColumn
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    (source.coordinate label).logThetaColumn =
      source.baseCoordinate.logThetaColumn :=
  rfl

/-- The full `F_l` label family has exactly `l` labels. -/
theorem label_cardinality
    (_source : IUTStage1FLLabelProcessionSource l) :
    Fintype.card (ZMod l.value) = l.value := by
  exact ZMod.card l.value

/-- Translation of labels agrees with translation of the coordinate representative. -/
theorem coordinate_translate
    (source : IUTStage1FLLabelProcessionSource l)
    (t label : ZMod l.value) :
    source.coordinate (zmodLabelTranslate l t label) =
      (source.coordinate label).translateFLLabel t := by
  cases source
  rfl

/-- Every label of `F_l` occurs in the source family. -/
theorem label_present
    (source : IUTStage1FLLabelProcessionSource l)
    (label : ZMod l.value) :
    ∃ coordinate,
      coordinate = source.coordinate label ∧
        coordinate.flLabel = label ∧
          coordinate.toThetaPilotLatticeCoordinate =
            source.baseCoordinate.toThetaPilotLatticeCoordinate :=
  ⟨source.coordinate label, rfl, rfl, rfl⟩

set_option linter.style.longLine false in
/--
Any coordinate over the same forgotten theta-pilot lattice node occurs with a
unique full `F_l` label.
-/
theorem existsUnique_label_of_toThetaPilotLatticeCoordinate_eq
    (source : IUTStage1FLLabelProcessionSource l)
    {coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l}
    (hlattice :
      source.baseCoordinate.toThetaPilotLatticeCoordinate =
        coordinate.toThetaPilotLatticeCoordinate) :
    ∃! label : ZMod l.value, source.coordinate label = coordinate := by
  refine ⟨coordinate.flLabel, ?_, ?_⟩
  · exact
      (IUTStage1Theorem311LogThetaLatticeCoordinate.withFLLabel_eq_iff).2
        ⟨hlattice, rfl⟩
  · intro label hlabel
    simpa [IUTStage1FLLabelProcessionSource.coordinate] using
      congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.flLabel hlabel

/--
Audit for the full-label procession source used in Remark 3.11.2.

The fields record cardinality, no omission, uniqueness of the label over the
forgotten lattice node, and compatibility of the finite torsor action with
coordinate translation.
-/
structure FullLabelProcessionAudit
    (source : IUTStage1FLLabelProcessionSource l) : Prop where
  label_cardinality : Fintype.card (ZMod l.value) = l.value
  all_labels_present :
    ∀ label : ZMod l.value,
      ∃ coordinate,
        coordinate = source.coordinate label ∧
          coordinate.flLabel = label ∧
            coordinate.toThetaPilotLatticeCoordinate =
              source.baseCoordinate.toThetaPilotLatticeCoordinate
  unique_label_over_lattice :
    ∀ coordinate,
      source.baseCoordinate.toThetaPilotLatticeCoordinate =
          coordinate.toThetaPilotLatticeCoordinate ->
        ∃! label : ZMod l.value, source.coordinate label = coordinate
  translation_action :
    ∀ t label : ZMod l.value,
      source.coordinate (zmodLabelTranslate l t label) =
        (source.coordinate label).translateFLLabel t

theorem fullLabelProcessionAudit
    (source : IUTStage1FLLabelProcessionSource l) :
    source.FullLabelProcessionAudit :=
  { label_cardinality := source.label_cardinality,
    all_labels_present := by
      intro label
      exact source.label_present label,
    unique_label_over_lattice := by
      intro coordinate hlattice
      exact source.existsUnique_label_of_toThetaPilotLatticeCoordinate_eq hlattice,
    translation_action := by
      intro t label
      exact source.coordinate_translate t label }

end IUTStage1FLLabelProcessionSource

/--
Naked index set of the mono-analytic `±`-procession component labeled by `j`.

IUT III, Remark 3.11.2 says that these index sets are not arithmetic
holomorphic data: they are determined, up to isomorphism, only by cardinality.
For the component labeled `j`, the cardinality is `j + 1`.
-/
abbrev IUTStage1PlusMinusProcessionIndexSet
    (j : Nat) : Type :=
  Fin (j + 1)

namespace IUTStage1PlusMinusProcessionIndexSet

/-- The index set labeled by `j` has exactly `j + 1` elements. -/
theorem cardinality
    (j : Nat) :
    Fintype.card (IUTStage1PlusMinusProcessionIndexSet j) = j + 1 := by
  simp [IUTStage1PlusMinusProcessionIndexSet]

/--
Any finite type of cardinality `j + 1` is a valid naked model of the same
`±`-procession index set.
-/
noncomputable def nakedEquiv
    (j : Nat) (α : Type u) [Fintype α]
    (hcard : Fintype.card α = j + 1) :
    α ≃ IUTStage1PlusMinusProcessionIndexSet j :=
  Fintype.equivFinOfCardEq hcard

theorem naked_equiv_nonempty
    (j : Nat) (α : Type u) [Fintype α]
    (hcard : Fintype.card α = j + 1) :
    Nonempty (α ≃ IUTStage1PlusMinusProcessionIndexSet j) :=
  ⟨nakedEquiv j α hcard⟩

end IUTStage1PlusMinusProcessionIndexSet

/--
The type of all label-identification choices for mono-analytic
`±`-procession index sets over `j = 0, ..., l`.

For each `j`, one chooses an element of a naked index set of cardinality
`j + 1`; the total number of choices is `(l + 1)!`.
-/
abbrev IUTStage1PlusMinusProcessionLabelIdentification
    (l : PrimeGeFive) : Type :=
  (j : Fin (l.value + 1)) ->
    IUTStage1PlusMinusProcessionIndexSet j.1

namespace IUTStage1PlusMinusProcessionLabelIdentification

variable {l : PrimeGeFive}

theorem component_cardinality
    (j : Fin (l.value + 1)) :
    Fintype.card (IUTStage1PlusMinusProcessionIndexSet j.1) = j.1 + 1 :=
  IUTStage1PlusMinusProcessionIndexSet.cardinality j.1

theorem range_product_cardinality
    (l : PrimeGeFive) :
    (∏ j ∈ Finset.range (l.value + 1),
        Fintype.card (IUTStage1PlusMinusProcessionIndexSet j)) =
      Nat.factorial (l.value + 1) := by
  simp [IUTStage1PlusMinusProcessionIndexSet,
    Finset.prod_range_add_one_eq_factorial]

theorem total_cardinality
    (l : PrimeGeFive) :
    Fintype.card (IUTStage1PlusMinusProcessionLabelIdentification l) =
      Nat.factorial (l.value + 1) := by
  rw [Fintype.card_pi]
  calc
    (∏ j : Fin (l.value + 1),
        Fintype.card (IUTStage1PlusMinusProcessionIndexSet j.1)) =
        ∏ j ∈ Finset.range (l.value + 1),
          Fintype.card (IUTStage1PlusMinusProcessionIndexSet j) := by
      exact Fin.prod_univ_eq_prod_range
        (fun j => Fintype.card (IUTStage1PlusMinusProcessionIndexSet j))
        (l.value + 1)
    _ = Nat.factorial (l.value + 1) :=
      range_product_cardinality l

set_option linter.style.longLine false in
/--
Audit for the naked mono-analytic `±`-procession index sets of Remark 3.11.2.

It records the per-label cardinality `j + 1`, the fact that any finite set of
that cardinality is equivalent to the chosen model, and the total
`(l + 1)! = l^{±}!` count of label-identification choices.
-/
structure Audit
    (l : PrimeGeFive) : Prop where
  component_cardinality :
    ∀ j : Fin (l.value + 1),
      Fintype.card (IUTStage1PlusMinusProcessionIndexSet j.1) = j.1 + 1
  naked_by_cardinality :
    ∀ (j : Fin (l.value + 1)) (α : Type u) [Fintype α],
      Fintype.card α = j.1 + 1 ->
        Nonempty (α ≃ IUTStage1PlusMinusProcessionIndexSet j.1)
  total_label_identification_cardinality :
    Fintype.card (IUTStage1PlusMinusProcessionLabelIdentification l) =
      Nat.factorial (l.value + 1)
  range_product_cardinality :
    (∏ j ∈ Finset.range (l.value + 1),
        Fintype.card (IUTStage1PlusMinusProcessionIndexSet j)) =
      Nat.factorial (l.value + 1)

theorem audit
    (l : PrimeGeFive) :
    Audit l :=
  { component_cardinality := by
      intro j
      exact component_cardinality j,
    naked_by_cardinality := by
      intro j α _ hcard
      exact
        IUTStage1PlusMinusProcessionIndexSet.naked_equiv_nonempty
          j.1 α hcard,
    total_label_identification_cardinality := total_cardinality l,
    range_product_cardinality := range_product_cardinality l }

end IUTStage1PlusMinusProcessionLabelIdentification

/--
Plus-minus/absolute label procession source over a fixed log-theta lattice node.

Remark 3.11.2 distinguishes the full arithmetic-holomorphic `F_l` labels from
the labels in `|F_l|` that feed the mono-analytic `±`-processions.  In the finite
model already present in this corridor, `|F_l|` is the zero label together with
the sign quotient of nonzero `ZMod l` labels.
-/
structure IUTStage1AbsoluteFLLabelProcessionSource
    (l : PrimeGeFive) where
  fullLabelSource : IUTStage1FLLabelProcessionSource l

namespace IUTStage1AbsoluteFLLabelProcessionSource

variable {l : PrimeGeFive}

/-- Build the `|F_l|` source by quotienting a full `F_l` source by sign. -/
def ofFullLabelSource
    (source : IUTStage1FLLabelProcessionSource l) :
    IUTStage1AbsoluteFLLabelProcessionSource l :=
  { fullLabelSource := source }

/-- The absolute/plus-minus label attached to a full `F_l` coordinate. -/
def absoluteLabel
    (_source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (label : ZMod l.value) :
    IUTStage1ZModCuspFullLabel l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate l label

/-- The absolute/plus-minus label read from a concrete log-theta coordinate. -/
def absoluteLabelAtCoordinate
    (_source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l) :
    IUTStage1ZModCuspFullLabel l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate l coordinate.flLabel

theorem absoluteLabel_zero
    (source : IUTStage1AbsoluteFLLabelProcessionSource l) :
    source.absoluteLabel (0 : ZMod l.value) = IUTStage1ZModCuspFullLabel.zero :=
  IUTStage1ZModCuspFullLabel.fromCoordinate_zero l

theorem absoluteLabel_nonzero
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (label : ZMod l.value) (hlabel : label ≠ 0) :
    source.absoluteLabel label =
      IUTStage1ZModCuspFullLabel.nonzero
        (zmodSignLabelFromCoordinate l label hlabel) :=
  IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l label hlabel

theorem absoluteLabel_neg
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (label : ZMod l.value) (hlabel : label ≠ 0) :
    source.absoluteLabel (-label) = source.absoluteLabel label :=
  IUTStage1ZModCuspFullLabel.fromCoordinate_neg l label hlabel

theorem absoluteLabel_eq_iff
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (label₁ label₂ : ZMod l.value) :
    source.absoluteLabel label₁ = source.absoluteLabel label₂ ↔
      label₁ = label₂ ∨ label₁ = -label₂ :=
  IUTStage1ZModCuspFullLabel.fromCoordinate_eq_iff label₁ label₂

/-- Every label of `|F_l|` is represented by a full `F_l` label. -/
theorem all_absolute_labels_present
    (source : IUTStage1AbsoluteFLLabelProcessionSource l) :
    ∀ absLabel : IUTStage1ZModCuspFullLabel l,
      ∃ label : ZMod l.value, source.absoluteLabel label = absLabel :=
  IUTStage1ZModCuspFullLabel.fromCoordinate_surjective

theorem nonzero_absolute_label_fiber_eq_sign_pair
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (absLabel : (zmodSignAction l).SignLabelQuotient) :
    ∃ (label : ZMod l.value) (_hlabel : label ≠ 0),
      ∀ k : ZMod l.value,
        source.absoluteLabel k =
            IUTStage1ZModCuspFullLabel.nonzero absLabel ↔
          k = label ∨ k = -label :=
  IUTStage1ZModCuspFullLabel.nonzero_fullLabel_fiber_eq_sign_pair absLabel

set_option linter.style.longLine false in
/--
Compatibility of the ordinary `F_l` procession action with the induced
`|F_l|`/`±`-procession label map.

This is the Lean form of the Remark 3.11.2 compatibility between processions and
`±`-processions relative to the natural map `F_l -> |F_l|`.
-/
theorem ordinary_to_absolute_procession_compatibility
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (t label : ZMod l.value) :
    source.absoluteLabel (zmodLabelTranslate l t label) =
      source.absoluteLabelAtCoordinate
        ((source.fullLabelSource.coordinate label).translateFLLabel t) :=
  rfl

theorem full_label_coordinate_absoluteLabel
    (source : IUTStage1AbsoluteFLLabelProcessionSource l)
    (label : ZMod l.value) :
    source.absoluteLabel label =
      source.absoluteLabelAtCoordinate
        (source.fullLabelSource.coordinate label) :=
  rfl

set_option linter.style.longLine false in
/--
Audit for the passage `F_l -> |F_l| -> ±`-processions in Remark 3.11.2.

The audit reuses the full-label no-omission/cardinality facts, then proves the
source-paper quotient facts: zero is retained, nonzero labels descend to the
sign quotient, opposite labels are identified, every `|F_l|` label occurs, and
ordinary processions are compatible with `±`-processions.
-/
structure AbsoluteLabelProcessionAudit
    (source : IUTStage1AbsoluteFLLabelProcessionSource l) : Prop where
  full_label_audit : source.fullLabelSource.FullLabelProcessionAudit
  plus_minus_index_audit :
    IUTStage1PlusMinusProcessionLabelIdentification.Audit.{u} l
  all_absolute_labels_present :
    ∀ absLabel : IUTStage1ZModCuspFullLabel l,
      ∃ label : ZMod l.value, source.absoluteLabel label = absLabel
  zero_label :
    source.absoluteLabel (0 : ZMod l.value) = IUTStage1ZModCuspFullLabel.zero
  nonzero_label :
    ∀ (label : ZMod l.value) (hlabel : label ≠ 0),
      source.absoluteLabel label =
        IUTStage1ZModCuspFullLabel.nonzero
          (zmodSignLabelFromCoordinate l label hlabel)
  neg_identifies_opposite_labels :
    ∀ (label : ZMod l.value) (_hlabel : label ≠ 0),
      source.absoluteLabel (-label) = source.absoluteLabel label
  quotient_identification :
    ∀ label₁ label₂ : ZMod l.value,
      source.absoluteLabel label₁ = source.absoluteLabel label₂ ↔
        label₁ = label₂ ∨ label₁ = -label₂
  ordinary_to_absolute_procession_compatibility :
    ∀ t label : ZMod l.value,
      source.absoluteLabel (zmodLabelTranslate l t label) =
        source.absoluteLabelAtCoordinate
          ((source.fullLabelSource.coordinate label).translateFLLabel t)

theorem absoluteLabelProcessionAudit
    (source : IUTStage1AbsoluteFLLabelProcessionSource l) :
    source.AbsoluteLabelProcessionAudit :=
  { full_label_audit := source.fullLabelSource.fullLabelProcessionAudit,
    plus_minus_index_audit :=
      IUTStage1PlusMinusProcessionLabelIdentification.audit l,
    all_absolute_labels_present := source.all_absolute_labels_present,
    zero_label := source.absoluteLabel_zero,
    nonzero_label := by
      intro label hlabel
      exact source.absoluteLabel_nonzero label hlabel,
    neg_identifies_opposite_labels := by
      intro label hlabel
      exact source.absoluteLabel_neg label hlabel,
    quotient_identification := by
      intro label₁ label₂
      exact source.absoluteLabel_eq_iff label₁ label₂,
    ordinary_to_absolute_procession_compatibility := by
      intro t label
      exact source.ordinary_to_absolute_procession_compatibility t label }

end IUTStage1AbsoluteFLLabelProcessionSource

/--
Concrete Hodge-theater/log-theta choice for Theorem 3.11.

This is the first choice space in the corridor whose indices are not anonymous:
each choice carries a Hodge-theater identifier, an `n,m` log-theta coordinate,
an `F_l` label, and the current procession/tensor/upper-semi state data.  The
projection below is the existing structured Theorem 3.11 choice consumed by the
typed indeterminacy and multiradial layers.
-/
structure IUTStage1ConcreteHodgeTheaterLogThetaChoice
    (coric : Type u) (l : PrimeGeFive) where
  hodgeTheater : QualitativeData.HodgeTheaterId
  historyLabel : String
  coordinate : IUTStage1Theorem311LogThetaLatticeCoordinate l
  coric : coric
  procession_state : IUTStage1ProcessionState
  local_tensor_state : IUTStage1LocalTensorState
  upper_semi_state : IUTStage1UpperSemiCompatibilityState
  procession_column_eq :
    procession_state.column = coordinate.column
  upper_semi_logThetaColumn_eq :
    upper_semi_state.logThetaColumn = coordinate.logThetaColumn

namespace IUTStage1ConcreteHodgeTheaterLogThetaChoice

variable {coric : Type u} {l : PrimeGeFive}

def toStructuredChoice
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    IUTStage1StructuredTheorem311Choice coric :=
  { column := choice.coordinate.column,
    row := choice.coordinate.row,
    coric := choice.coric,
    procession_state := choice.procession_state,
    local_tensor_state := choice.local_tensor_state,
    upper_semi_state := choice.upper_semi_state }

theorem toStructuredChoice_column
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    choice.toStructuredChoice.column = choice.coordinate.column :=
  rfl

theorem toStructuredChoice_row
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    choice.toStructuredChoice.row = choice.coordinate.row :=
  rfl

/-- Translate the concrete choice by the finite `F_l` procession label. -/
def flProcessionTranslate
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l :=
  { hodgeTheater := choice.hodgeTheater,
    historyLabel := choice.historyLabel,
    coordinate := choice.coordinate.translateFLLabel t,
    coric := choice.coric,
    procession_state := choice.procession_state,
    local_tensor_state := choice.local_tensor_state,
    upper_semi_state := choice.upper_semi_state,
    procession_column_eq := choice.procession_column_eq,
    upper_semi_logThetaColumn_eq := choice.upper_semi_logThetaColumn_eq }

theorem flProcessionTranslate_zero
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    flProcessionTranslate 0 choice = choice := by
  cases choice
  simp [flProcessionTranslate,
    IUTStage1Theorem311LogThetaLatticeCoordinate.translateFLLabel_zero]

theorem flProcessionTranslate_add
    (t u : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    flProcessionTranslate (t + u) choice =
      flProcessionTranslate t (flProcessionTranslate u choice) := by
  cases choice
  simp [flProcessionTranslate,
    IUTStage1Theorem311LogThetaLatticeCoordinate.translateFLLabel_add]

theorem flProcessionTranslate_flLabel
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (flProcessionTranslate t choice).coordinate.flLabel =
      zmodLabelTranslate l t choice.coordinate.flLabel :=
  rfl

/--
Theta-pilot class of a concrete Hodge-theater/log-theta choice.

This is the source-side class that remains after forgetting the finite
`F_l`-procession label and the local tensor representative.  It keeps the
Hodge-theater history, the `n,m` log-theta lattice position, the
log-theta-column, and the coric datum.  Thus `(Ind1)` label/procession changes
and `(Ind2)` local tensor changes preserve the class, while `(Ind3)` row changes
are deliberately not quotient data.
-/
structure ThetaPilotClass where
  hodgeTheater : QualitativeData.HodgeTheaterId
  historyLabel : String
  column : Int
  row : Int
  logThetaColumn : LogThetaColumnId
  coric : coric

namespace ThetaPilotClass

/-- The log-theta lattice coordinate carried by a theta-pilot class. -/
def latticeCoordinate
    (thetaClass : ThetaPilotClass (coric := coric)) :
    IUTStage1Theorem311ThetaPilotLatticeCoordinate :=
  { column := thetaClass.column,
    row := thetaClass.row,
    logThetaColumn := thetaClass.logThetaColumn }

set_option linter.style.longLine false in
/--
Canonical zero-label representative of the theta-pilot log-theta lattice node.

The theta-pilot class has forgotten the finite `F_l` label.  This section picks
the zero label only to generate the full label procession; the subsequent
average ranges over all labels and is independent of this representative
choice.
-/
def zeroLabelCoordinate
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    IUTStage1Theorem311LogThetaLatticeCoordinate l :=
  { column := thetaClass.column,
    row := thetaClass.row,
    flLabel := 0,
    logThetaColumn := thetaClass.logThetaColumn }

theorem zeroLabelCoordinate_flLabel
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    (thetaClass.zeroLabelCoordinate l).flLabel = 0 :=
  rfl

theorem zeroLabelCoordinate_toThetaPilotLatticeCoordinate
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    (thetaClass.zeroLabelCoordinate l).toThetaPilotLatticeCoordinate =
      thetaClass.latticeCoordinate :=
  rfl

/-- Full `F_l` label procession over the theta-pilot class's lattice node. -/
def flLabelProcessionSource
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    IUTStage1FLLabelProcessionSource l :=
  IUTStage1FLLabelProcessionSource.ofCoordinate
    (thetaClass.zeroLabelCoordinate l)

theorem flLabelProcessionSource_latticeCoordinate
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    (thetaClass.flLabelProcessionSource l).baseCoordinate.toThetaPilotLatticeCoordinate =
      thetaClass.latticeCoordinate :=
  rfl

theorem flLabelProcessionSource_fullLabelAudit
    (thetaClass : ThetaPilotClass (coric := coric))
    (l : PrimeGeFive) :
    (thetaClass.flLabelProcessionSource l).FullLabelProcessionAudit :=
  (thetaClass.flLabelProcessionSource l).fullLabelProcessionAudit

end ThetaPilotClass

/-- Forget the `F_l` label and local tensor representative of a concrete choice. -/
def thetaPilotClass
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    ThetaPilotClass (coric := coric) :=
  { hodgeTheater := choice.hodgeTheater,
    historyLabel := choice.historyLabel,
    column := choice.coordinate.column,
    row := choice.coordinate.row,
    logThetaColumn := choice.coordinate.logThetaColumn,
    coric := choice.coric }

/-- The log-theta lattice part of a concrete choice after forgetting `F_l`. -/
def thetaPilotLatticeCoordinate
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    IUTStage1Theorem311ThetaPilotLatticeCoordinate :=
  choice.coordinate.toThetaPilotLatticeCoordinate

theorem thetaPilotClass_latticeCoordinate
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (thetaPilotClass choice).latticeCoordinate =
      thetaPilotLatticeCoordinate choice := by
  rfl

theorem thetaPilotClass_eq_of_latticeKey_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hhodge : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (hhistory : choice₁.historyLabel = choice₂.historyLabel)
    (hlattice :
      thetaPilotLatticeCoordinate choice₁ =
        thetaPilotLatticeCoordinate choice₂)
    (hcoric : choice₁.coric = choice₂.coric) :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ := by
  rcases choice₁ with
    ⟨hodge1, history1, coordinate1, coric1, procession1, local1, upper1,
      hprocession1, hupper1⟩
  rcases choice₂ with
    ⟨hodge2, history2, coordinate2, coric2, procession2, local2, upper2,
      hprocession2, hupper2⟩
  rcases coordinate1 with ⟨column1, row1, flLabel1, logThetaColumn1⟩
  rcases coordinate2 with ⟨column2, row2, flLabel2, logThetaColumn2⟩
  have hlatticeFields :
      column1 = column2 ∧ row1 = row2 ∧
        logThetaColumn1 = logThetaColumn2 := by
    simpa [thetaPilotLatticeCoordinate,
      IUTStage1Theorem311LogThetaLatticeCoordinate.toThetaPilotLatticeCoordinate]
      using hlattice
  have hhodgeField : hodge1 = hodge2 := by
    simpa using hhodge
  have hhistoryField : history1 = history2 := by
    simpa using hhistory
  have hcoricField : coric1 = coric2 := by
    simpa using hcoric
  rcases hlatticeFields with ⟨hcolumn, hrow, hlogThetaColumn⟩
  subst hodge2
  subst history2
  subst column2
  subst row2
  subst logThetaColumn2
  subst coric2
  rfl

theorem hodgeTheater_eq_of_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hclass : thetaPilotClass choice₁ = thetaPilotClass choice₂) :
    choice₁.hodgeTheater = choice₂.hodgeTheater := by
  simpa [thetaPilotClass] using
    congrArg ThetaPilotClass.hodgeTheater hclass

theorem historyLabel_eq_of_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hclass : thetaPilotClass choice₁ = thetaPilotClass choice₂) :
    choice₁.historyLabel = choice₂.historyLabel := by
  simpa [thetaPilotClass] using
    congrArg ThetaPilotClass.historyLabel hclass

theorem thetaPilotLatticeCoordinate_eq_of_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hclass : thetaPilotClass choice₁ = thetaPilotClass choice₂) :
    thetaPilotLatticeCoordinate choice₁ =
      thetaPilotLatticeCoordinate choice₂ := by
  simpa [thetaPilotClass_latticeCoordinate] using
    congrArg ThetaPilotClass.latticeCoordinate hclass

theorem coric_eq_of_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hclass : thetaPilotClass choice₁ = thetaPilotClass choice₂) :
    choice₁.coric = choice₂.coric := by
  simpa [thetaPilotClass] using
    congrArg ThetaPilotClass.coric hclass

theorem thetaPilotClass_eq_iff_latticeKey_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l} :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ ↔
      choice₁.hodgeTheater = choice₂.hodgeTheater ∧
        choice₁.historyLabel = choice₂.historyLabel ∧
          thetaPilotLatticeCoordinate choice₁ =
            thetaPilotLatticeCoordinate choice₂ ∧
            choice₁.coric = choice₂.coric := by
  constructor
  · intro hclass
    exact
      ⟨hodgeTheater_eq_of_thetaPilotClass_eq hclass,
        historyLabel_eq_of_thetaPilotClass_eq hclass,
        thetaPilotLatticeCoordinate_eq_of_thetaPilotClass_eq hclass,
        coric_eq_of_thetaPilotClass_eq hclass⟩
  · rintro ⟨hhodge, hhistory, hlattice, hcoric⟩
    exact
      thetaPilotClass_eq_of_latticeKey_eq
        hhodge hhistory hlattice hcoric

theorem thetaPilotClass_flProcessionTranslate
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    thetaPilotClass (flProcessionTranslate t choice) =
      thetaPilotClass choice := by
  rfl

theorem thetaPilotLatticeCoordinate_flProcessionTranslate
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    thetaPilotLatticeCoordinate (flProcessionTranslate t choice) =
      thetaPilotLatticeCoordinate choice := by
  rfl

/--
Source-side representatives for concrete theta-pilot classes.

The theta-pilot class has forgotten the finite `F_l` label, the procession
representative, the local tensor representative, and the upper-semi
representative.  This data records a section of that forgetting map, together
with the two coherence laws needed to rebuild a concrete
Hodge-theater/log-theta choice.
-/
structure ThetaPilotClassRepresentativeData
    (coric : Type u) (l : PrimeGeFive) where
  flLabel :
    ThetaPilotClass (coric := coric) -> ZMod l.value
  procession_state :
    ThetaPilotClass (coric := coric) -> IUTStage1ProcessionState
  local_tensor_state :
    ThetaPilotClass (coric := coric) -> IUTStage1LocalTensorState
  upper_semi_state :
    ThetaPilotClass (coric := coric) ->
      IUTStage1UpperSemiCompatibilityState
  procession_column_eq :
    ∀ thetaClass,
      (procession_state thetaClass).column = thetaClass.column
  upper_semi_logThetaColumn_eq :
    ∀ thetaClass,
      (upper_semi_state thetaClass).logThetaColumn =
        thetaClass.logThetaColumn

namespace ThetaPilotClassRepresentativeData

variable
  (data : ThetaPilotClassRepresentativeData coric l)

/-- Rebuild a concrete choice from a theta-pilot class and chosen forgotten data. -/
def representative
    (thetaClass : ThetaPilotClass (coric := coric)) :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l :=
  { hodgeTheater := thetaClass.hodgeTheater,
    historyLabel := thetaClass.historyLabel,
    coordinate :=
      { column := thetaClass.column,
        row := thetaClass.row,
        flLabel := data.flLabel thetaClass,
        logThetaColumn := thetaClass.logThetaColumn },
    coric := thetaClass.coric,
    procession_state := data.procession_state thetaClass,
    local_tensor_state := data.local_tensor_state thetaClass,
    upper_semi_state := data.upper_semi_state thetaClass,
    procession_column_eq := data.procession_column_eq thetaClass,
    upper_semi_logThetaColumn_eq :=
      data.upper_semi_logThetaColumn_eq thetaClass }

theorem thetaPilotClass_representative
    (thetaClass : ThetaPilotClass (coric := coric)) :
    thetaPilotClass (data.representative thetaClass) = thetaClass := by
  cases thetaClass
  rfl

end ThetaPilotClassRepresentativeData

/--
Concrete `(Ind1)` step induced by an automorphism of the procession of
D-prime-strips.

It preserves the Hodge-theater history and the log-theta lattice node, but it
may change the finite `F_l` label.  This matches the label/procession passage of
Remark 3.11.2 and descends to the existing structured
procession-automorphism step, which does not see the finite label.
-/
structure Ind1ProcessionStep
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  row_eq : choice₁.coordinate.row = choice₂.coordinate.row
  logThetaColumn_eq :
    choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn
  structured_step :
    IUTStage1StructuredTheorem311Choice.ProcessionAutomorphismStep
      choice₁.toStructuredChoice choice₂.toStructuredChoice

theorem flProcessionTranslate_ind1Step
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    Ind1ProcessionStep choice (flProcessionTranslate t choice) :=
  { hodgeTheater_eq := rfl,
    historyLabel_eq := rfl,
    column_eq := rfl,
    row_eq := rfl,
    logThetaColumn_eq := rfl,
    structured_step :=
      { column_eq := rfl,
        row_eq := rfl,
        coric_eq := rfl,
        procession_eq := rfl,
        procession_column_eq := rfl,
        local_tensor_eq := rfl,
        upper_semi_eq := rfl } }

theorem ind1_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind1ProcessionStep choice₁ choice₂) :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ := by
  have hcoric : choice₁.coric = choice₂.coric := by
    simpa [toStructuredChoice] using hstep.structured_step.coric_eq
  simp [thetaPilotClass, hstep.hodgeTheater_eq, hstep.historyLabel_eq,
    hstep.column_eq, hstep.row_eq, hstep.logThetaColumn_eq, hcoric]

set_option linter.style.longLine false in
/--
Full `F_l` label procession source attached to a concrete Hodge-theater choice.

The source varies only the finite `F_l` label of the log-theta coordinate.  The
procession state, local tensor state, upper-semi state, Hodge-theater history,
and coric datum are fixed.  This is the concrete choice-level form of the
Remark 3.11.2 transition from all labels in `F_l` to the naked procession
representatives used by `(Ind1)`.
-/
structure FLLabelProcessionChoiceSource
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) where
  labelSource : IUTStage1FLLabelProcessionSource l
  base_coordinate_eq : labelSource.baseCoordinate = choice.coordinate

namespace FLLabelProcessionChoiceSource

set_option linter.style.longLine false in
/--
Canonical full-label source attached to a concrete choice.

It uses the choice's own log-theta coordinate as the forgotten theta-pilot
lattice node, then varies only the finite `F_l` label.
-/
def ofChoice
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    FLLabelProcessionChoiceSource choice :=
  { labelSource :=
      IUTStage1FLLabelProcessionSource.ofCoordinate choice.coordinate,
    base_coordinate_eq := rfl }

@[simp]
theorem ofChoice_baseCoordinate
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (ofChoice choice).labelSource.baseCoordinate = choice.coordinate :=
  rfl

set_option linter.style.longLine false in
/-- The concrete choice with its finite `F_l` label replaced by `label`. -/
def choiceAt
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l :=
  { hodgeTheater := choice.hodgeTheater,
    historyLabel := choice.historyLabel,
    coordinate := source.labelSource.coordinate label,
    coric := choice.coric,
    procession_state := choice.procession_state,
    local_tensor_state := choice.local_tensor_state,
    upper_semi_state := choice.upper_semi_state,
    procession_column_eq := by
      calc
        choice.procession_state.column = choice.coordinate.column :=
          choice.procession_column_eq
        _ = source.labelSource.baseCoordinate.column := by
          simpa using
            congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.column
              source.base_coordinate_eq.symm
        _ = (source.labelSource.coordinate label).column := by
          rfl,
    upper_semi_logThetaColumn_eq := by
      calc
        choice.upper_semi_state.logThetaColumn =
            choice.coordinate.logThetaColumn :=
          choice.upper_semi_logThetaColumn_eq
        _ = source.labelSource.baseCoordinate.logThetaColumn := by
          simpa using
            congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.logThetaColumn
              source.base_coordinate_eq.symm
        _ = (source.labelSource.coordinate label).logThetaColumn := by
          rfl }

theorem choiceAt_flLabel
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    (source.choiceAt label).coordinate.flLabel = label :=
  rfl

theorem choiceAt_thetaPilotLatticeCoordinate
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    thetaPilotLatticeCoordinate (source.choiceAt label) =
      thetaPilotLatticeCoordinate choice := by
  simp [thetaPilotLatticeCoordinate, choiceAt,
    IUTStage1FLLabelProcessionSource.coordinate_toThetaPilotLatticeCoordinate,
    source.base_coordinate_eq]

set_option linter.style.longLine false in
/--
Every full-label representative is an `(Ind1)` procession step from the base
choice.
-/
theorem ind1Step_choiceAt
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    Ind1ProcessionStep choice (source.choiceAt label) :=
  { hodgeTheater_eq := rfl,
    historyLabel_eq := rfl,
    column_eq := by
      calc
        choice.coordinate.column = source.labelSource.baseCoordinate.column := by
          simpa using
            congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.column
              source.base_coordinate_eq.symm
        _ = (source.labelSource.coordinate label).column := by
          rfl,
    row_eq := by
      calc
        choice.coordinate.row = source.labelSource.baseCoordinate.row := by
          simpa using
            congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.row
              source.base_coordinate_eq.symm
        _ = (source.labelSource.coordinate label).row := by
          rfl,
    logThetaColumn_eq := by
      calc
        choice.coordinate.logThetaColumn =
            source.labelSource.baseCoordinate.logThetaColumn := by
          simpa using
            congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.logThetaColumn
              source.base_coordinate_eq.symm
        _ = (source.labelSource.coordinate label).logThetaColumn := by
          rfl,
    structured_step :=
      { column_eq := by
          calc
            choice.coordinate.column =
                source.labelSource.baseCoordinate.column := by
              simpa [toStructuredChoice] using
                congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.column
                  source.base_coordinate_eq.symm
            _ = (source.labelSource.coordinate label).column := by
              rfl,
        row_eq := by
          calc
            choice.coordinate.row = source.labelSource.baseCoordinate.row := by
              simpa [toStructuredChoice] using
                congrArg IUTStage1Theorem311LogThetaLatticeCoordinate.row
                  source.base_coordinate_eq.symm
            _ = (source.labelSource.coordinate label).row := by
              rfl,
        coric_eq := rfl,
        procession_eq := rfl,
        procession_column_eq := rfl,
        local_tensor_eq := rfl,
        upper_semi_eq := rfl } }

theorem thetaPilotClass_choiceAt
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    thetaPilotClass (source.choiceAt label) = thetaPilotClass choice :=
  (ind1_thetaPilotClass_eq (source.ind1Step_choiceAt label)).symm

/-- The `|F_l|`/`±`-procession source induced by a choice-level full-label source. -/
def toAbsoluteLabelProcessionSource
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) :
    IUTStage1AbsoluteFLLabelProcessionSource l :=
  IUTStage1AbsoluteFLLabelProcessionSource.ofFullLabelSource source.labelSource

theorem absoluteLabel_choiceAt
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    source.toAbsoluteLabelProcessionSource.absoluteLabel label =
      source.toAbsoluteLabelProcessionSource.absoluteLabelAtCoordinate
        (source.choiceAt label).coordinate :=
  rfl

set_option linter.style.longLine false in
theorem ordinary_to_absolute_choice_procession_compatibility
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice)
    (t label : ZMod l.value) :
    source.toAbsoluteLabelProcessionSource.absoluteLabel
        (zmodLabelTranslate l t label) =
      source.toAbsoluteLabelProcessionSource.absoluteLabelAtCoordinate
        ((source.labelSource.coordinate label).translateFLLabel t) :=
  source.toAbsoluteLabelProcessionSource
    |>.ordinary_to_absolute_procession_compatibility t label

set_option linter.style.longLine false in
/--
Choice-level audit for the Remark 3.11.2 passage from full processions to
`±`-processions.

It says that the choice-level full `F_l` procession induces a no-omission
`|F_l|` label family, that choice representatives carry the induced absolute
label, and that the ordinary procession action is compatible with the
plus-minus procession label map.
-/
structure AbsoluteLabelProcessionChoiceAudit
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) : Prop where
  source_audit :
    IUTStage1AbsoluteFLLabelProcessionSource.AbsoluteLabelProcessionAudit.{u}
      source.toAbsoluteLabelProcessionSource
  all_absolute_labels_present :
    ∀ absLabel : IUTStage1ZModCuspFullLabel l,
      ∃ label : ZMod l.value,
        source.toAbsoluteLabelProcessionSource.absoluteLabel label = absLabel
  choice_absolute_label :
    ∀ label : ZMod l.value,
      source.toAbsoluteLabelProcessionSource.absoluteLabel label =
        source.toAbsoluteLabelProcessionSource.absoluteLabelAtCoordinate
          (source.choiceAt label).coordinate
  ordinary_to_absolute_procession_compatibility :
    ∀ t label : ZMod l.value,
      source.toAbsoluteLabelProcessionSource.absoluteLabel
          (zmodLabelTranslate l t label) =
        source.toAbsoluteLabelProcessionSource.absoluteLabelAtCoordinate
          ((source.labelSource.coordinate label).translateFLLabel t)

theorem absoluteLabelProcessionChoiceAudit
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) :
    AbsoluteLabelProcessionChoiceAudit source :=
  { source_audit :=
      source.toAbsoluteLabelProcessionSource.absoluteLabelProcessionAudit,
    all_absolute_labels_present := by
      intro absLabel
      exact
        source.toAbsoluteLabelProcessionSource.all_absolute_labels_present
          absLabel,
    choice_absolute_label := by
      intro label
      exact source.absoluteLabel_choiceAt label,
    ordinary_to_absolute_procession_compatibility := by
      intro t label
      exact source.ordinary_to_absolute_choice_procession_compatibility t label }

set_option linter.style.longLine false in
/--
Audit for the choice-level full-label procession source.

It combines the source-level no-omission/cardinality facts with the concrete
Theorem 3.11 consequence: every full-label representative lies in the `(Ind1)`
equality side and hence preserves the theta-pilot class.  The normalized
log-volume consequence is added below once `IndeterminacyData` is available.
-/
structure FullLabelProcessionChoiceAudit
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) : Prop where
  source_audit : source.labelSource.FullLabelProcessionAudit
  label_cardinality : Fintype.card (ZMod l.value) = l.value
  all_labels_present :
    ∀ label : ZMod l.value,
      ∃ labelledChoice,
        labelledChoice = source.choiceAt label ∧
          labelledChoice.coordinate.flLabel = label
  all_labels_ind1 :
    ∀ label : ZMod l.value,
      Ind1ProcessionStep choice (source.choiceAt label)
  all_labels_thetaPilotClass_eq :
    ∀ label : ZMod l.value,
      thetaPilotClass (source.choiceAt label) = thetaPilotClass choice

theorem fullLabelProcessionChoiceAudit
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) :
    FullLabelProcessionChoiceAudit source :=
  { source_audit := source.labelSource.fullLabelProcessionAudit,
    label_cardinality := source.labelSource.label_cardinality,
    all_labels_present := by
      intro label
      exact ⟨source.choiceAt label, rfl, rfl⟩,
    all_labels_ind1 := by
      intro label
      exact source.ind1Step_choiceAt label,
    all_labels_thetaPilotClass_eq := by
      intro label
      exact source.thetaPilotClass_choiceAt label }

end FLLabelProcessionChoiceSource

set_option linter.style.longLine false in
/--
Build a concrete `(Ind1)` step from typed procession transport.

This is the source-level finite-procession boundary: the log-theta lattice node
and the non-procession representatives are fixed by explicit equalities, while
the D-prime-strip procession identifier/representative data is supplied by the
typed procession transport.
-/
def Ind1ProcessionStep.ofTypedProcessionTransport
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel)
    (column_eq : choice₁.coordinate.column = choice₂.coordinate.column)
    (row_eq : choice₁.coordinate.row = choice₂.coordinate.row)
    (logThetaColumn_eq :
      choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn)
    (coric_eq : choice₁.coric = choice₂.coric)
    (processionTransport :
      IUTStage1ProcessionState.ProcessionTransport
        choice₁.procession_state choice₂.procession_state)
    (local_tensor_eq :
      choice₁.local_tensor_state = choice₂.local_tensor_state)
    (upper_semi_eq :
      choice₁.upper_semi_state = choice₂.upper_semi_state) :
    Ind1ProcessionStep choice₁ choice₂ :=
  { hodgeTheater_eq := hodgeTheater_eq,
    historyLabel_eq := historyLabel_eq,
    column_eq := column_eq,
    row_eq := row_eq,
    logThetaColumn_eq := logThetaColumn_eq,
    structured_step :=
      { column_eq := column_eq,
        row_eq := row_eq,
        coric_eq := coric_eq,
        procession_eq := processionTransport.procession_eq,
        procession_column_eq := by
          calc
            choice₁.procession_state.column = choice₁.coordinate.column :=
              choice₁.procession_column_eq
            _ = choice₂.coordinate.column := column_eq
            _ = choice₂.procession_state.column :=
              choice₂.procession_column_eq.symm,
        local_tensor_eq := local_tensor_eq,
        upper_semi_eq := upper_semi_eq } }

/--
Concrete `(Ind2)` step induced by the local tensor/direct-summand symmetry.

It keeps the Hodge-theater history and log-theta coordinate fixed and descends to
the existing structured local tensor symmetry step.
-/
structure Ind2LocalTensorStep
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel
  coordinate_eq : choice₁.coordinate = choice₂.coordinate
  structured_step :
    IUTStage1StructuredTheorem311Choice.LocalTensorSymmetryStep
      choice₁.toStructuredChoice choice₂.toStructuredChoice

theorem ind2_thetaPilotClass_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind2LocalTensorStep choice₁ choice₂) :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ := by
  have hcoric : choice₁.coric = choice₂.coric := by
    simpa [toStructuredChoice] using hstep.structured_step.coric_eq
  simp [thetaPilotClass, hstep.hodgeTheater_eq, hstep.historyLabel_eq,
    hstep.coordinate_eq, hcoric]

set_option linter.style.longLine false in
/--
Build a concrete `(Ind2)` step from typed local transports.

The theta-pilot fiber fixes the concrete log-theta coordinate.  The
procession-state equality and upper-semi-state equality are reconstructed from
the typed transports together with the column laws already carried by the two
concrete choices.  The only local tensor datum still required at this level is
equality of the direct-summand counts.
-/
def Ind2LocalTensorStep.ofTypedLocalTransports
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel)
    (coordinate_eq : choice₁.coordinate = choice₂.coordinate)
    (processionTransport :
      IUTStage1ProcessionState.ProcessionTransport
        choice₁.procession_state choice₂.procession_state)
    (direct_summand_count_eq :
      choice₁.local_tensor_state.directSummandCount =
        choice₂.local_tensor_state.directSummandCount)
    (upperSemiTransport :
      IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
        choice₁.upper_semi_state choice₂.upper_semi_state)
    (coric_eq : choice₁.coric = choice₂.coric) :
    Ind2LocalTensorStep choice₁ choice₂ :=
  { hodgeTheater_eq := hodgeTheater_eq,
    historyLabel_eq := historyLabel_eq,
    coordinate_eq := coordinate_eq,
    structured_step :=
      { column_eq := by
          simpa [toStructuredChoice] using congrArg
            IUTStage1Theorem311LogThetaLatticeCoordinate.column coordinate_eq,
        row_eq := by
          simpa [toStructuredChoice] using congrArg
            IUTStage1Theorem311LogThetaLatticeCoordinate.row coordinate_eq,
        coric_eq := coric_eq,
        procession_eq :=
          processionTransport.eq_of_column_eq
            (by
              calc
                choice₁.procession_state.column =
                    choice₁.coordinate.column :=
                  choice₁.procession_column_eq
                _ = choice₂.coordinate.column := by
                  rw [coordinate_eq]
                _ = choice₂.procession_state.column :=
                  choice₂.procession_column_eq.symm),
        direct_summand_count_eq := direct_summand_count_eq,
        upper_semi_eq :=
          upperSemiTransport.eq_of_logThetaColumn_eq
            (by
              calc
                choice₁.upper_semi_state.logThetaColumn =
                    choice₁.coordinate.logThetaColumn :=
                  choice₁.upper_semi_logThetaColumn_eq
                _ = choice₂.coordinate.logThetaColumn := by
                  rw [coordinate_eq]
                _ = choice₂.upper_semi_state.logThetaColumn :=
                  choice₂.upper_semi_logThetaColumn_eq.symm) } }

/--
Concrete `(Ind3)` upper-semi step as the row `m` varies in a fixed column.

The step preserves the Hodge-theater identity, column, coric data, procession,
and local tensor data, but may change the row and upper-semi representative.  It
descends to the structured upper-semi step; the log-volume conclusion remains
one-sided and is supplied by the concrete indeterminacy data below.
-/
structure Ind3UpperSemiStep
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  structured_step :
    IUTStage1StructuredTheorem311Choice.UpperSemiCompatibilityStep
      choice₁.toStructuredChoice choice₂.toStructuredChoice

set_option linter.style.longLine false in
/--
Build a concrete `(Ind3)` step from typed upper-semi transport data.

The source-paper role of `(Ind3)` is still one-sided: this constructor only
builds the step relation.  The log-volume inequality remains the separate
`ind3_upper_semi_logVolume` field of `IndeterminacyData`.
-/
def Ind3UpperSemiStep.ofTypedUpperSemiTransport
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (column_eq : choice₁.coordinate.column = choice₂.coordinate.column)
    (logThetaColumn_eq :
      choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn)
    (coric_eq : choice₁.coric = choice₂.coric)
    (procession_eq : choice₁.procession_state = choice₂.procession_state)
    (local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state)
    (upperSemiTransport :
      IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
        choice₁.upper_semi_state choice₂.upper_semi_state) :
    Ind3UpperSemiStep choice₁ choice₂ :=
  { hodgeTheater_eq := hodgeTheater_eq,
    column_eq := column_eq,
    coric_eq := coric_eq,
    procession_eq := procession_eq,
    local_tensor_eq := local_tensor_eq,
    structured_step :=
      { column_eq := column_eq,
        coric_eq := coric_eq,
        procession_eq := procession_eq,
        local_tensor_eq := local_tensor_eq,
        logThetaColumn_eq := by
          calc
            choice₁.upper_semi_state.logThetaColumn =
                choice₁.coordinate.logThetaColumn :=
              choice₁.upper_semi_logThetaColumn_eq
            _ = choice₂.coordinate.logThetaColumn := logThetaColumn_eq
            _ = choice₂.upper_semi_state.logThetaColumn :=
              choice₂.upper_semi_logThetaColumn_eq.symm,
        nonarchimedean_inclusions_eq :=
          upperSemiTransport.nonarchimedeanInclusions_eq,
        archimedean_surjections_eq :=
          upperSemiTransport.archimedeanSurjections_eq,
        log_volume_compatibility_eq :=
          upperSemiTransport.logVolumeCompatibility_eq,
        has_nonarchimedean_inclusions_eq :=
          upperSemiTransport.hasNonarchimedeanInclusions_eq,
        has_archimedean_surjections_eq :=
          upperSemiTransport.hasArchimedeanSurjections_eq } }

set_option linter.style.longLine false in
/--
Source package for a concrete `(Ind1)` procession transport.

This bundles the Hodge-theater/history/lattice equalities and the typed
procession transport that previously appeared as separate arguments at the
audit boundary.
-/
structure Ind1ProcessionTransportSource
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  row_eq : choice₁.coordinate.row = choice₂.coordinate.row
  logThetaColumn_eq :
    choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn
  coric_eq : choice₁.coric = choice₂.coric
  processionTransport :
    IUTStage1ProcessionState.ProcessionTransport
      choice₁.procession_state choice₂.procession_state
  local_tensor_eq :
    choice₁.local_tensor_state = choice₂.local_tensor_state
  upper_semi_eq :
    choice₁.upper_semi_state = choice₂.upper_semi_state

namespace Ind1ProcessionTransportSource

set_option linter.style.longLine false in
def toStep
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind1ProcessionTransportSource choice₁ choice₂) :
    Ind1ProcessionStep choice₁ choice₂ :=
  Ind1ProcessionStep.ofTypedProcessionTransport
    source.hodgeTheater_eq source.historyLabel_eq source.column_eq
    source.row_eq source.logThetaColumn_eq source.coric_eq
    source.processionTransport source.local_tensor_eq source.upper_semi_eq

theorem thetaPilotClass_eq
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind1ProcessionTransportSource choice₁ choice₂) :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ :=
  ind1_thetaPilotClass_eq source.toStep

set_option linter.style.longLine false in
/--
Audit for the concrete `(Ind1)` procession-transport source.

The source is the paper-side finite-procession equality datum: Hodge-theater
history, row/column/log-theta coordinates, the coric datum, and the non-
procession states are fixed, while the procession representative is transported
by the typed procession transport.  The audit records both the constructed
`(Ind1)` step and the theta-pilot class equality consumed by the quotient
construction.
-/
structure Audit
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind1ProcessionTransportSource choice₁ choice₂) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  row_eq : choice₁.coordinate.row = choice₂.coordinate.row
  logThetaColumn_eq :
    choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn
  coric_eq : choice₁.coric = choice₂.coric
  procession_transport :
    IUTStage1ProcessionState.ProcessionTransport
      choice₁.procession_state choice₂.procession_state
  procession_eq :
    choice₁.procession_state.procession = choice₂.procession_state.procession
  procession_representative_eq :
    choice₁.procession_state.representative =
      choice₂.procession_state.representative
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upper_semi_eq : choice₁.upper_semi_state = choice₂.upper_semi_state
  ind1_procession_step : Ind1ProcessionStep choice₁ choice₂
  thetaPilotClass_eq : thetaPilotClass choice₁ = thetaPilotClass choice₂

set_option linter.style.longLine false in
theorem audit
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind1ProcessionTransportSource choice₁ choice₂) :
    Audit source :=
  { hodgeTheater_eq := source.hodgeTheater_eq,
    historyLabel_eq := source.historyLabel_eq,
    column_eq := source.column_eq,
    row_eq := source.row_eq,
    logThetaColumn_eq := source.logThetaColumn_eq,
    coric_eq := source.coric_eq,
    procession_transport := source.processionTransport,
    procession_eq := source.processionTransport.procession_eq,
    procession_representative_eq := source.processionTransport.representative_eq,
    local_tensor_eq := source.local_tensor_eq,
    upper_semi_eq := source.upper_semi_eq,
    ind1_procession_step := source.toStep,
    thetaPilotClass_eq := source.thetaPilotClass_eq }

end Ind1ProcessionTransportSource

set_option linter.style.longLine false in
/--
Source package for a concrete `(Ind2)` local tensor transport.

The theta-pilot coordinate is fixed, while the procession and upper-semi
representatives are related by their typed transport records.  The direct
summand count equality is the local tensor datum used by the existing typed
`(Ind2)` action.
-/
structure Ind2LocalTensorTransportSource
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel
  coordinate_eq : choice₁.coordinate = choice₂.coordinate
  processionTransport :
    IUTStage1ProcessionState.ProcessionTransport
      choice₁.procession_state choice₂.procession_state
  direct_summand_count_eq :
    choice₁.local_tensor_state.directSummandCount =
      choice₂.local_tensor_state.directSummandCount
  upperSemiTransport :
    IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
      choice₁.upper_semi_state choice₂.upper_semi_state
  coric_eq : choice₁.coric = choice₂.coric

namespace Ind2LocalTensorTransportSource

set_option linter.style.longLine false in
def toStep
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind2LocalTensorTransportSource choice₁ choice₂) :
    Ind2LocalTensorStep choice₁ choice₂ :=
  Ind2LocalTensorStep.ofTypedLocalTransports
    source.hodgeTheater_eq source.historyLabel_eq source.coordinate_eq
    source.processionTransport source.direct_summand_count_eq
    source.upperSemiTransport source.coric_eq

theorem thetaPilotClass_eq
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind2LocalTensorTransportSource choice₁ choice₂) :
    thetaPilotClass choice₁ = thetaPilotClass choice₂ :=
  ind2_thetaPilotClass_eq source.toStep

end Ind2LocalTensorTransportSource

set_option linter.style.longLine false in
/--
Source package for a concrete `(Ind3)` upper-semi transport.

This records the common column/Hodge-theater data and the typed upper-semi
transport.  It constructs only the `(Ind3)` step; the log-volume statement
remains the asymmetric upper-semi inequality supplied by `IndeterminacyData`.
-/
structure Ind3UpperSemiTransportSource
    (choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  logThetaColumn_eq :
    choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upperSemiTransport :
    IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
      choice₁.upper_semi_state choice₂.upper_semi_state

namespace Ind3UpperSemiTransportSource

set_option linter.style.longLine false in
def toStep
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind3UpperSemiTransportSource choice₁ choice₂) :
    Ind3UpperSemiStep choice₁ choice₂ :=
  Ind3UpperSemiStep.ofTypedUpperSemiTransport
    source.hodgeTheater_eq source.column_eq source.logThetaColumn_eq
    source.coric_eq source.procession_eq source.local_tensor_eq
    source.upperSemiTransport

set_option linter.style.longLine false in
/--
Audit for the concrete `(Ind3)` upper-semi transport source.

Unlike the `(Ind1)` and `(Ind2)` source audits, this audit records only a
one-sided source transport.  It exposes the common Hodge-theater/column data,
the fixed procession and local tensor states, the typed upper-semi transport
fields, and the constructed `(Ind3)` step.  Log-volume comparison is supplied by
the typed core through `typedInd3UpperSemiTransportSourceAudit`.
-/
structure Audit
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind3UpperSemiTransportSource choice₁ choice₂) : Prop where
  hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater
  column_eq : choice₁.coordinate.column = choice₂.coordinate.column
  logThetaColumn_eq :
    choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn
  coric_eq : choice₁.coric = choice₂.coric
  procession_eq : choice₁.procession_state = choice₂.procession_state
  local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state
  upperSemiTransport :
    IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
      choice₁.upper_semi_state choice₂.upper_semi_state
  upperSemi_compatibility_eq :
    choice₁.upper_semi_state.compatibility =
      choice₂.upper_semi_state.compatibility
  upperSemi_nonarchimedeanInclusions_eq :
    choice₁.upper_semi_state.nonarchimedeanInclusions =
      choice₂.upper_semi_state.nonarchimedeanInclusions
  upperSemi_archimedeanSurjections_eq :
    choice₁.upper_semi_state.archimedeanSurjections =
      choice₂.upper_semi_state.archimedeanSurjections
  upperSemi_logVolumeCompatibility_eq :
    choice₁.upper_semi_state.logVolumeCompatibility =
      choice₂.upper_semi_state.logVolumeCompatibility
  upperSemi_logVolumeCompatible_eq :
    choice₁.upper_semi_state.logVolumeCompatible =
      choice₂.upper_semi_state.logVolumeCompatible
  ind3_upper_semi_step : Ind3UpperSemiStep choice₁ choice₂

set_option linter.style.longLine false in
theorem audit
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : Ind3UpperSemiTransportSource choice₁ choice₂) :
    Audit source :=
  { hodgeTheater_eq := source.hodgeTheater_eq,
    column_eq := source.column_eq,
    logThetaColumn_eq := source.logThetaColumn_eq,
    coric_eq := source.coric_eq,
    procession_eq := source.procession_eq,
    local_tensor_eq := source.local_tensor_eq,
    upperSemiTransport := source.upperSemiTransport,
    upperSemi_compatibility_eq :=
      source.upperSemiTransport.compatibility_eq,
    upperSemi_nonarchimedeanInclusions_eq :=
      source.upperSemiTransport.nonarchimedeanInclusions_eq,
    upperSemi_archimedeanSurjections_eq :=
      source.upperSemiTransport.archimedeanSurjections_eq,
    upperSemi_logVolumeCompatibility_eq :=
      source.upperSemiTransport.logVolumeCompatibility_eq,
    upperSemi_logVolumeCompatible_eq :=
      source.upperSemiTransport.logVolumeCompatible_eq,
    ind3_upper_semi_step := source.toStep }

end Ind3UpperSemiTransportSource

/--
Concrete Theorem 3.11 indeterminacy data on Hodge-theater/log-theta choices.

The preservation/upper-semi fields are the current mathematical obligations
coming from Theorem 3.11(i),(ii): `(Ind1)` and `(Ind2)` preserve
procession-normalized log-volume; `(Ind3)` gives only the upper-semi
inequality.
-/
structure IndeterminacyData
    (coric : Type u) (l : PrimeGeFive) where
  logVolume : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l -> Real
  ind1_preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂},
      Ind1ProcessionStep choice₁ choice₂ ->
        logVolume choice₁ = logVolume choice₂
  ind2_preserves_processionNormalizedLogVolume :
    ∀ {choice₁ choice₂},
      Ind2LocalTensorStep choice₁ choice₂ ->
        logVolume choice₁ = logVolume choice₂
  ind3_upper_semi_logVolume :
    ∀ {choice₁ choice₂},
      Ind3UpperSemiStep choice₁ choice₂ ->
        logVolume choice₁ <= logVolume choice₂

namespace FLLabelProcessionChoiceSource

theorem logVolume_choiceAt_eq
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (indData : IndeterminacyData coric l)
    (source : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    indData.logVolume (source.choiceAt label) =
      indData.logVolume choice :=
  (indData.ind1_preserves_processionNormalizedLogVolume
    (source.ind1Step_choiceAt label)).symm

set_option linter.style.longLine false in
/--
Log-volume audit for a choice-level full-label procession source.

Once the Theorem 3.11 indeterminacy law is supplied, the pure full-label
procession audit upgrades to the source-paper equality statement: every full
`F_l` representative preserves the procession-normalized log-volume because it
is an `(Ind1)` procession step.
-/
structure FullLabelProcessionChoiceLogVolumeAudit
    (indData : IndeterminacyData coric l)
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) : Prop where
  choice_audit : source.FullLabelProcessionChoiceAudit
  all_labels_logVolume_eq :
    ∀ label : ZMod l.value,
      indData.logVolume (source.choiceAt label) = indData.logVolume choice

theorem fullLabelProcessionChoiceLogVolumeAudit
    (indData : IndeterminacyData coric l)
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source : FLLabelProcessionChoiceSource choice) :
    FullLabelProcessionChoiceLogVolumeAudit indData source :=
  { choice_audit := source.fullLabelProcessionChoiceAudit,
    all_labels_logVolume_eq := by
      intro label
      exact source.logVolume_choiceAt_eq indData label }

end FLLabelProcessionChoiceSource

set_option linter.style.longLine false in
/--
Concrete procession-normalized log-volume source for the Theorem 3.11
Hodge-theater/log-theta choice space.

The source attaches an actual finite `F_l = ZMod l.value` averaged
procession log-volume to each theta-pilot class.  Thus the log-volume of a
concrete choice is obtained only after forgetting the finite label and the
local tensor representative.  Consequently `(Ind1)` and `(Ind2)` preservation
are derived from theta-pilot-class invariance.  The `(Ind3)` contribution is
kept as a one-sided upper-semi average inequality, as in the source theorem.
-/
structure ProcessionNormalizedLogVolumeSource
    (coric : Type u) (l : PrimeGeFive) where
  labelAverage :
    ThetaPilotClass (coric := coric) ->
      IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)
  ind3_upper_semi_average :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind3UpperSemiStep choice₁ choice₂ ->
        (labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (labelAverage (thetaPilotClass choice₂)).averageLogVolume

set_option linter.style.longLine false in
/--
Concrete upper-semi source for the finite procession-normalized log-volume.

This is the Step (x) lowering used by the Theorem 3.11 corridor.  Instead of
supplying the `(Ind3)` average inequality directly, it aligns the source
theta-pilot average with the source log-volume coordinate of the upper-semi
compatibility state and the target theta-pilot average with the target
coordinate.  The one-sided inequality is then exactly
`IUTStage1LogVolumeCompatibilityData.source_le_target`.
-/
structure ProcessionNormalizedUpperSemiComparisonSource
    (coric : Type u) (l : PrimeGeFive) where
  labelAverage :
    ThetaPilotClass (coric := coric) ->
      IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)
  ind3_source_average_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (labelAverage (thetaPilotClass choice₁)).averageLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_average_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (labelAverage (thetaPilotClass choice₂)).averageLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace ProcessionNormalizedUpperSemiComparisonSource

variable
  (source : ProcessionNormalizedUpperSemiComparisonSource coric l)

theorem ind3_upper_semi_average
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
      (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume := by
  calc
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
        choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume :=
      source.ind3_source_average_eq hstep
    _ <= choice₁.upper_semi_state.logVolumeCompatibility.targetLogVolume :=
      choice₁.upper_semi_state.logVolumeCompatibility.source_le_target
    _ = choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
      exact congrArg IUTStage1LogVolumeCompatibilityData.targetLogVolume
        hstep.structured_step.log_volume_compatibility_eq
    _ = (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume :=
      (source.ind3_target_average_eq hstep).symm

/--
Forget the upper-semi comparison source to the finite averaged source consumed
by the typed Theorem 3.11 core.
-/
def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  { labelAverage := source.labelAverage,
    ind3_upper_semi_average := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_average hstep }

set_option linter.style.longLine false in
/--
Audit for deriving the old finite-procession source from upper-semi
compatibility data.
-/
structure Audit : Prop where
  finite_procession_source :
    Nonempty (ProcessionNormalizedLogVolumeSource coric l)
  old_source_labelAverage_eq :
    source.toProcessionNormalizedLogVolumeSource.labelAverage =
      source.labelAverage
  ind3_source_average_alignment :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_average_alignment :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume
  ind3_logVolume_le_from_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume

theorem audit :
    Audit source :=
  { finite_procession_source :=
      ⟨source.toProcessionNormalizedLogVolumeSource⟩,
    old_source_labelAverage_eq := rfl,
    ind3_source_average_alignment := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_average_eq hstep,
    ind3_target_average_alignment := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_average_eq hstep,
    ind3_logVolume_le_from_upperSemi := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_average hstep }

end ProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/--
Label-wise log-theta procession source for the procession-normalized upper-semi
comparison.

This is one level below `ProcessionNormalizedUpperSemiComparisonSource`.  The
source no longer supplies an averaged label object.  Instead, for each
theta-pilot class it supplies the normalized log-volume of every concrete
`F_l = ZMod l.value` label in the full log-theta procession.  Lean constructs
the finite average and uses the two source/target average alignments to recover
the upper-semi comparison source.
-/
structure LogThetaLabelProcessionUpperSemiSource
    (coric : Type u) (l : PrimeGeFive) where
  labelLogVolume :
    ThetaPilotClass (coric := coric) -> ZMod l.value -> Real
  ind3_source_labelAverage_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (Finset.univ.sum fun label : ZMod l.value =>
          labelLogVolume (thetaPilotClass choice₁) label) / (l.value : Real) =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_labelAverage_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (Finset.univ.sum fun label : ZMod l.value =>
          labelLogVolume (thetaPilotClass choice₂) label) / (l.value : Real) =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace LogThetaLabelProcessionUpperSemiSource

variable
  (source : LogThetaLabelProcessionUpperSemiSource coric l)

/-- The full finite label procession attached to a theta-pilot class. -/
def labelProcessionSource
    (_source : LogThetaLabelProcessionUpperSemiSource coric l)
    (thetaClass : ThetaPilotClass (coric := coric)) :
    IUTStage1FLLabelProcessionSource l :=
  thetaClass.flLabelProcessionSource l

set_option linter.style.longLine false in
/-- The averaged procession log-volume constructed from label-wise data. -/
noncomputable def labelAverage
    (thetaClass : ThetaPilotClass (coric := coric)) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume := fun label => source.labelLogVolume thetaClass label,
    averageLogVolume :=
      (Finset.univ.sum fun label : ZMod l.value =>
        source.labelLogVolume thetaClass label) / (l.value : Real),
    average_eq := by
      rw [ZMod.card] }

@[simp]
theorem labelAverage_normalizedLogVolume
    (thetaClass : ThetaPilotClass (coric := coric))
    (label : ZMod l.value) :
    (source.labelAverage thetaClass).normalizedLogVolume label =
      source.labelLogVolume thetaClass label :=
  rfl

set_option linter.style.longLine false in
theorem labelAverage_average_eq_fl_sum
    (thetaClass : ThetaPilotClass (coric := coric)) :
    (source.labelAverage thetaClass).averageLogVolume =
      (Finset.univ.sum fun label : ZMod l.value =>
        source.labelLogVolume thetaClass label) / (l.value : Real) :=
  rfl

set_option linter.style.longLine false in
theorem ind3_source_average_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
      choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume := by
  exact source.ind3_source_labelAverage_eq_upperSemiSource hstep

set_option linter.style.longLine false in
theorem ind3_target_average_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
      choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
  exact source.ind3_target_labelAverage_eq_upperSemiTarget hstep

set_option linter.style.longLine false in
/--
Construct the upper-semi comparison source from label-wise log-theta
procession data.
-/
noncomputable def toProcessionNormalizedUpperSemiComparisonSource :
    ProcessionNormalizedUpperSemiComparisonSource coric l :=
  { labelAverage := source.labelAverage,
    ind3_source_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_average_eq hstep,
    ind3_target_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_average_eq hstep }

set_option linter.style.longLine false in
/-- Forget further to the finite averaged source consumed by older wrappers. -/
noncomputable def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  source.toProcessionNormalizedUpperSemiComparisonSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
theorem ind3_upper_semi_average
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
      (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume :=
  source.toProcessionNormalizedUpperSemiComparisonSource.ind3_upper_semi_average
    hstep

set_option linter.style.longLine false in
/--
Audit for constructing procession-normalized averages from label-wise
log-theta procession data.
-/
structure Audit : Prop where
  zmod_label_cardinality :
    Fintype.card (ZMod l.value) = l.value
  full_label_procession_audit :
    ∀ thetaClass : ThetaPilotClass (coric := coric),
      (source.labelProcessionSource thetaClass).FullLabelProcessionAudit
  label_procession_lattice :
    ∀ thetaClass : ThetaPilotClass (coric := coric),
      (source.labelProcessionSource thetaClass).baseCoordinate.toThetaPilotLatticeCoordinate =
        thetaClass.latticeCoordinate
  labelAverage_constructed :
    ∀ (thetaClass : ThetaPilotClass (coric := coric))
      (label : ZMod l.value),
      (source.labelAverage thetaClass).normalizedLogVolume label =
        source.labelLogVolume thetaClass label
  labelAverage_formula :
    ∀ thetaClass : ThetaPilotClass (coric := coric),
      (source.labelAverage thetaClass).averageLogVolume =
        (Finset.univ.sum fun label : ZMod l.value =>
          source.labelLogVolume thetaClass label) / (l.value : Real)
  upperSemi_source :
    Nonempty (ProcessionNormalizedUpperSemiComparisonSource coric l)
  finite_procession_source :
    Nonempty (ProcessionNormalizedLogVolumeSource coric l)
  ind3_source_average_alignment :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_average_alignment :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume
  ind3_average_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume

set_option linter.style.longLine false in
theorem audit :
    Audit source :=
  { zmod_label_cardinality := ZMod.card l.value,
    full_label_procession_audit := by
      intro thetaClass
      exact thetaClass.flLabelProcessionSource_fullLabelAudit l,
    label_procession_lattice := by
      intro thetaClass
      exact thetaClass.flLabelProcessionSource_latticeCoordinate l,
    labelAverage_constructed := by
      intro thetaClass label
      rfl,
    labelAverage_formula := by
      intro thetaClass
      rfl,
    upperSemi_source :=
      ⟨source.toProcessionNormalizedUpperSemiComparisonSource⟩,
    finite_procession_source :=
      ⟨source.toProcessionNormalizedLogVolumeSource⟩,
    ind3_source_average_alignment := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_average_eq hstep,
    ind3_target_average_alignment := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_average_eq hstep,
    ind3_average_le := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_average hstep }

end LogThetaLabelProcessionUpperSemiSource

set_option linter.style.longLine false in
/--
Nonarchimedean packet alignment source for the upper-semi finite procession
comparison.

This lowers the two average-to-upper-semi alignment fields by inserting the
local tensor packet normalized log-volume.  The source records, for each
concrete Hodge-theater/log-theta choice, the nonarchimedean packet state whose
tensor coordinate is the choice's local tensor state.  The average attached to
the theta-pilot class is identified with the packet normalized log-volume; an
`(Ind3)` step then aligns the source packet with the upper-semi source
coordinate and the target packet with the upper-semi target coordinate.
-/
structure ProcessionNormalizedVerticalLogKummerPacketAlignmentSource
    (coric : Type u) (l : PrimeGeFive) where
  labelAverage :
    ThetaPilotClass (coric := coric) ->
      IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)
  packetState :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l ->
      IUTStage1LocalTensorPacketLogVolumeState
        IUTStage1PlaceKind.nonarchimedean
  packet_tensor_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (packetState choice).tensorState = choice.local_tensor_state
  average_eq_packetNormalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (labelAverage (thetaPilotClass choice)).averageLogVolume =
        (packetState choice).capsuleFamily.normalizedLogVolume
  ind3_source_packet_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₁).capsuleFamily.normalizedLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_packet_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₂).capsuleFamily.normalizedLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace ProcessionNormalizedVerticalLogKummerPacketAlignmentSource

variable
  (source : ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l)

theorem ind3_source_average_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
      choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume := by
  calc
    (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
        (source.packetState choice₁).capsuleFamily.normalizedLogVolume :=
      source.average_eq_packetNormalized choice₁
    _ = choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume :=
      source.ind3_source_packet_eq_upperSemiSource hstep

theorem ind3_target_average_eq
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
      choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
  calc
    (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
        (source.packetState choice₂).capsuleFamily.normalizedLogVolume :=
      source.average_eq_packetNormalized choice₂
    _ = choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume :=
      source.ind3_target_packet_eq_upperSemiTarget hstep

/--
Forget the packet-alignment source to the upper-semi comparison source used by
the typed core.
-/
def toProcessionNormalizedUpperSemiComparisonSource :
    ProcessionNormalizedUpperSemiComparisonSource coric l :=
  { labelAverage := source.labelAverage,
    ind3_source_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_average_eq hstep,
    ind3_target_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_average_eq hstep }

/-- Forget further to the finite averaged source consumed by older wrappers. -/
def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  source.toProcessionNormalizedUpperSemiComparisonSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
/--
Audit for the packet-aligned upper-semi construction.
-/
structure Audit : Prop where
  upperSemi_source :
    Nonempty (ProcessionNormalizedUpperSemiComparisonSource coric l)
  finite_procession_source :
    Nonempty (ProcessionNormalizedLogVolumeSource coric l)
  packet_tensor_alignment :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).tensorState = choice.local_tensor_state
  average_eq_packet_normalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume
  ind3_source_average_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_average_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume
  ind3_average_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume

theorem audit :
    Audit source :=
  { upperSemi_source :=
      ⟨source.toProcessionNormalizedUpperSemiComparisonSource⟩,
    finite_procession_source :=
      ⟨source.toProcessionNormalizedLogVolumeSource⟩,
    packet_tensor_alignment := by
      intro choice
      exact source.packet_tensor_eq choice,
    average_eq_packet_normalized := by
      intro choice
      exact source.average_eq_packetNormalized choice,
    ind3_source_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_average_eq hstep,
    ind3_target_average_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_average_eq hstep,
    ind3_average_le := by
      intro choice₁ choice₂ hstep
      exact
        source.toProcessionNormalizedUpperSemiComparisonSource.ind3_upper_semi_average
          hstep }

end ProcessionNormalizedVerticalLogKummerPacketAlignmentSource

set_option linter.style.longLine false in
/--
Classified packet-local-object source for the vertical log-Kummer upper-semi
comparison.

This is one level below `ProcessionNormalizedVerticalLogKummerPacketAlignmentSource`.
Instead of assuming that the finite procession average is already the packet
normalized log-volume, it identifies the average with the packet local object's
finite log-volume and then uses a classified packet-normalization proof to pass
to the normalized capsule log-volume.  The `(Ind3)` source/target alignments are
also stated at the local-object finite log-volume level.
-/
structure ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource
    (coric : Type u) (l : PrimeGeFive) where
  labelAverage :
    ThetaPilotClass (coric := coric) ->
      IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)
  packetState :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l ->
      IUTStage1LocalTensorPacketLogVolumeState
        IUTStage1PlaceKind.nonarchimedean
  packet_tensor_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (packetState choice).tensorState = choice.local_tensor_state
  packet_normalization :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        (packetState choice)
  average_eq_packetLocalObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (labelAverage (thetaPilotClass choice)).averageLogVolume =
        (packetState choice).localObject.finiteLogVolume
  ind3_source_localObject_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₁).localObject.finiteLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_localObject_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₂).localObject.finiteLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource

variable
  (source :
    ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource
      coric l)

set_option linter.style.longLine false in
theorem average_eq_packetNormalized
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
      (source.packetState choice).capsuleFamily.normalizedLogVolume := by
  calc
    (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).localObject.finiteLogVolume :=
      source.average_eq_packetLocalObject choice
    _ = (source.packetState choice).capsuleFamily.normalizedLogVolume :=
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.localObject_finiteLogVolume_eq_normalizedLogVolume
        (source.packet_normalization choice)

set_option linter.style.longLine false in
theorem ind3_source_packet_eq_upperSemiSource
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.packetState choice₁).capsuleFamily.normalizedLogVolume =
      choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume := by
  calc
    (source.packetState choice₁).capsuleFamily.normalizedLogVolume =
        (source.packetState choice₁).localObject.finiteLogVolume :=
      (IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.localObject_finiteLogVolume_eq_normalizedLogVolume
        (source.packet_normalization choice₁)).symm
    _ = choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume :=
      source.ind3_source_localObject_eq_upperSemiSource hstep

set_option linter.style.longLine false in
theorem ind3_target_packet_eq_upperSemiTarget
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (source.packetState choice₂).capsuleFamily.normalizedLogVolume =
      choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
  calc
    (source.packetState choice₂).capsuleFamily.normalizedLogVolume =
        (source.packetState choice₂).localObject.finiteLogVolume :=
      (IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.localObject_finiteLogVolume_eq_normalizedLogVolume
        (source.packet_normalization choice₂)).symm
    _ = choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume :=
      source.ind3_target_localObject_eq_upperSemiTarget hstep

set_option linter.style.longLine false in
/--
Promote classified packet-local-object data to the packet-aligned source
consumed by the typed Theorem 3.11 core.
-/
def toProcessionNormalizedVerticalLogKummerPacketAlignmentSource :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l :=
  { labelAverage := source.labelAverage,
    packetState := source.packetState,
    packet_tensor_eq := source.packet_tensor_eq,
    average_eq_packetNormalized := by
      intro choice
      exact source.average_eq_packetNormalized choice,
    ind3_source_packet_eq_upperSemiSource := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_packet_eq_upperSemiSource hstep,
    ind3_target_packet_eq_upperSemiTarget := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_packet_eq_upperSemiTarget hstep }

set_option linter.style.longLine false in
/-- Forget to the upper-semi comparison source. -/
noncomputable def toProcessionNormalizedUpperSemiComparisonSource :
    ProcessionNormalizedUpperSemiComparisonSource coric l :=
  source.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource.toProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/-- Forget further to the finite averaged source consumed by older wrappers. -/
def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  source.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
/--
Audit for the classified packet-local-object source.  The main payload is the
replacement of the raw packet-normalized equality by the local-object finite
log-volume equality plus classified packet-normalization compatibility.
-/
structure Audit : Prop where
  packet_alignment_audit :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSource.Audit
      source.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource
  packet_tensor_alignment :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).tensorState = choice.local_tensor_state
  packet_normalization_localObject_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).localObject.finiteLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume
  packet_normalization_capsule_average :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).localObject.finiteLogVolume =
        (source.packetState choice).capsuleFamily.totalLogVolume /
          ((source.packetState choice).capsuleFamily.capsuleCount : Real)
  average_eq_packet_localObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).localObject.finiteLogVolume
  average_eq_packet_normalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume
  ind3_source_localObject_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.packetState choice₁).localObject.finiteLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_localObject_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.packetState choice₂).localObject.finiteLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume
  ind3_average_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (source.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage (thetaPilotClass choice₂)).averageLogVolume

set_option linter.style.longLine false in
theorem audit :
    Audit source :=
  { packet_alignment_audit :=
      source.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource.audit,
    packet_tensor_alignment := by
      intro choice
      exact source.packet_tensor_eq choice,
    packet_normalization_localObject_eq := by
      intro choice
      exact
        IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.localObject_finiteLogVolume_eq_normalizedLogVolume
          (source.packet_normalization choice),
    packet_normalization_capsule_average := by
      intro choice
      exact
        IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.normalizedLogVolume_eq_capsuleAverage
          (source.packet_normalization choice),
    average_eq_packet_localObject := by
      intro choice
      exact source.average_eq_packetLocalObject choice,
    average_eq_packet_normalized := by
      intro choice
      exact source.average_eq_packetNormalized choice,
    ind3_source_localObject_eq_upperSemiSource := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_localObject_eq_upperSemiSource hstep,
    ind3_target_localObject_eq_upperSemiTarget := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_localObject_eq_upperSemiTarget hstep,
    ind3_average_le := by
      intro choice₁ choice₂ hstep
      exact
        source.toProcessionNormalizedUpperSemiComparisonSource.ind3_upper_semi_average
          hstep }

end ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource

set_option linter.style.longLine false in
/--
Label-wise vertical log-Kummer packet-local-object source.

This is one level below
`ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource`.
The source supplies the log-theta procession values label by label and proves
that their finite `F_l` average is the finite log-volume of the classified local
packet object.  Lean then constructs both the label-wise upper-semi source and
the older classified packet-local-object source.
-/
structure LogThetaLabelProcessionVerticalLogKummerClassifiedPacketLocalObjectSource
    (coric : Type u) (l : PrimeGeFive) where
  labelLogVolume :
    ThetaPilotClass (coric := coric) -> ZMod l.value -> Real
  packetState :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l ->
      IUTStage1LocalTensorPacketLogVolumeState
        IUTStage1PlaceKind.nonarchimedean
  packet_tensor_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (packetState choice).tensorState = choice.local_tensor_state
  packet_normalization :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility
        (packetState choice)
  labelAverage_eq_packetLocalObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (Finset.univ.sum fun label : ZMod l.value =>
        labelLogVolume (thetaPilotClass choice) label) / (l.value : Real) =
        (packetState choice).localObject.finiteLogVolume
  ind3_source_localObject_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₁).localObject.finiteLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_localObject_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₂).localObject.finiteLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace LogThetaLabelProcessionVerticalLogKummerClassifiedPacketLocalObjectSource

variable
  (source :
    LogThetaLabelProcessionVerticalLogKummerClassifiedPacketLocalObjectSource
      coric l)

set_option linter.style.longLine false in
theorem ind3_source_labelAverage_eq_upperSemiSource
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (Finset.univ.sum fun label : ZMod l.value =>
      source.labelLogVolume (thetaPilotClass choice₁) label) / (l.value : Real) =
      choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume := by
  calc
    (Finset.univ.sum fun label : ZMod l.value =>
      source.labelLogVolume (thetaPilotClass choice₁) label) / (l.value : Real) =
        (source.packetState choice₁).localObject.finiteLogVolume :=
      source.labelAverage_eq_packetLocalObject choice₁
    _ = choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume :=
      source.ind3_source_localObject_eq_upperSemiSource hstep

set_option linter.style.longLine false in
theorem ind3_target_labelAverage_eq_upperSemiTarget
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    (Finset.univ.sum fun label : ZMod l.value =>
      source.labelLogVolume (thetaPilotClass choice₂) label) / (l.value : Real) =
      choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume := by
  calc
    (Finset.univ.sum fun label : ZMod l.value =>
      source.labelLogVolume (thetaPilotClass choice₂) label) / (l.value : Real) =
        (source.packetState choice₂).localObject.finiteLogVolume :=
      source.labelAverage_eq_packetLocalObject choice₂
    _ = choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume :=
      source.ind3_target_localObject_eq_upperSemiTarget hstep

set_option linter.style.longLine false in
/-- Construct the label-wise upper-semi source from packet-local data. -/
def toLogThetaLabelProcessionUpperSemiSource :
    LogThetaLabelProcessionUpperSemiSource coric l :=
  { labelLogVolume := source.labelLogVolume,
    ind3_source_labelAverage_eq_upperSemiSource := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_labelAverage_eq_upperSemiSource hstep,
    ind3_target_labelAverage_eq_upperSemiTarget := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_labelAverage_eq_upperSemiTarget hstep }

set_option linter.style.longLine false in
/-- Construct the classified packet-local source from label-wise data. -/
noncomputable def toClassifiedPacketLocalObjectSource :
    ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource
      coric l :=
  { labelAverage := source.toLogThetaLabelProcessionUpperSemiSource.labelAverage,
    packetState := source.packetState,
    packet_tensor_eq := source.packet_tensor_eq,
    packet_normalization := source.packet_normalization,
    average_eq_packetLocalObject := by
      intro choice
      exact source.labelAverage_eq_packetLocalObject choice,
    ind3_source_localObject_eq_upperSemiSource := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_localObject_eq_upperSemiSource hstep,
    ind3_target_localObject_eq_upperSemiTarget := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_localObject_eq_upperSemiTarget hstep }

set_option linter.style.longLine false in
/-- Forget to the packet-aligned source consumed by the one-sided constructor. -/
noncomputable def toProcessionNormalizedVerticalLogKummerPacketAlignmentSource :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l :=
  source.toClassifiedPacketLocalObjectSource.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource

set_option linter.style.longLine false in
/-- Forget to the upper-semi comparison source. -/
noncomputable def toProcessionNormalizedUpperSemiComparisonSource :
    ProcessionNormalizedUpperSemiComparisonSource coric l :=
  source.toLogThetaLabelProcessionUpperSemiSource.toProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/-- Forget to the finite averaged source consumed by older wrappers. -/
noncomputable def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  source.toLogThetaLabelProcessionUpperSemiSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
theorem average_eq_packetLocalObject
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (source.toLogThetaLabelProcessionUpperSemiSource.labelAverage
      (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).localObject.finiteLogVolume :=
  source.labelAverage_eq_packetLocalObject choice

set_option linter.style.longLine false in
theorem average_eq_packetNormalized
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    (source.toLogThetaLabelProcessionUpperSemiSource.labelAverage
      (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume :=
  source.toClassifiedPacketLocalObjectSource.average_eq_packetNormalized choice

set_option linter.style.longLine false in
/--
Audit for deriving classified vertical log-Kummer packet-local data from
label-wise log-theta procession values.
-/
structure Audit : Prop where
  labelwise_source_audit :
    LogThetaLabelProcessionUpperSemiSource.Audit
      source.toLogThetaLabelProcessionUpperSemiSource
  classified_packet_source_audit :
    ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource.Audit
      source.toClassifiedPacketLocalObjectSource
  packet_tensor_alignment :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).tensorState = choice.local_tensor_state
  packet_normalization_localObject_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).localObject.finiteLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume
  labelAverage_eq_packet_localObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.toLogThetaLabelProcessionUpperSemiSource.labelAverage
        (thetaPilotClass choice)).averageLogVolume =
          (source.packetState choice).localObject.finiteLogVolume
  labelAverage_eq_packet_normalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.toLogThetaLabelProcessionUpperSemiSource.labelAverage
        (thetaPilotClass choice)).averageLogVolume =
          (source.packetState choice).capsuleFamily.normalizedLogVolume
  ind3_source_labelAverage_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (Finset.univ.sum fun label : ZMod l.value =>
          source.labelLogVolume (thetaPilotClass choice₁) label) /
            (l.value : Real) =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_labelAverage_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (Finset.univ.sum fun label : ZMod l.value =>
          source.labelLogVolume (thetaPilotClass choice₂) label) /
            (l.value : Real) =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

set_option linter.style.longLine false in
theorem audit :
    Audit source :=
  { labelwise_source_audit :=
      source.toLogThetaLabelProcessionUpperSemiSource.audit,
    classified_packet_source_audit :=
      source.toClassifiedPacketLocalObjectSource.audit,
    packet_tensor_alignment := by
      intro choice
      exact source.packet_tensor_eq choice,
    packet_normalization_localObject_eq := by
      intro choice
      exact
        IUTStage1ClassifiedLocalTensorPacketNormalizedCompatibility.localObject_finiteLogVolume_eq_normalizedLogVolume
          (source.packet_normalization choice),
    labelAverage_eq_packet_localObject := by
      intro choice
      exact source.average_eq_packetLocalObject choice,
    labelAverage_eq_packet_normalized := by
      intro choice
      exact source.average_eq_packetNormalized choice,
    ind3_source_labelAverage_eq_upperSemiSource := by
      intro choice₁ choice₂ hstep
      exact source.ind3_source_labelAverage_eq_upperSemiSource hstep,
    ind3_target_labelAverage_eq_upperSemiTarget := by
      intro choice₁ choice₂ hstep
      exact source.ind3_target_labelAverage_eq_upperSemiTarget hstep }

end LogThetaLabelProcessionVerticalLogKummerClassifiedPacketLocalObjectSource

set_option linter.style.longLine false in
/--
Direct packet-local-object source.  This is the concrete finite-capsule-average
variant of the classified source: for each nonarchimedean packet, it supplies the
direct packet-normalization datum whose capsule-sum average identifies the local
object finite log-volume.
-/
structure ProcessionNormalizedVerticalLogKummerDirectPacketLocalObjectSource
    (coric : Type u) (l : PrimeGeFive) where
  labelAverage :
    ThetaPilotClass (coric := coric) ->
      IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)
  packetState :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l ->
      IUTStage1LocalTensorPacketLogVolumeState
        IUTStage1PlaceKind.nonarchimedean
  packet_tensor_eq :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (packetState choice).tensorState = choice.local_tensor_state
  direct_packet_normalization :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      IUTStage1DirectPacketNormalizationData (packetState choice)
  average_eq_packetLocalObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (labelAverage (thetaPilotClass choice)).averageLogVolume =
        (packetState choice).localObject.finiteLogVolume
  ind3_source_localObject_eq_upperSemiSource :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₁).localObject.finiteLogVolume =
          choice₁.upper_semi_state.logVolumeCompatibility.sourceLogVolume
  ind3_target_localObject_eq_upperSemiTarget :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (packetState choice₂).localObject.finiteLogVolume =
          choice₂.upper_semi_state.logVolumeCompatibility.targetLogVolume

namespace ProcessionNormalizedVerticalLogKummerDirectPacketLocalObjectSource

variable
  (source :
    ProcessionNormalizedVerticalLogKummerDirectPacketLocalObjectSource
      coric l)

set_option linter.style.longLine false in
/-- Promote direct finite-capsule packet-normalization data to the classified source. -/
def toClassifiedPacketLocalObjectSource :
    ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource
      coric l :=
  { labelAverage := source.labelAverage,
    packetState := source.packetState,
    packet_tensor_eq := source.packet_tensor_eq,
    packet_normalization := by
      intro choice
      exact
        (source.direct_packet_normalization choice).toClassifiedPacketNormalizedCompatibility,
    average_eq_packetLocalObject := source.average_eq_packetLocalObject,
    ind3_source_localObject_eq_upperSemiSource :=
      source.ind3_source_localObject_eq_upperSemiSource,
    ind3_target_localObject_eq_upperSemiTarget :=
      source.ind3_target_localObject_eq_upperSemiTarget }

set_option linter.style.longLine false in
noncomputable def toProcessionNormalizedVerticalLogKummerPacketAlignmentSource :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l :=
  source.toClassifiedPacketLocalObjectSource.toProcessionNormalizedVerticalLogKummerPacketAlignmentSource

noncomputable def toProcessionNormalizedUpperSemiComparisonSource :
    ProcessionNormalizedUpperSemiComparisonSource coric l :=
  source.toClassifiedPacketLocalObjectSource.toProcessionNormalizedUpperSemiComparisonSource

noncomputable def toProcessionNormalizedLogVolumeSource :
    ProcessionNormalizedLogVolumeSource coric l :=
  source.toClassifiedPacketLocalObjectSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
/-- Audit for the direct finite-capsule packet-local-object source. -/
structure Audit : Prop where
  classified_audit :
    ProcessionNormalizedVerticalLogKummerClassifiedPacketLocalObjectSource.Audit
      source.toClassifiedPacketLocalObjectSource
  capsule_average_localObject :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).localObject.finiteLogVolume =
        (source.packetState choice).capsuleFamily.totalLogVolume /
          ((source.packetState choice).capsuleFamily.capsuleCount : Real)
  average_eq_packet_normalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.labelAverage (thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume

theorem audit :
    Audit source :=
  { classified_audit := source.toClassifiedPacketLocalObjectSource.audit,
    capsule_average_localObject := by
      intro choice
      exact
        (source.direct_packet_normalization choice).localObject_finiteLogVolume_eq_capsuleAverage,
    average_eq_packet_normalized := by
      intro choice
      exact
        source.toClassifiedPacketLocalObjectSource.average_eq_packetNormalized
          choice }

end ProcessionNormalizedVerticalLogKummerDirectPacketLocalObjectSource

namespace ProcessionNormalizedLogVolumeSource

variable
  (source : ProcessionNormalizedLogVolumeSource coric l)

/-- The procession-normalized log-volume of a concrete choice. -/
def logVolume
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    Real :=
  (source.labelAverage (thetaPilotClass choice)).averageLogVolume

theorem logVolume_eq_average
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    source.logVolume choice =
      (source.labelAverage (thetaPilotClass choice)).averageLogVolume :=
  rfl

theorem average_eq_zmod_sum
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    source.logVolume choice =
      (Finset.univ.sum fun label : ZMod l.value =>
        (source.labelAverage (thetaPilotClass choice)).normalizedLogVolume label) /
          Fintype.card (ZMod l.value) := by
  exact (source.labelAverage (thetaPilotClass choice)).average_eq

theorem average_eq_fl_sum
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    source.logVolume choice =
      (Finset.univ.sum fun label : ZMod l.value =>
        (source.labelAverage (thetaPilotClass choice)).normalizedLogVolume label) /
          (l.value : Real) := by
  rw [source.average_eq_zmod_sum choice, ZMod.card]

theorem ind1_preserves_processionNormalizedLogVolume
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind1ProcessionStep choice₁ choice₂) :
    source.logVolume choice₁ = source.logVolume choice₂ := by
  rw [logVolume, logVolume, ind1_thetaPilotClass_eq hstep]

theorem ind2_preserves_processionNormalizedLogVolume
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind2LocalTensorStep choice₁ choice₂) :
    source.logVolume choice₁ = source.logVolume choice₂ := by
  rw [logVolume, logVolume, ind2_thetaPilotClass_eq hstep]

theorem ind3_upper_semi_logVolume
    {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind3UpperSemiStep choice₁ choice₂) :
    source.logVolume choice₁ <= source.logVolume choice₂ :=
  source.ind3_upper_semi_average hstep

/--
Forget the finite-label averaged source to the older indeterminacy record.

This is the main lowering: the equality-side laws of the old record are no
longer source fields, but theorems from the theta-pilot-class quotient.
-/
def toIndeterminacyData :
    IndeterminacyData coric l :=
  { logVolume := source.logVolume,
    ind1_preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact source.ind1_preserves_processionNormalizedLogVolume hstep,
    ind2_preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact source.ind2_preserves_processionNormalizedLogVolume hstep,
    ind3_upper_semi_logVolume := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_logVolume hstep }

theorem flLabel_choiceAt_logVolume_eq
    {choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (labelSource : FLLabelProcessionChoiceSource choice)
    (label : ZMod l.value) :
    source.logVolume (labelSource.choiceAt label) =
      source.logVolume choice :=
  (source.ind1_preserves_processionNormalizedLogVolume
    (labelSource.ind1Step_choiceAt label)).symm

theorem flProcessionTranslate_logVolume_eq
    (t : ZMod l.value)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    source.logVolume (flProcessionTranslate t choice) =
      source.logVolume choice :=
  (source.ind1_preserves_processionNormalizedLogVolume
    (flProcessionTranslate_ind1Step t choice)).symm

set_option linter.style.longLine false in
/--
Audit for the finite-label averaged source.

It records the average formula over `ZMod l`, the cardinality
`|ZMod l| = l`, the derived old indeterminacy record, equality-side invariance,
and the asymmetric `(Ind3)` upper-semi law.
-/
structure Audit : Prop where
  zmod_label_cardinality :
    Fintype.card (ZMod l.value) = l.value
  average_formula :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      source.logVolume choice =
        (Finset.univ.sum fun label : ZMod l.value =>
          (source.labelAverage (thetaPilotClass choice)).normalizedLogVolume label) /
            (l.value : Real)
  old_indeterminacy_data :
    Nonempty (IndeterminacyData coric l)
  ind1_logVolume_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind1ProcessionStep choice₁ choice₂ ->
        source.logVolume choice₁ = source.logVolume choice₂
  ind2_logVolume_eq :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind2LocalTensorStep choice₁ choice₂ ->
        source.logVolume choice₁ = source.logVolume choice₂
  ind3_logVolume_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind3UpperSemiStep choice₁ choice₂ ->
        source.logVolume choice₁ <= source.logVolume choice₂

theorem audit :
    Audit source :=
  { zmod_label_cardinality := ZMod.card l.value,
    average_formula := by
      intro choice
      exact source.average_eq_fl_sum choice,
    old_indeterminacy_data := ⟨source.toIndeterminacyData⟩,
    ind1_logVolume_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_preserves_processionNormalizedLogVolume hstep,
    ind2_logVolume_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_preserves_processionNormalizedLogVolume hstep,
    ind3_logVolume_le := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_logVolume hstep }

end ProcessionNormalizedLogVolumeSource

end IUTStage1ConcreteHodgeTheaterLogThetaChoice

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

set_option linter.style.longLine false in
theorem NonarchimedeanIsmActionEntryStep.toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂)
    (hsymmetry :
      audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
        audited₂.choice.local_tensor_state.packetState.tensorState.symmetry) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState := by
  rcases hstep.matching_action_exists with
    ⟨action, _hplace, _hentry, htargetCapsuleFamily⟩
  exact Or.inl
    ⟨audited₁.choice.local_tensor_state,
      audited₂.choice.local_tensor_state,
      rfl, rfl, hsymmetry, action, htargetCapsuleFamily⟩

set_option linter.style.longLine false in
theorem ArchimedeanOrderTwoActionEntryStep.toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂)
    (hsymmetry :
      audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
        audited₂.choice.local_tensor_state.packetState.tensorState.symmetry) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState := by
  rcases hstep.matching_action_exists with
    ⟨action, _hplace, _hentry, htargetCapsuleFamily⟩
  exact Or.inr
    ⟨audited₁.choice.local_tensor_state,
      audited₂.choice.local_tensor_state,
      rfl, rfl, hsymmetry, action, htargetCapsuleFamily⟩

set_option linter.style.longLine false in
theorem NonarchimedeanIsmActionEntryStep.toDirectSummandActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryStep audited₁ audited₂)
    (hsymmetry :
      audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
        audited₂.choice.local_tensor_state.packetState.tensorState.symmetry) :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  (hstep.toInd2ActionPacketSymmetry hsymmetry).toDirectSummandActionPacketSymmetry

set_option linter.style.longLine false in
theorem ArchimedeanOrderTwoActionEntryStep.toDirectSummandActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂)
    (hsymmetry :
      audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
        audited₂.choice.local_tensor_state.packetState.tensorState.symmetry) :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  (hstep.toInd2ActionPacketSymmetry hsymmetry).toDirectSummandActionPacketSymmetry

set_option linter.style.longLine false in
/--
Nonarchimedean action-entry step with its local tensor symmetry-label source.

The matching `Ism` action and target capsule family are supplied by
`NonarchimedeanIsmActionEntryStep`; this wrapper adds the source-paper
certificate that both local tensor states carry the canonical `Ism` symmetry
label.
-/
structure NonarchimedeanIsmActionEntrySymmetryStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_step : NonarchimedeanIsmActionEntryStep audited₁ audited₂
  source_symmetry :
    IUTStage1LocalTensorState.NonarchimedeanIsmSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
  target_symmetry :
    IUTStage1LocalTensorState.NonarchimedeanIsmSymmetrySource
      audited₂.choice.local_tensor_state.packetState.tensorState

set_option linter.style.longLine false in
/--
Archimedean order-two action-entry step with its local tensor symmetry-label
source.
-/
structure ArchimedeanOrderTwoActionEntrySymmetryStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_step : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂
  source_symmetry :
    IUTStage1LocalTensorState.ArchimedeanOrderTwoSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
  target_symmetry :
    IUTStage1LocalTensorState.ArchimedeanOrderTwoSymmetrySource
      audited₂.choice.local_tensor_state.packetState.tensorState

namespace NonarchimedeanIsmActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem symmetry_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
      audited₂.choice.local_tensor_state.packetState.tensorState.symmetry :=
  hstep.source_symmetry.symmetry_eq_of hstep.target_symmetry

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.action_step.toInd2ActionPacketSymmetry hstep.symmetry_eq

set_option linter.style.longLine false in
theorem toDirectSummandActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toInd2ActionPacketSymmetry.toDirectSummandActionPacketSymmetry

end NonarchimedeanIsmActionEntrySymmetryStep

namespace ArchimedeanOrderTwoActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem symmetry_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.tensorState.symmetry =
      audited₂.choice.local_tensor_state.packetState.tensorState.symmetry :=
  hstep.source_symmetry.symmetry_eq_of hstep.target_symmetry

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.action_step.toInd2ActionPacketSymmetry hstep.symmetry_eq

set_option linter.style.longLine false in
theorem toDirectSummandActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toInd2ActionPacketSymmetry.toDirectSummandActionPacketSymmetry

end ArchimedeanOrderTwoActionEntrySymmetryStep

set_option linter.style.longLine false in
/--
Nonarchimedean action-entry step whose tensor-label certificates are derived
from direct-summand packet label sources.

The source packet's `Ism` kind is read from the typed action entry.  The target
packet still supplies its own `Ism` kind certificate, since the current action
record identifies the target capsule family but not the target summand-family
kind.
-/
structure NonarchimedeanIsmActionEntryPacketLabelStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_step : NonarchimedeanIsmActionEntryStep audited₁ audited₂
  source_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₁.choice.local_tensor_state
  target_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₂.choice.local_tensor_state
  target_symmetry_kind_eq :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm

set_option linter.style.longLine false in
/--
Archimedean action-entry step whose tensor-label certificates are derived from
direct-summand packet label sources.
-/
structure ArchimedeanOrderTwoActionEntryPacketLabelStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_step : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂
  source_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₁.choice.local_tensor_state
  target_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₂.choice.local_tensor_state
  target_symmetry_kind_eq :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo

namespace NonarchimedeanIsmActionEntryPacketLabelStep

set_option linter.style.longLine false in
theorem source_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, _htargetCapsuleFamily⟩
  exact action.symmetryKind_eq

set_option linter.style.longLine false in
theorem source_symmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.NonarchimedeanIsmSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState :=
  hstep.source_label.toNonarchimedeanIsmSymmetrySource
    hstep.source_symmetry_kind_eq

set_option linter.style.longLine false in
theorem target_symmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.NonarchimedeanIsmSymmetrySource
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.target_label.toNonarchimedeanIsmSymmetrySource
    hstep.target_symmetry_kind_eq

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_symmetry := hstep.source_symmetry,
    target_symmetry := hstep.target_symmetry }

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toActionEntrySymmetryStep.toInd2ActionPacketSymmetry

end NonarchimedeanIsmActionEntryPacketLabelStep

namespace ArchimedeanOrderTwoActionEntryPacketLabelStep

set_option linter.style.longLine false in
theorem source_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, _htargetCapsuleFamily⟩
  exact action.symmetryKind_eq

set_option linter.style.longLine false in
theorem source_symmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.ArchimedeanOrderTwoSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState :=
  hstep.source_label.toArchimedeanOrderTwoSymmetrySource
    hstep.source_symmetry_kind_eq

set_option linter.style.longLine false in
theorem target_symmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.ArchimedeanOrderTwoSymmetrySource
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.target_label.toArchimedeanOrderTwoSymmetrySource
    hstep.target_symmetry_kind_eq

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_symmetry := hstep.source_symmetry,
    target_symmetry := hstep.target_symmetry }

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toActionEntrySymmetryStep.toInd2ActionPacketSymmetry

end ArchimedeanOrderTwoActionEntryPacketLabelStep

set_option linter.style.longLine false in
/--
Nonarchimedean action-entry step whose target `Ism` kind is obtained by
transporting the source packet's direct-summand symmetry kind.
-/
structure NonarchimedeanIsmActionEntryTransportedPacketLabelStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_step : NonarchimedeanIsmActionEntryStep audited₁ audited₂
  source_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₁.choice.local_tensor_state
  target_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₂.choice.local_tensor_state
  target_kind_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryKindTransport
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

set_option linter.style.longLine false in
/--
Archimedean action-entry step whose target order-two kind is obtained by
transporting the source packet's direct-summand symmetry kind.
-/
structure ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_step : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂
  source_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₁.choice.local_tensor_state
  target_label :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelSource
      audited₂.choice.local_tensor_state
  target_kind_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryKindTransport
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

namespace NonarchimedeanIsmActionEntryTransportedPacketLabelStep

set_option linter.style.longLine false in
theorem source_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, _htargetCapsuleFamily⟩
  exact action.symmetryKind_eq

set_option linter.style.longLine false in
theorem target_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm :=
  hstep.target_kind_transport.target_symmetryKind_eq
    hstep.source_symmetry_kind_eq

set_option linter.style.longLine false in
def toPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_label := hstep.source_label,
    target_label := hstep.target_label,
    target_symmetry_kind_eq := hstep.target_symmetry_kind_eq }

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂ :=
  hstep.toPacketLabelStep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toPacketLabelStep.toInd2ActionPacketSymmetry

end NonarchimedeanIsmActionEntryTransportedPacketLabelStep

namespace ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep

set_option linter.style.longLine false in
theorem source_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, _htargetCapsuleFamily⟩
  exact action.symmetryKind_eq

set_option linter.style.longLine false in
theorem target_symmetry_kind_eq
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo :=
  hstep.target_kind_transport.target_symmetryKind_eq
    hstep.source_symmetry_kind_eq

set_option linter.style.longLine false in
def toPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_label := hstep.source_label,
    target_label := hstep.target_label,
    target_symmetry_kind_eq := hstep.target_symmetry_kind_eq }

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂ :=
  hstep.toPacketLabelStep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toPacketLabelStep.toInd2ActionPacketSymmetry

end ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep

set_option linter.style.longLine false in
/--
Nonarchimedean action-entry step whose source and target packet labels and
target symmetry-kind transport are all derived from one label-transport source.
-/
structure NonarchimedeanIsmActionEntryLabelTransportStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_step : NonarchimedeanIsmActionEntryStep audited₁ audited₂
  label_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

set_option linter.style.longLine false in
/--
Archimedean action-entry step whose source and target packet labels and target
symmetry-kind transport are all derived from one label-transport source.
-/
structure ArchimedeanOrderTwoActionEntryLabelTransportStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_step : ArchimedeanOrderTwoActionEntryStep audited₁ audited₂
  label_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

namespace NonarchimedeanIsmActionEntryLabelTransportStep

set_option linter.style.longLine false in
def toTransportedPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_label := hstep.label_transport.sourceLabelSource,
    target_label := hstep.label_transport.targetLabelSource,
    target_kind_transport := hstep.label_transport.symmetryKindTransport }

set_option linter.style.longLine false in
def toPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂ :=
  hstep.toTransportedPacketLabelStep.toPacketLabelStep

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂ :=
  hstep.toTransportedPacketLabelStep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toTransportedPacketLabelStep.toInd2ActionPacketSymmetry

set_option linter.style.longLine false in
theorem nonemptyInd2ActionPacketSymmetrySource
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    Nonempty
      (IUTStage1LocalTensorState.NonarchimedeanInd2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState) := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, htargetCapsuleFamily⟩
  exact ⟨
    { sourcePacket := audited₁.choice.local_tensor_state,
      targetPacket := audited₂.choice.local_tensor_state,
      source_tensor_eq := rfl,
      target_tensor_eq := rfl,
      label_transport := hstep.label_transport,
      action := action,
      target_capsule_eq := htargetCapsuleFamily }⟩

set_option linter.style.longLine false in
theorem nonemptyInd2ActionPacketSymmetrySourceSum
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    Nonempty
      (IUTStage1LocalTensorState.Ind2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState) := by
  rcases hstep.nonemptyInd2ActionPacketSymmetrySource with ⟨source⟩
  exact ⟨Sum.inl source⟩

set_option linter.style.longLine false in
/--
Audit package for the source-derived nonarchimedean `(Ind2)` label transport.

A single `SymmetryLabelTransportSource` now supplies the transported packet
labels, the target symmetry-kind equality, the action-entry symmetry, the typed
`(Ind2)` packet symmetry, and the resulting direct-summand-count equality.
-/
structure Ind2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) where
  label_transport_audit :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource.TransportAudit
      hstep.label_transport
  transported_step :
    NonarchimedeanIsmActionEntryTransportedPacketLabelStep audited₁ audited₂
  packet_label_step :
    NonarchimedeanIsmActionEntryPacketLabelStep audited₁ audited₂
  action_entry_symmetry_step :
    NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂
  source_symmetry_kind_eq :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm
  target_symmetry_kind_eq :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.nonarchimedeanIsm
  ind2_action_packet_symmetry :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_action_packet_symmetry :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_packet_symmetry :
    IUTStage1LocalTensorState.DirectSummandPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_symmetry :
    IUTStage1LocalTensorState.DirectSummandSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_count_eq :
    audited₁.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited₂.choice.local_tensor_state.packetState.tensorState.directSummandCount

set_option linter.style.longLine false in
def ind2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    Ind2ActionPacketAudit hstep := by
  let ind2Symmetry := hstep.toInd2ActionPacketSymmetry
  let directActionSymmetry :=
    ind2Symmetry.toDirectSummandActionPacketSymmetry
  let directPacketSymmetry :=
    ind2Symmetry.toDirectSummandPacketSymmetry
  let directSymmetry :=
    ind2Symmetry.toDirectSummandSymmetry
  exact
    { label_transport_audit := hstep.label_transport.transportAudit,
      transported_step := hstep.toTransportedPacketLabelStep,
      packet_label_step := hstep.toPacketLabelStep,
      action_entry_symmetry_step := hstep.toActionEntrySymmetryStep,
      source_symmetry_kind_eq :=
        hstep.toTransportedPacketLabelStep.source_symmetry_kind_eq,
      target_symmetry_kind_eq :=
        hstep.toTransportedPacketLabelStep.target_symmetry_kind_eq,
      ind2_action_packet_symmetry := ind2Symmetry,
      direct_summand_action_packet_symmetry := directActionSymmetry,
      direct_summand_packet_symmetry := directPacketSymmetry,
      direct_summand_symmetry := directSymmetry,
      direct_summand_count_eq := directSymmetry.directSummandCount_eq }

set_option linter.style.longLine false in
/--
Audit package retaining the source-level nonarchimedean `(Ind2)` packet/action
object produced by a label-transport step.
-/
structure SourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    Prop where
  source_level_ind2_action_packet_nonempty :
    Nonempty
      (IUTStage1LocalTensorState.NonarchimedeanInd2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState)
  projected_ind2_action_packet_symmetry :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  projected_direct_summand_count_eq :
    audited₁.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited₂.choice.local_tensor_state.packetState.tensorState.directSummandCount

set_option linter.style.longLine false in
def sourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂) :
    SourceInd2ActionPacketAudit hstep :=
  let projectedAudit := hstep.ind2ActionPacketAudit
  { source_level_ind2_action_packet_nonempty :=
      hstep.nonemptyInd2ActionPacketSymmetrySource,
    projected_ind2_action_packet_symmetry :=
      projectedAudit.ind2_action_packet_symmetry,
    projected_direct_summand_count_eq :=
      projectedAudit.direct_summand_count_eq }

end NonarchimedeanIsmActionEntryLabelTransportStep

namespace ArchimedeanOrderTwoActionEntryLabelTransportStep

set_option linter.style.longLine false in
def toTransportedPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂ :=
  { action_step := hstep.action_step,
    source_label := hstep.label_transport.sourceLabelSource,
    target_label := hstep.label_transport.targetLabelSource,
    target_kind_transport := hstep.label_transport.symmetryKindTransport }

set_option linter.style.longLine false in
def toPacketLabelStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂ :=
  hstep.toTransportedPacketLabelStep.toPacketLabelStep

set_option linter.style.longLine false in
def toActionEntrySymmetryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂ :=
  hstep.toTransportedPacketLabelStep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem toInd2ActionPacketSymmetry
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  hstep.toTransportedPacketLabelStep.toInd2ActionPacketSymmetry

set_option linter.style.longLine false in
theorem nonemptyInd2ActionPacketSymmetrySource
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    Nonempty
      (IUTStage1LocalTensorState.ArchimedeanInd2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState) := by
  rcases hstep.action_step.matching_action_exists with
    ⟨action, _hplace, _hentry, htargetCapsuleFamily⟩
  exact ⟨
    { sourcePacket := audited₁.choice.local_tensor_state,
      targetPacket := audited₂.choice.local_tensor_state,
      source_tensor_eq := rfl,
      target_tensor_eq := rfl,
      label_transport := hstep.label_transport,
      action := action,
      target_capsule_eq := htargetCapsuleFamily }⟩

set_option linter.style.longLine false in
theorem nonemptyInd2ActionPacketSymmetrySourceSum
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    Nonempty
      (IUTStage1LocalTensorState.Ind2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState) := by
  rcases hstep.nonemptyInd2ActionPacketSymmetrySource with ⟨source⟩
  exact ⟨Sum.inr source⟩

set_option linter.style.longLine false in
/--
Audit package for the source-derived archimedean `(Ind2)` label transport.

A single `SymmetryLabelTransportSource` now supplies the transported packet
labels, the target symmetry-kind equality, the action-entry symmetry, the typed
`(Ind2)` packet symmetry, and the resulting direct-summand-count equality.
-/
structure Ind2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) where
  label_transport_audit :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource.TransportAudit
      hstep.label_transport
  transported_step :
    ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep audited₁ audited₂
  packet_label_step :
    ArchimedeanOrderTwoActionEntryPacketLabelStep audited₁ audited₂
  action_entry_symmetry_step :
    ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂
  source_symmetry_kind_eq :
    audited₁.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo
  target_symmetry_kind_eq :
    audited₂.choice.local_tensor_state.summandFamily.symmetryKind =
      IUTStage1TensorSummandSymmetryKind.archimedeanOrderTwo
  ind2_action_packet_symmetry :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_action_packet_symmetry :
    IUTStage1LocalTensorState.DirectSummandActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_packet_symmetry :
    IUTStage1LocalTensorState.DirectSummandPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_symmetry :
    IUTStage1LocalTensorState.DirectSummandSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  direct_summand_count_eq :
    audited₁.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited₂.choice.local_tensor_state.packetState.tensorState.directSummandCount

set_option linter.style.longLine false in
def ind2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    Ind2ActionPacketAudit hstep := by
  let ind2Symmetry := hstep.toInd2ActionPacketSymmetry
  let directActionSymmetry :=
    ind2Symmetry.toDirectSummandActionPacketSymmetry
  let directPacketSymmetry :=
    ind2Symmetry.toDirectSummandPacketSymmetry
  let directSymmetry :=
    ind2Symmetry.toDirectSummandSymmetry
  exact
    { label_transport_audit := hstep.label_transport.transportAudit,
      transported_step := hstep.toTransportedPacketLabelStep,
      packet_label_step := hstep.toPacketLabelStep,
      action_entry_symmetry_step := hstep.toActionEntrySymmetryStep,
      source_symmetry_kind_eq :=
        hstep.toTransportedPacketLabelStep.source_symmetry_kind_eq,
      target_symmetry_kind_eq :=
        hstep.toTransportedPacketLabelStep.target_symmetry_kind_eq,
      ind2_action_packet_symmetry := ind2Symmetry,
      direct_summand_action_packet_symmetry := directActionSymmetry,
      direct_summand_packet_symmetry := directPacketSymmetry,
      direct_summand_symmetry := directSymmetry,
      direct_summand_count_eq := directSymmetry.directSummandCount_eq }

set_option linter.style.longLine false in
/--
Audit package retaining the source-level archimedean `(Ind2)` packet/action
object produced by a label-transport step.
-/
structure SourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    Prop where
  source_level_ind2_action_packet_nonempty :
    Nonempty
      (IUTStage1LocalTensorState.ArchimedeanInd2ActionPacketSymmetrySource
        audited₁.choice.local_tensor_state.packetState.tensorState
        audited₂.choice.local_tensor_state.packetState.tensorState)
  projected_ind2_action_packet_symmetry :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetry
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  projected_direct_summand_count_eq :
    audited₁.choice.local_tensor_state.packetState.tensorState.directSummandCount =
      audited₂.choice.local_tensor_state.packetState.tensorState.directSummandCount

set_option linter.style.longLine false in
def sourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂) :
    SourceInd2ActionPacketAudit hstep :=
  let projectedAudit := hstep.ind2ActionPacketAudit
  { source_level_ind2_action_packet_nonempty :=
      hstep.nonemptyInd2ActionPacketSymmetrySource,
    projected_ind2_action_packet_symmetry :=
      projectedAudit.ind2_action_packet_symmetry,
    projected_direct_summand_count_eq :=
      projectedAudit.direct_summand_count_eq }

end ArchimedeanOrderTwoActionEntryLabelTransportStep

set_option linter.style.longLine false in
/--
Nonarchimedean action-entry step with the matching `Ism` action retained as
data.

This is lower than `NonarchimedeanIsmActionEntryStep`: the latter stores the
matching action behind a propositional existential, which is enough for projected
proofs but not enough to construct source-level packet/action data.  This source
step keeps the action itself and derives the older step by forgetting it.
-/
structure NonarchimedeanIsmActionEntrySourceStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_entry : IUTStage1NonarchimedeanIsmActionEntry
  action_entry_mem :
    action_entry ∈
      audited₁.placeFamilyCompatibility.ind2Actions.nonarchimedeanActions
  source_step : NonarchimedeanIsmInd2Step audited₁ audited₂
  matching_action :
    IUTStage1NonarchimedeanIsmDirectSummandAction
      audited₁.choice.local_tensor_state.summandFamily
  matching_action_place : matching_action.place = action_entry.place
  matching_action_transformedFamily_eq_entry :
    matching_action.toDirectSummandAction.toCapsuleAction.transformedFamily =
      action_entry.toDirectSummandAction.toCapsuleAction.transformedFamily
  target_capsule_eq :
    audited₂.choice.local_tensor_state.packetState.capsuleFamily =
      matching_action.toDirectSummandAction.toCapsuleAction.transformedFamily

namespace NonarchimedeanIsmActionEntrySourceStep

set_option linter.style.longLine false in
def toActionEntryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntrySourceStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryStep audited₁ audited₂ :=
  { action_entry := source.action_entry,
    action_entry_mem := source.action_entry_mem,
    source_step := source.source_step,
    matching_action_exists :=
      ⟨source.matching_action, source.matching_action_place,
        source.matching_action_transformedFamily_eq_entry,
        source.target_capsule_eq⟩ }

end NonarchimedeanIsmActionEntrySourceStep

set_option linter.style.longLine false in
/--
Archimedean action-entry step with the matching order-two action retained as
data.
-/
structure ArchimedeanOrderTwoActionEntrySourceStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_entry : IUTStage1ArchimedeanOrderTwoActionEntry
  action_entry_mem :
    action_entry ∈
      audited₁.placeFamilyCompatibility.ind2Actions.archimedeanActions
  source_step : ArchimedeanOrderTwoInd2Step audited₁ audited₂
  matching_action :
    IUTStage1ArchimedeanOrderTwoDirectSummandAction
      audited₁.choice.local_tensor_state.summandFamily
  matching_action_place : matching_action.place = action_entry.place
  matching_action_transformedFamily_eq_entry :
    matching_action.toDirectSummandAction.toCapsuleAction.transformedFamily =
      action_entry.toDirectSummandAction.toCapsuleAction.transformedFamily
  target_capsule_eq :
    audited₂.choice.local_tensor_state.packetState.capsuleFamily =
      matching_action.toDirectSummandAction.toCapsuleAction.transformedFamily

namespace ArchimedeanOrderTwoActionEntrySourceStep

set_option linter.style.longLine false in
def toActionEntryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntrySourceStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryStep audited₁ audited₂ :=
  { action_entry := source.action_entry,
    action_entry_mem := source.action_entry_mem,
    source_step := source.source_step,
    matching_action_exists :=
      ⟨source.matching_action, source.matching_action_place,
        source.matching_action_transformedFamily_eq_entry,
        source.target_capsule_eq⟩ }

end ArchimedeanOrderTwoActionEntrySourceStep

set_option linter.style.longLine false in
/--
Nonarchimedean label-transport step with the matching action retained as data.
-/
structure NonarchimedeanIsmActionEntryLabelTransportSourceStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean) where
  action_source_step :
    NonarchimedeanIsmActionEntrySourceStep audited₁ audited₂
  label_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

namespace NonarchimedeanIsmActionEntryLabelTransportSourceStep

set_option linter.style.longLine false in
def toLabelTransportStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntryLabelTransportSourceStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryLabelTransportStep audited₁ audited₂ :=
  { action_step := source.action_source_step.toActionEntryStep,
    label_transport := source.label_transport }

set_option linter.style.longLine false in
def toInd2ActionPacketSymmetrySource
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntryLabelTransportSourceStep audited₁ audited₂) :
    IUTStage1LocalTensorState.NonarchimedeanInd2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  { sourcePacket := audited₁.choice.local_tensor_state,
    targetPacket := audited₂.choice.local_tensor_state,
    source_tensor_eq := rfl,
    target_tensor_eq := rfl,
    label_transport := source.label_transport,
    action := source.action_source_step.matching_action,
    target_capsule_eq := source.action_source_step.target_capsule_eq }

set_option linter.style.longLine false in
def toInd2ActionPacketSymmetrySourceSum
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntryLabelTransportSourceStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  Sum.inl source.toInd2ActionPacketSymmetrySource

set_option linter.style.longLine false in
structure SourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntryLabelTransportSourceStep audited₁ audited₂) where
  source_level_ind2_action_packet :
    IUTStage1LocalTensorState.NonarchimedeanInd2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  source_level_audit :
    IUTStage1LocalTensorState.NonarchimedeanInd2ActionPacketSymmetrySource.Audit
      source_level_ind2_action_packet
  projected_label_transport_audit :
    source.toLabelTransportStep.SourceInd2ActionPacketAudit

set_option linter.style.longLine false in
def sourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (source :
      NonarchimedeanIsmActionEntryLabelTransportSourceStep audited₁ audited₂) :
    SourceInd2ActionPacketAudit source :=
  let sourceLevel := source.toInd2ActionPacketSymmetrySource
  { source_level_ind2_action_packet := sourceLevel,
    source_level_audit := sourceLevel.audit,
    projected_label_transport_audit :=
      source.toLabelTransportStep.sourceInd2ActionPacketAudit }

end NonarchimedeanIsmActionEntryLabelTransportSourceStep

set_option linter.style.longLine false in
/--
Archimedean label-transport step with the matching action retained as data.
-/
structure ArchimedeanOrderTwoActionEntryLabelTransportSourceStep
    (audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean) where
  action_source_step :
    ArchimedeanOrderTwoActionEntrySourceStep audited₁ audited₂
  label_transport :
    IUTStage1LocalTensorDirectSummandPacketState.SymmetryLabelTransportSource
      audited₁.choice.local_tensor_state
      audited₂.choice.local_tensor_state

namespace ArchimedeanOrderTwoActionEntryLabelTransportSourceStep

set_option linter.style.longLine false in
def toLabelTransportStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntryLabelTransportSourceStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryLabelTransportStep audited₁ audited₂ :=
  { action_step := source.action_source_step.toActionEntryStep,
    label_transport := source.label_transport }

set_option linter.style.longLine false in
def toInd2ActionPacketSymmetrySource
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntryLabelTransportSourceStep audited₁ audited₂) :
    IUTStage1LocalTensorState.ArchimedeanInd2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  { sourcePacket := audited₁.choice.local_tensor_state,
    targetPacket := audited₂.choice.local_tensor_state,
    source_tensor_eq := rfl,
    target_tensor_eq := rfl,
    label_transport := source.label_transport,
    action := source.action_source_step.matching_action,
    target_capsule_eq := source.action_source_step.target_capsule_eq }

set_option linter.style.longLine false in
def toInd2ActionPacketSymmetrySourceSum
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntryLabelTransportSourceStep audited₁ audited₂) :
    IUTStage1LocalTensorState.Ind2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState :=
  Sum.inr source.toInd2ActionPacketSymmetrySource

set_option linter.style.longLine false in
structure SourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntryLabelTransportSourceStep audited₁ audited₂) where
  source_level_ind2_action_packet :
    IUTStage1LocalTensorState.ArchimedeanInd2ActionPacketSymmetrySource
      audited₁.choice.local_tensor_state.packetState.tensorState
      audited₂.choice.local_tensor_state.packetState.tensorState
  source_level_audit :
    IUTStage1LocalTensorState.ArchimedeanInd2ActionPacketSymmetrySource.Audit
      source_level_ind2_action_packet
  projected_label_transport_audit :
    source.toLabelTransportStep.SourceInd2ActionPacketAudit

set_option linter.style.longLine false in
def sourceInd2ActionPacketAudit
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (source :
      ArchimedeanOrderTwoActionEntryLabelTransportSourceStep audited₁ audited₂) :
    SourceInd2ActionPacketAudit source :=
  let sourceLevel := source.toInd2ActionPacketSymmetrySource
  { source_level_ind2_action_packet := sourceLevel,
    source_level_audit := sourceLevel.audit,
    projected_label_transport_audit :=
      source.toLabelTransportStep.sourceInd2ActionPacketAudit }

end ArchimedeanOrderTwoActionEntryLabelTransportSourceStep

def nonarchimedeanEntrySymmetry_toNonarchimedeanEntryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    NonarchimedeanIsmActionEntryStep audited₁ audited₂ :=
  hstep.action_step

def archimedeanEntrySymmetry_toArchimedeanEntryStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    ArchimedeanOrderTwoActionEntryStep audited₁ audited₂ :=
  hstep.action_step

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

def nonarchimedeanEntrySymmetry_toNonarchimedeanIsmStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    NonarchimedeanIsmInd2Step audited₁ audited₂ :=
  nonarchimedeanEntry_toNonarchimedeanIsmStep hstep.action_step

def archimedeanEntrySymmetry_toArchimedeanOrderTwoStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    ArchimedeanOrderTwoInd2Step audited₁ audited₂ :=
  archimedeanEntry_toArchimedeanOrderTwoStep hstep.action_step

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

def nonarchimedeanEntrySymmetry_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  nonarchimedeanEntry_toDirectSummandActionStep hstep.action_step

def archimedeanEntrySymmetry_toDirectSummandActionStep
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    LocalTensorDirectSummandActionStep audited₁ audited₂ :=
  archimedeanEntry_toDirectSummandActionStep hstep.action_step

theorem nonarchimedeanEntrySymmetry_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep : NonarchimedeanIsmActionEntrySymmetryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (nonarchimedeanEntrySymmetry_toDirectSummandActionStep hstep)

theorem archimedeanEntrySymmetry_preserves_capsuleTotalLogVolume
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep : ArchimedeanOrderTwoActionEntrySymmetryStep audited₁ audited₂) :
    audited₁.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume =
      audited₂.choice.local_tensor_state.packetState.capsuleFamily.totalLogVolume :=
  ind2_preserves_capsuleTotalLogVolume
    (archimedeanEntrySymmetry_toDirectSummandActionStep hstep)

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

theorem region_eq_of_nonarchimedeanEntrySymmetry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_nonarchimedeanEntry_step hstep.action_step

theorem region_eq_of_nonarchimedeanEntryPacketLabel_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_nonarchimedeanEntrySymmetry_step
    hstep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_nonarchimedeanEntryPacketLabel_step
    hstep.toPacketLabelStep

set_option linter.style.longLine false in
theorem region_eq_of_nonarchimedeanEntryLabelTransport_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.nonarchimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step
    hstep.toTransportedPacketLabelStep

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

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntrySymmetry_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntrySymmetry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryTransportedPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryLabelTransport_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryLabelTransport_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
/--
Possible-image quotient audit for a source-labelled nonarchimedean `(Ind2)`
transport.

This packages the exact point needed in Theorem 3.11: the source label transport
enters the equality quotient through the typed `(Ind2)` direct-summand action,
hence the two theta-pilot possible-image regions agree, while the acting place
is still certified to lie in the relevant nonarchimedean fiber.
-/
structure NonarchimedeanEntryLabelTransportPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) where
  ind2_packet_audit :
    IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep.Ind2ActionPacketAudit
      hstep
  equality_quotient_relation :
    data.quotient.relation audited₁ audited₂
  region_eq :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂
  fiber_mem :
    hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places

set_option linter.style.longLine false in
def nonarchimedeanEntryLabelTransportPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    NonarchimedeanEntryLabelTransportPossibleImageAudit
      data fiberPackage hstep :=
  { ind2_packet_audit := hstep.ind2ActionPacketAudit,
    equality_quotient_relation := by
      rw [data.quotient_eq_generated]
      exact IUTStage1GeneratedIndeterminacyRelation.ind2
        (IUTStage1PlaceAuditedDirectSummandPacketChoice.nonarchimedeanEntry_toDirectSummandActionStep
          hstep.action_step),
    region_eq := data.region_eq_of_nonarchimedeanEntryLabelTransport_step hstep,
    fiber_mem := fiberPackage.entry_place_mem_fiber hstep.action_step }

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

theorem region_eq_of_archimedeanEntrySymmetry_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_archimedeanEntry_step hstep.action_step

theorem region_eq_of_archimedeanEntryPacketLabel_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_archimedeanEntrySymmetry_step
    hstep.toActionEntrySymmetryStep

set_option linter.style.longLine false in
theorem region_eq_of_archimedeanEntryTransportedPacketLabel_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_archimedeanEntryPacketLabel_step
    hstep.toPacketLabelStep

set_option linter.style.longLine false in
theorem region_eq_of_archimedeanEntryLabelTransport_step
    (data :
      IUTStage1PlaceAuditedMultiradialImages
        (target := target) coric IUTStage1PlaceKind.archimedean)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ :=
  data.region_eq_of_archimedeanEntryTransportedPacketLabel_step
    hstep.toTransportedPacketLabelStep

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

theorem region_eq_and_fiber_mem_of_archimedeanEntrySymmetry_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntrySymmetry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

theorem region_eq_and_fiber_mem_of_archimedeanEntryPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_archimedeanEntryTransportedPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryTransportedPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_archimedeanEntryLabelTransport_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryLabelTransport_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
/--
Possible-image quotient audit for a source-labelled archimedean `(Ind2)`
transport.

This is the archimedean order-two analogue of the nonarchimedean audit: the
label transport is converted to the equality-quotient `(Ind2)` generator, hence
possible-image regions agree, and the acting place remains in the relevant
archimedean fiber.
-/
structure ArchimedeanEntryLabelTransportPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) where
  ind2_packet_audit :
    IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep.Ind2ActionPacketAudit
      hstep
  equality_quotient_relation :
    data.quotient.relation audited₁ audited₂
  region_eq :
    data.possibleImages.region audited₁ = data.possibleImages.region audited₂
  fiber_mem :
    hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places

set_option linter.style.longLine false in
def archimedeanEntryLabelTransportPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    ArchimedeanEntryLabelTransportPossibleImageAudit
      data fiberPackage hstep :=
  { ind2_packet_audit := hstep.ind2ActionPacketAudit,
    equality_quotient_relation := by
      rw [data.quotient_eq_generated]
      exact IUTStage1GeneratedIndeterminacyRelation.ind2
        (IUTStage1PlaceAuditedDirectSummandPacketChoice.archimedeanEntry_toDirectSummandActionStep
          hstep.action_step),
    region_eq := data.region_eq_of_archimedeanEntryLabelTransport_step hstep,
    fiber_mem := fiberPackage.entry_place_mem_fiber hstep.action_step }

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

theorem region_eq_of_nonarchimedeanEntrySymmetry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_nonarchimedeanEntrySymmetry_step hstep

theorem region_eq_of_nonarchimedeanEntryPacketLabel_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_nonarchimedeanEntryPacketLabel_step hstep

set_option linter.style.longLine false in
theorem region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact
    data.auditedImages.region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step
      hstep

set_option linter.style.longLine false in
theorem region_eq_of_nonarchimedeanEntryLabelTransport_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.nonarchimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.nonarchimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ :=
  data.region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step
    hstep.toTransportedPacketLabelStep

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

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntrySymmetry_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntrySymmetry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryTransportedPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryTransportedPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_nonarchimedeanEntryLabelTransport_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_nonarchimedeanEntryLabelTransport_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
/--
Theta-image quotient audit for a source-labelled nonarchimedean `(Ind2)`
transport.

This lifts the audited possible-image quotient step from the place-audited
family to the source package's theta-pilot possible-image family.
-/
structure NonarchimedeanEntryLabelTransportThetaPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) where
  audited_possible_image_audit :
    IUTStage1PlaceAuditedMultiradialImages.NonarchimedeanEntryLabelTransportPossibleImageAudit
      data.auditedImages fiberPackage hstep
  theta_region_eq :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂
  fiber_mem :
    hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places

set_option linter.style.longLine false in
def nonarchimedeanEntryLabelTransportThetaPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.NonarchimedeanIsmActionEntryLabelTransportStep
        audited₁ audited₂) :
    NonarchimedeanEntryLabelTransportThetaPossibleImageAudit
      data fiberPackage hstep :=
  { audited_possible_image_audit :=
      data.auditedImages.nonarchimedeanEntryLabelTransportPossibleImageAudit
        fiberPackage hstep,
    theta_region_eq :=
      data.region_eq_of_nonarchimedeanEntryLabelTransport_step hstep,
    fiber_mem := fiberPackage.entry_place_mem_fiber hstep.action_step }

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

theorem region_eq_of_archimedeanEntrySymmetry_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_archimedeanEntrySymmetry_step hstep

theorem region_eq_of_archimedeanEntryPacketLabel_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact data.auditedImages.region_eq_of_archimedeanEntryPacketLabel_step hstep

set_option linter.style.longLine false in
theorem region_eq_of_archimedeanEntryTransportedPacketLabel_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ := by
  rw [← data.audited_possibleImages_eq]
  exact
    data.auditedImages.region_eq_of_archimedeanEntryTransportedPacketLabel_step
      hstep

set_option linter.style.longLine false in
theorem region_eq_of_archimedeanEntryLabelTransport_step
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1PlaceAuditedDirectSummandPacketChoice
          coric IUTStage1PlaceKind.archimedean)}
    (data : IUTStage1PlaceAuditedMultiradialThetaImages package)
    {audited₁ audited₂ :
      IUTStage1PlaceAuditedDirectSummandPacketChoice
        coric IUTStage1PlaceKind.archimedean}
    (hstep :
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂ :=
  data.region_eq_of_archimedeanEntryTransportedPacketLabel_step
    hstep.toTransportedPacketLabelStep

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

theorem region_eq_and_fiber_mem_of_archimedeanEntrySymmetry_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntrySymmetryStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntrySymmetry_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

theorem region_eq_and_fiber_mem_of_archimedeanEntryPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_archimedeanEntryTransportedPacketLabel_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryTransportedPacketLabelStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryTransportedPacketLabel_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
theorem region_eq_and_fiber_mem_of_archimedeanEntryLabelTransport_step
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    data.possibleImages.images.region audited₁ =
        data.possibleImages.images.region audited₂ ∧
      hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places :=
  ⟨data.region_eq_of_archimedeanEntryLabelTransport_step hstep,
    fiberPackage.entry_place_mem_fiber hstep.action_step⟩

set_option linter.style.longLine false in
/--
Theta-image quotient audit for a source-labelled archimedean `(Ind2)`
transport.

This lifts the audited possible-image quotient step from the place-audited
family to the source package's theta-pilot possible-image family.
-/
structure ArchimedeanEntryLabelTransportThetaPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) where
  audited_possible_image_audit :
    IUTStage1PlaceAuditedMultiradialImages.ArchimedeanEntryLabelTransportPossibleImageAudit
      data.auditedImages fiberPackage hstep
  theta_region_eq :
    data.possibleImages.images.region audited₁ =
      data.possibleImages.images.region audited₂
  fiber_mem :
    hstep.action_step.action_entry.place ∈ fiberPackage.fiberAudit.fiber.places

set_option linter.style.longLine false in
def archimedeanEntryLabelTransportThetaPossibleImageAudit
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
      IUTStage1PlaceAuditedDirectSummandPacketChoice.ArchimedeanOrderTwoActionEntryLabelTransportStep
        audited₁ audited₂) :
    ArchimedeanEntryLabelTransportThetaPossibleImageAudit
      data fiberPackage hstep :=
  { audited_possible_image_audit :=
      data.auditedImages.archimedeanEntryLabelTransportPossibleImageAudit
        fiberPackage hstep,
    theta_region_eq :=
      data.region_eq_of_archimedeanEntryLabelTransport_step hstep,
    fiber_mem := fiberPackage.entry_place_mem_fiber hstep.action_step }

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

namespace ConcreteHodgeTheaterLogTheta

variable {coric : Type u} {l : PrimeGeFive}

abbrev Choice :=
  IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l

def ind1Action
    (data :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l) :
    IUTStage1Theorem311Ind1Action (Choice (coric := coric) (l := l)) :=
  { step := IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind1ProcessionStep,
    logVolume := data.logVolume,
    preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact data.ind1_preserves_processionNormalizedLogVolume hstep }

def ind2Action
    (data :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l) :
    IUTStage1Theorem311Ind2Action (Choice (coric := coric) (l := l)) :=
  { step := IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind2LocalTensorStep,
    logVolume := data.logVolume,
    preserves_processionNormalizedLogVolume := by
      intro choice₁ choice₂ hstep
      exact data.ind2_preserves_processionNormalizedLogVolume hstep }

def ind3Relation
    (data :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l) :
    IUTStage1Theorem311Ind3UpperSemiRelation
      (Choice (coric := coric) (l := l)) :=
  { step := IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiStep,
    logVolume := data.logVolume,
    upper_semi_logVolume := by
      intro choice₁ choice₂ hstep
      exact data.ind3_upper_semi_logVolume hstep }

def typedCore
    (data :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (Choice (coric := coric) (l := l)) :=
  { logVolume := data.logVolume,
    ind1 := ind1Action data,
    ind2 := ind2Action data,
    ind3 := ind3Relation data,
    ind1_logVolume_eq := rfl,
    ind2_logVolume_eq := rfl,
    ind3_logVolume_eq := rfl }

end ConcreteHodgeTheaterLogTheta

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

def equalitySetoid
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    Setoid choice :=
  core.equalityQuotient.setoid

def equalitySetoidQuotientMap
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    choice -> Quotient core.equalitySetoid :=
  core.equalityQuotient.setoidQuotientMap

theorem equalitySetoidQuotientMap_eq_iff
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice} :
    core.equalitySetoidQuotientMap choice₁ =
        core.equalitySetoidQuotientMap choice₂ ↔
      core.equalityQuotient.relation choice₁ choice₂ :=
  core.equalityQuotient.setoidQuotientMap_eq_iff

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

theorem ind1_equalitySetoidQuotientMap_eq
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind1.step choice₁ choice₂) :
    core.equalitySetoidQuotientMap choice₁ =
      core.equalitySetoidQuotientMap choice₂ :=
  (core.equalitySetoidQuotientMap_eq_iff).2
    (IUTStage1GeneratedIndeterminacyRelation.ind1 hstep)

theorem ind2_equalitySetoidQuotientMap_eq
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice)
    {choice₁ choice₂ : choice}
    (hstep : core.ind2.step choice₁ choice₂) :
    core.equalitySetoidQuotientMap choice₁ =
      core.equalitySetoidQuotientMap choice₂ :=
  (core.equalitySetoidQuotientMap_eq_iff).2
    (IUTStage1GeneratedIndeterminacyRelation.ind2 hstep)

/--
Exact setoid audit for the Theorem 3.11 equality quotient.

Unlike the legacy `Quot` map, this quotient is backed by the equivalence proof
stored in `IUTStage1IndeterminacyQuotient`; hence equality in the quotient is
definitionally equivalent to the generated `(Ind1)/(Ind2)` relation.  The
`(Ind3)` generator of this equality quotient is still false.
-/
structure EqualityQuotientSetoidAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) : Prop where
  equality_relation_is_equivalence :
    Equivalence core.equalityQuotient.relation
  equalitySetoid_relation :
    core.equalitySetoid.r = core.equalityQuotient.relation
  equalitySetoidQuotientMap_eq_iff :
    ∀ {choice₁ choice₂ : choice},
      core.equalitySetoidQuotientMap choice₁ =
          core.equalitySetoidQuotientMap choice₂ ↔
        core.equalityQuotient.relation choice₁ choice₂
  ind1_equalitySetoidQuotientMap_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        core.equalitySetoidQuotientMap choice₁ =
          core.equalitySetoidQuotientMap choice₂
  ind2_equalitySetoidQuotientMap_eq :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        core.equalitySetoidQuotientMap choice₁ =
          core.equalitySetoidQuotientMap choice₂
  equalityQuotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : choice},
      core.equalityGenerators.ind3_step choice₁ choice₂ -> False

theorem equalityQuotientSetoidAudit
    (core : IUTStage1Theorem311TypedIndeterminacyCore choice) :
    EqualityQuotientSetoidAudit core :=
  { equality_relation_is_equivalence :=
      core.equalityQuotient.is_equivalence,
    equalitySetoid_relation := rfl,
    equalitySetoidQuotientMap_eq_iff := by
      intro choice₁ choice₂
      exact core.equalitySetoidQuotientMap_eq_iff,
    ind1_equalitySetoidQuotientMap_eq := by
      intro choice₁ choice₂ hstep
      exact core.ind1_equalitySetoidQuotientMap_eq hstep,
    ind2_equalitySetoidQuotientMap_eq := by
      intro choice₁ choice₂ hstep
      exact core.ind2_equalitySetoidQuotientMap_eq hstep,
    equalityQuotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact core.equalityGenerators_ind3_false hstep }

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

namespace ConcreteHodgeTheaterLogTheta

variable {coric : Type u} {l : PrimeGeFive}

set_option linter.style.longLine false in
/--
Typed-source audit for a concrete `(Ind1)` procession transport.

The transport constructor is immediately viewed through the concrete typed
Theorem 3.11 core: it gives an `(Ind1)` generator, preserves the normalized
log-volume used by the core, and identifies the two choices in the
`(Ind1),(Ind2)` equality quotient.
-/
theorem typedInd1ProcessionTransportAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel)
    (column_eq : choice₁.coordinate.column = choice₂.coordinate.column)
    (row_eq : choice₁.coordinate.row = choice₂.coordinate.row)
    (logThetaColumn_eq :
      choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn)
    (coric_eq : choice₁.coric = choice₂.coric)
    (processionTransport :
      IUTStage1ProcessionState.ProcessionTransport
        choice₁.procession_state choice₂.procession_state)
    (local_tensor_eq :
      choice₁.local_tensor_state = choice₂.local_tensor_state)
    (upper_semi_eq :
      choice₁.upper_semi_state = choice₂.upper_semi_state) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    core.ind1.step choice₁ choice₂ ∧
      core.logVolume choice₁ = core.logVolume choice₂ ∧
        core.equalityQuotientMap choice₁ = core.equalityQuotientMap choice₂ ∧
          IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁ =
            IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂ := by
  intro core
  let hstep :=
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind1ProcessionStep.ofTypedProcessionTransport
      hodgeTheater_eq historyLabel_eq column_eq row_eq
      logThetaColumn_eq coric_eq processionTransport
      local_tensor_eq upper_semi_eq
  exact
    ⟨hstep,
      core.ind1_preserves_logVolume hstep,
      core.ind1_equalityQuotientMap_eq hstep,
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ind1_thetaPilotClass_eq hstep⟩

set_option linter.style.longLine false in
/--
Typed-source audit for a concrete `(Ind2)` local tensor transport.

The audit states the source-paper equality side of Theorem 3.11 at the local
tensor boundary: typed procession and upper-semi transports, together with the
direct-summand count equality, build the `(Ind2)` generator; the typed core then
proves normalized log-volume preservation and equality-quotient compatibility.
-/
theorem typedInd2LocalTransportAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (historyLabel_eq : choice₁.historyLabel = choice₂.historyLabel)
    (coordinate_eq : choice₁.coordinate = choice₂.coordinate)
    (processionTransport :
      IUTStage1ProcessionState.ProcessionTransport
        choice₁.procession_state choice₂.procession_state)
    (direct_summand_count_eq :
      choice₁.local_tensor_state.directSummandCount =
        choice₂.local_tensor_state.directSummandCount)
    (upperSemiTransport :
      IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
        choice₁.upper_semi_state choice₂.upper_semi_state)
    (coric_eq : choice₁.coric = choice₂.coric) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    core.ind2.step choice₁ choice₂ ∧
      core.logVolume choice₁ = core.logVolume choice₂ ∧
        core.equalityQuotientMap choice₁ = core.equalityQuotientMap choice₂ ∧
          IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁ =
            IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂ := by
  intro core
  let hstep :=
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind2LocalTensorStep.ofTypedLocalTransports
      hodgeTheater_eq historyLabel_eq coordinate_eq
      processionTransport direct_summand_count_eq
      upperSemiTransport coric_eq
  exact
    ⟨hstep,
      core.ind2_preserves_logVolume hstep,
      core.ind2_equalityQuotientMap_eq hstep,
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ind2_thetaPilotClass_eq hstep⟩

set_option linter.style.longLine false in
/--
Typed-source audit for a concrete `(Ind3)` upper-semi transport.

Unlike the previous two audits, this one returns the asymmetric typed
`Ind3UpperSemiStepAudit`: the step is certified as a one-sided log-volume
transport and is explicitly absent from the equality quotient.
-/
theorem typedInd3UpperSemiTransportAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hodgeTheater_eq : choice₁.hodgeTheater = choice₂.hodgeTheater)
    (column_eq : choice₁.coordinate.column = choice₂.coordinate.column)
    (logThetaColumn_eq :
      choice₁.coordinate.logThetaColumn = choice₂.coordinate.logThetaColumn)
    (coric_eq : choice₁.coric = choice₂.coric)
    (procession_eq : choice₁.procession_state = choice₂.procession_state)
    (local_tensor_eq : choice₁.local_tensor_state = choice₂.local_tensor_state)
    (upperSemiTransport :
      IUTStage1UpperSemiCompatibilityState.UpperSemiTransport
        choice₁.upper_semi_state choice₂.upper_semi_state) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    Ind3UpperSemiStepAudit core choice₁ choice₂ := by
  intro core
  let hstep :=
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiStep.ofTypedUpperSemiTransport
      hodgeTheater_eq column_eq logThetaColumn_eq coric_eq
      procession_eq local_tensor_eq upperSemiTransport
  exact core.ind3UpperSemiStepAudit hstep

set_option linter.style.longLine false in
/--
Record-based typed-source audit for a concrete `(Ind1)` procession transport.

This is the source-facing form used by the concrete Theorem 3.11 layer: the
transport source constructs the `(Ind1)` step, and the typed core supplies
log-volume preservation, equality-quotient compatibility, and theta-pilot class
invariance.
-/
theorem typedInd1ProcessionTransportSourceAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind1ProcessionTransportSource
        choice₁ choice₂) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    core.ind1.step choice₁ choice₂ ∧
      core.logVolume choice₁ = core.logVolume choice₂ ∧
        core.equalityQuotientMap choice₁ = core.equalityQuotientMap choice₂ ∧
          IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁ =
            IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂ := by
  intro core
  let hstep := source.toStep
  exact
    ⟨hstep,
      core.ind1_preserves_logVolume hstep,
      core.ind1_equalityQuotientMap_eq hstep,
      source.thetaPilotClass_eq⟩

set_option linter.style.longLine false in
/--
Record-based typed-source audit for a concrete `(Ind2)` local tensor transport.

The source record builds the equality-side `(Ind2)` step from the fixed
theta-pilot coordinate, typed procession/upper-semi transports, and the
direct-summand count equality.  The typed core then derives the normalized
log-volume equality and equality-quotient compatibility.
-/
theorem typedInd2LocalTensorTransportSourceAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind2LocalTensorTransportSource
        choice₁ choice₂) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    core.ind2.step choice₁ choice₂ ∧
      core.logVolume choice₁ = core.logVolume choice₂ ∧
        core.equalityQuotientMap choice₁ = core.equalityQuotientMap choice₂ ∧
          IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁ =
            IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂ := by
  intro core
  let hstep := source.toStep
  exact
    ⟨hstep,
      core.ind2_preserves_logVolume hstep,
      core.ind2_equalityQuotientMap_eq hstep,
      source.thetaPilotClass_eq⟩

set_option linter.style.longLine false in
/--
Record-based typed-source audit for a concrete `(Ind3)` upper-semi transport.

The source record constructs the `(Ind3)` step.  The resulting audit is
intentionally asymmetric: it gives the one-sided log-volume inequality and
certifies that this step is not an equality-quotient generator.
-/
theorem typedInd3UpperSemiTransportSourceAudit
    (indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiTransportSource
        choice₁ choice₂) :
    let core :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData;
    Ind3UpperSemiStepAudit core choice₁ choice₂ := by
  intro core
  exact core.ind3UpperSemiStepAudit source.toStep

set_option linter.style.longLine false in
/-- Construct the typed core from concrete finite-label averaged procession data. -/
def typedCoreOfProcessionNormalizedLogVolumeSource
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource
        coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :=
  typedCore source.toIndeterminacyData

set_option linter.style.longLine false in
/--
Typed-core audit for the concrete finite-label averaged source.

This is the Theorem 3.11 bridge from an actual `F_l`-average indexed by
theta-pilot classes to the typed `(Ind1),(Ind2),(Ind3)` source used by the
multiradial quotient machinery.
-/
structure ProcessionNormalizedLogVolumeSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource
        coric l) : Prop where
  finite_label_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource.Audit
      source
  typed_core :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l))
  core_logVolume_eq_average :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice =
        (Finset.univ.sum fun label : ZMod l.value =>
          (source.labelAverage
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice)).normalizedLogVolume
              label) /
          (l.value : Real)
  ind1_preserves_core_logVolume :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedLogVolumeSource source).ind1.step choice₁ choice₂ ->
        (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₁ =
          (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₂
  ind2_preserves_core_logVolume :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedLogVolumeSource source).ind2.step choice₁ choice₂ ->
        (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₁ =
          (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₂
  ind3_core_logVolume_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedLogVolumeSource source).ind3.step choice₁ choice₂ ->
        (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₁ <=
          (typedCoreOfProcessionNormalizedLogVolumeSource source).logVolume choice₂
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedLogVolumeSource source).equalityGenerators.ind3_step
        choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem processionNormalizedLogVolumeSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource
        coric l) :
    ProcessionNormalizedLogVolumeSourceTypedCoreAudit source :=
  { finite_label_source_audit := source.audit,
    typed_core := ⟨typedCoreOfProcessionNormalizedLogVolumeSource source⟩,
    core_logVolume_eq_average := by
      intro choice
      exact source.average_eq_fl_sum choice,
    ind1_preserves_core_logVolume := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedLogVolumeSource source).ind1_preserves_logVolume
          hstep,
    ind2_preserves_core_logVolume := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedLogVolumeSource source).ind2_preserves_logVolume
          hstep,
    ind3_core_logVolume_le := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedLogVolumeSource source).ind3_logVolume_le
          hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedLogVolumeSource source).equalityGenerators_ind3_false
          hstep }

set_option linter.style.longLine false in
/--
Construct the typed core from finite procession averages aligned with the
upper-semi source/target log-volume coordinates.
-/
def typedCoreOfProcessionNormalizedUpperSemiComparisonSource
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource
        coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :=
  typedCoreOfProcessionNormalizedLogVolumeSource
    source.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
/--
Typed-core audit for the upper-semi-derived finite procession source.

This records the point where the `(Ind3)` inequality stops being an arbitrary
field of the finite-average source: it is obtained from the upper-semi
source/target log-volume coordinates and their one-sided compatibility bound.
-/
structure ProcessionNormalizedUpperSemiComparisonSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource
        coric l) : Prop where
  upperSemi_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource.Audit
      source
  finite_label_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource.Audit
      source.toProcessionNormalizedLogVolumeSource
  typed_core :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l))
  core_logVolume_eq_average :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).logVolume choice =
        (Finset.univ.sum fun label : ZMod l.value =>
          (source.labelAverage
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice)).normalizedLogVolume
              label) /
          (l.value : Real)
  ind3_average_le_from_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiStep
        choice₁ choice₂) ->
        (source.labelAverage
          (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂)).averageLogVolume
  ind3_core_logVolume_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).ind3.step choice₁ choice₂ ->
        (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).logVolume choice₁ <=
          (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).logVolume choice₂
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).equalityGenerators.ind3_step
        choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem processionNormalizedUpperSemiComparisonSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource
        coric l) :
    ProcessionNormalizedUpperSemiComparisonSourceTypedCoreAudit source :=
  { upperSemi_source_audit := source.audit,
    finite_label_source_audit :=
      source.toProcessionNormalizedLogVolumeSource.audit,
    typed_core :=
      ⟨typedCoreOfProcessionNormalizedUpperSemiComparisonSource source⟩,
    core_logVolume_eq_average := by
      intro choice
      exact source.toProcessionNormalizedLogVolumeSource.average_eq_fl_sum choice,
    ind3_average_le_from_upperSemi := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_average hstep,
    ind3_core_logVolume_le := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).ind3_logVolume_le
          hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedUpperSemiComparisonSource source).equalityGenerators_ind3_false
          hstep }

set_option linter.style.longLine false in
/--
Construct the typed core from label-wise log-theta procession data.
-/
noncomputable def typedCoreOfLogThetaLabelProcessionUpperSemiSource
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.LogThetaLabelProcessionUpperSemiSource
        coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :=
  typedCoreOfProcessionNormalizedUpperSemiComparisonSource
    source.toProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/--
Typed-core audit for the label-wise log-theta procession source.

This is the lower Theorem 3.11 bridge from a concrete `ZMod l` label-wise
log-volume family to the typed `(Ind1),(Ind2),(Ind3)` source.  It records the
canonical full-label procession over each theta-pilot lattice node, the average
formula, and the upper-semi conversion of `(Ind3)`.
-/
structure LogThetaLabelProcessionUpperSemiSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.LogThetaLabelProcessionUpperSemiSource
        coric l) : Prop where
  labelwise_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.LogThetaLabelProcessionUpperSemiSource.Audit
      source
  upperSemi_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource.Audit
      source.toProcessionNormalizedUpperSemiComparisonSource
  finite_label_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedLogVolumeSource.Audit
      source.toProcessionNormalizedLogVolumeSource
  typed_core :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l))
  core_logVolume_eq_labelwise_average :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).logVolume choice =
        (Finset.univ.sum fun label : ZMod l.value =>
          source.labelLogVolume
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice)
            label) /
          (l.value : Real)
  ind3_average_le_from_labelwise_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiStep
        choice₁ choice₂) ->
        (source.labelAverage
          (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂)).averageLogVolume
  ind3_core_logVolume_le :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).ind3.step choice₁ choice₂ ->
        (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).logVolume choice₁ <=
          (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).logVolume choice₂
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).equalityGenerators.ind3_step
        choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem logThetaLabelProcessionUpperSemiSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.LogThetaLabelProcessionUpperSemiSource
        coric l) :
    LogThetaLabelProcessionUpperSemiSourceTypedCoreAudit source :=
  { labelwise_source_audit := source.audit,
    upperSemi_source_audit :=
      source.toProcessionNormalizedUpperSemiComparisonSource.audit,
    finite_label_source_audit :=
      source.toProcessionNormalizedLogVolumeSource.audit,
    typed_core :=
      ⟨typedCoreOfLogThetaLabelProcessionUpperSemiSource source⟩,
    core_logVolume_eq_labelwise_average := by
      intro choice
      exact source.toProcessionNormalizedLogVolumeSource.average_eq_fl_sum choice,
    ind3_average_le_from_labelwise_upperSemi := by
      intro choice₁ choice₂ hstep
      exact source.ind3_upper_semi_average hstep,
    ind3_core_logVolume_le := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).ind3_logVolume_le
          hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfLogThetaLabelProcessionUpperSemiSource source).equalityGenerators_ind3_false
          hstep }

set_option linter.style.longLine false in
/--
Construct the typed core from nonarchimedean vertical log-Kummer packet
alignment data.
-/
def typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedVerticalLogKummerPacketAlignmentSource
        coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :=
  typedCoreOfProcessionNormalizedUpperSemiComparisonSource
    source.toProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/--
Typed-core audit for the packet-aligned upper-semi source.

The audit records the lowered source chain
finite procession average -> packet normalized log-volume -> upper-semi
source/target coordinates -> one-sided `(Ind3)` inequality.
-/
structure ProcessionNormalizedVerticalLogKummerPacketAlignmentSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedVerticalLogKummerPacketAlignmentSource
        coric l) : Prop where
  packet_alignment_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedVerticalLogKummerPacketAlignmentSource.Audit
      source
  upperSemi_source_audit :
    IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedUpperSemiComparisonSource.Audit
      source.toProcessionNormalizedUpperSemiComparisonSource
  typed_core :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l))
  average_eq_packet_normalized :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.labelAverage
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice)).averageLogVolume =
        (source.packetState choice).capsuleFamily.normalizedLogVolume
  packet_tensor_alignment :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      (source.packetState choice).tensorState = choice.local_tensor_state
  ind3_average_le_from_packet_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : IUTStage1ConcreteHodgeTheaterLogThetaChoice.Ind3UpperSemiStep
        choice₁ choice₂) ->
        (source.labelAverage
          (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₁)).averageLogVolume <=
          (source.labelAverage
            (IUTStage1ConcreteHodgeTheaterLogThetaChoice.thetaPilotClass choice₂)).averageLogVolume
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
          source).equalityGenerators.ind3_step choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem processionNormalizedVerticalLogKummerPacketAlignmentSourceTypedCoreAudit
    (source :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.ProcessionNormalizedVerticalLogKummerPacketAlignmentSource
        coric l) :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSourceTypedCoreAudit
      source :=
  { packet_alignment_audit := source.audit,
    upperSemi_source_audit :=
      source.toProcessionNormalizedUpperSemiComparisonSource.audit,
    typed_core :=
      ⟨typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource source⟩,
    average_eq_packet_normalized := by
      intro choice
      exact source.average_eq_packetNormalized choice,
    packet_tensor_alignment := by
      intro choice
      exact source.packet_tensor_eq choice,
    ind3_average_le_from_packet_upperSemi := by
      intro choice₁ choice₂ hstep
      exact
        source.toProcessionNormalizedUpperSemiComparisonSource.ind3_upper_semi_average
          hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
          source).equalityGenerators_ind3_false hstep }

end ConcreteHodgeTheaterLogTheta

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
Recover the old possible-image compatibility record from an explicitly
quotient-indexed possible-image family.

This is the direction used by the concrete Theorem 3.11 source layer: the
mathematical input is a family on the `(Ind1,Ind2)` equality quotient, and Lean
derives the direct `(Ind1)`/`(Ind2)` image equalities required by the existing
multiradial corridor.  `(Ind3)` still contributes only the core upper-semi
log-volume inequality.
-/
def toCompatibility
    (quotientImages : EqualityQuotientPossibleImages core images) :
    PossibleImageQuotientCompatibility core images :=
  { ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact quotientImages.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact quotientImages.ind2_region_eq hstep,
    ind3_logVolume_upper := by
      intro choice₁ choice₂ hstep
      exact quotientImages.ind3_logVolume_le hstep }

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

namespace IUTStage1ConcreteHodgeTheaterLogThetaChoice

set_option linter.style.longLine false in
/--
Concrete theta-pilot possible-image source.

The possible-image family is first indexed by the theta-pilot class, i.e. by the
Hodge-theater history, the `n,m` log-theta lattice node, the log-theta column,
and the coric datum after forgetting the finite `F_l` label and the
local/upper-semi representatives.  Pulling this family back to concrete choices
therefore makes `(Ind1)` and `(Ind2)` image invariance a theorem from
`thetaPilotClass` preservation, while `(Ind3)` is still supplied only by the
one-sided typed-core upper-semi law.
-/
structure ThetaPilotClassPossibleImageSource
    {target : Copy}
    (coric : Type u) (l : PrimeGeFive) where
  classImages :
    RegionFamily target (ThetaPilotClass (coric := coric))

namespace ThetaPilotClassPossibleImageSource

variable {target : Copy} {coric : Type u} {l : PrimeGeFive}

/-- Pull back theta-pilot-class possible images to concrete choices. -/
def choiceImages
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l) :
    RegionFamily target
      (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :=
  { region := fun choice =>
      source.classImages.region (thetaPilotClass choice) }

theorem choiceImages_region
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l) :
    source.choiceImages.region choice =
      source.classImages.region (thetaPilotClass choice) :=
  rfl

theorem region_eq_of_thetaPilotClass_eq
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hclass : thetaPilotClass choice₁ = thetaPilotClass choice₂) :
    source.choiceImages.region choice₁ =
      source.choiceImages.region choice₂ := by
  simp [choiceImages, hclass]

theorem ind1_region_eq
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind1ProcessionStep choice₁ choice₂) :
    source.choiceImages.region choice₁ =
      source.choiceImages.region choice₂ :=
  source.region_eq_of_thetaPilotClass_eq (ind1_thetaPilotClass_eq hstep)

theorem ind2_region_eq
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l}
    (hstep : Ind2LocalTensorStep choice₁ choice₂) :
    source.choiceImages.region choice₁ =
      source.choiceImages.region choice₂ :=
  source.region_eq_of_thetaPilotClass_eq (ind2_thetaPilotClass_eq hstep)

set_option linter.style.longLine false in
/--
The concrete theta-pilot possible-image source satisfies the typed
possible-image quotient compatibility for the concrete Theorem 3.11 core.

This is the source-facing construction of the `(Ind1)/(Ind2)` equality quotient:
the region equalities are derived from theta-pilot-class invariance.  The
`(Ind3)` field is not converted into a region equality; it is exactly the
one-sided upper-semi log-volume theorem of the typed core.
-/
def toPossibleImageQuotientCompatibility
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (indData : IndeterminacyData coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData)
      source.choiceImages :=
  { ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_region_eq hstep,
    ind3_logVolume_upper := by
      intro choice₁ choice₂ hstep
      exact
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
          indData).ind3_logVolume_le hstep }

set_option linter.style.longLine false in
/--
Construct the quotient-indexed possible-image family from concrete
Hodge-theater/log-theta theta-pilot data.

The resulting family is indexed by the equality quotient generated by concrete
`(Ind1)` and `(Ind2)` steps.  It is obtained without an `(Ind3)` region-equality
hypothesis.
-/
def toEqualityQuotientPossibleImages
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (indData : IndeterminacyData coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
        indData)
      source.choiceImages :=
  IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages.ofCompatibility
    (source.toPossibleImageQuotientCompatibility indData)

set_option linter.style.longLine false in
/--
Compatibility from concrete theta-pilot possible images and finite-label
averaged procession log-volumes.

This is the quotient possible-image boundary with the old raw
`IndeterminacyData` hidden behind the concrete `F_l` averaged source.
-/
def toPossibleImageQuotientCompatibilityOfProcessionNormalized
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedLogVolumeSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedLogVolumeSource
        volumeSource)
      source.choiceImages :=
  source.toPossibleImageQuotientCompatibility volumeSource.toIndeterminacyData

set_option linter.style.longLine false in
/--
Construct quotient-indexed possible images directly from concrete theta-pilot
class images and the finite `F_l` procession-normalized log-volume source.
-/
def toEqualityQuotientPossibleImagesOfProcessionNormalized
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedLogVolumeSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedLogVolumeSource
        volumeSource)
      source.choiceImages :=
  IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages.ofCompatibility
    (source.toPossibleImageQuotientCompatibilityOfProcessionNormalized
      volumeSource)

set_option linter.style.longLine false in
/--
Compatibility from concrete theta-pilot possible images and an upper-semi
derived finite-procession source.
-/
def toPossibleImageQuotientCompatibilityOfProcessionNormalizedUpperSemi
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedUpperSemiComparisonSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedUpperSemiComparisonSource
        volumeSource)
      source.choiceImages :=
  source.toPossibleImageQuotientCompatibilityOfProcessionNormalized
    volumeSource.toProcessionNormalizedLogVolumeSource

set_option linter.style.longLine false in
/--
Construct quotient-indexed possible images directly from theta-pilot class
images and the upper-semi-derived finite `F_l` procession source.
-/
def toEqualityQuotientPossibleImagesOfProcessionNormalizedUpperSemi
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedUpperSemiComparisonSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedUpperSemiComparisonSource
        volumeSource)
      source.choiceImages :=
  IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages.ofCompatibility
    (source.toPossibleImageQuotientCompatibilityOfProcessionNormalizedUpperSemi
      volumeSource)

set_option linter.style.longLine false in
/--
Compatibility from concrete theta-pilot possible images and a vertical
log-Kummer packet-aligned finite-procession source.
-/
def toPossibleImageQuotientCompatibilityOfVerticalLogKummerPacketAlignment
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource :
      ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
        volumeSource)
      source.choiceImages :=
  source.toPossibleImageQuotientCompatibilityOfProcessionNormalizedUpperSemi
    volumeSource.toProcessionNormalizedUpperSemiComparisonSource

set_option linter.style.longLine false in
/--
Construct quotient-indexed possible images directly from theta-pilot class
images and the vertical log-Kummer packet-aligned finite procession source.
-/
def toEqualityQuotientPossibleImagesOfVerticalLogKummerPacketAlignment
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource :
      ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l) :
    IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
        volumeSource)
      source.choiceImages :=
  IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages.ofCompatibility
    (source.toPossibleImageQuotientCompatibilityOfVerticalLogKummerPacketAlignment
      volumeSource)

set_option linter.style.longLine false in
/--
Audit of the concrete theta-pilot possible-image construction.

It records the actual pullback from theta-pilot classes, the induced
quotient-indexed family, the `(Ind1)/(Ind2)` region equalities, and the
remaining one-sided `(Ind3)` upper-semi law.
-/
structure Audit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (indData : IndeterminacyData coric l) : Prop where
  choice_region_is_thetaPilot_pullback :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      source.choiceImages.region choice =
        source.classImages.region (thetaPilotClass choice)
  equality_quotient_possible_images :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
          indData)
        source.choiceImages)
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind1ProcessionStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind2LocalTensorStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind3_upper_semi_logVolume :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind3UpperSemiStep choice₁ choice₂ ->
        indData.logVolume choice₁ <= indData.logVolume choice₂
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
          indData).equalityGenerators.ind3_step choice₁ choice₂ ->
        False

theorem audit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (indData : IndeterminacyData coric l) :
    Audit source indData :=
  { choice_region_is_thetaPilot_pullback := by
      intro choice
      exact source.choiceImages_region choice,
    equality_quotient_possible_images :=
      ⟨source.toEqualityQuotientPossibleImages indData⟩,
    ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_region_eq hstep,
    ind3_upper_semi_logVolume := by
      intro choice₁ choice₂ hstep
      exact indData.ind3_upper_semi_logVolume hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
          indData).equalityGenerators_ind3_false hstep }

set_option linter.style.longLine false in
/--
Audit of the concrete theta-pilot possible-image construction when the typed
core is built from finite-label averaged procession log-volumes.
-/
structure ProcessionNormalizedAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedLogVolumeSource coric l) : Prop where
  finite_label_source_audit :
    ProcessionNormalizedLogVolumeSource.Audit volumeSource
  typed_core_audit :
    IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.ProcessionNormalizedLogVolumeSourceTypedCoreAudit
      volumeSource
  equality_quotient_possible_images :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedLogVolumeSource
          volumeSource)
        source.choiceImages)
  choice_region_is_thetaPilot_pullback :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      source.choiceImages.region choice =
        source.classImages.region (thetaPilotClass choice)
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind1ProcessionStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind2LocalTensorStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind3_upper_semi_logVolume :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind3UpperSemiStep choice₁ choice₂ ->
        volumeSource.logVolume choice₁ <= volumeSource.logVolume choice₂
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedLogVolumeSource
          volumeSource).equalityGenerators.ind3_step choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem processionNormalizedAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedLogVolumeSource coric l) :
    ProcessionNormalizedAudit source volumeSource :=
  { finite_label_source_audit := volumeSource.audit,
    typed_core_audit :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.processionNormalizedLogVolumeSourceTypedCoreAudit
        volumeSource,
    equality_quotient_possible_images :=
      ⟨source.toEqualityQuotientPossibleImagesOfProcessionNormalized
        volumeSource⟩,
    choice_region_is_thetaPilot_pullback := by
      intro choice
      exact source.choiceImages_region choice,
    ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_region_eq hstep,
    ind3_upper_semi_logVolume := by
      intro choice₁ choice₂ hstep
      exact volumeSource.ind3_upper_semi_logVolume hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedLogVolumeSource
          volumeSource).equalityGenerators_ind3_false hstep }

set_option linter.style.longLine false in
/--
Audit of the concrete theta-pilot possible-image construction when the finite
procession source is derived from upper-semi source/target log-volume
alignment.
-/
structure ProcessionNormalizedUpperSemiAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedUpperSemiComparisonSource coric l) : Prop where
  upperSemi_source_audit :
    ProcessionNormalizedUpperSemiComparisonSource.Audit volumeSource
  typed_core_audit :
    IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.ProcessionNormalizedUpperSemiComparisonSourceTypedCoreAudit
      volumeSource
  equality_quotient_possible_images :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedUpperSemiComparisonSource
          volumeSource)
        source.choiceImages)
  choice_region_is_thetaPilot_pullback :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      source.choiceImages.region choice =
        source.classImages.region (thetaPilotClass choice)
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind1ProcessionStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind2LocalTensorStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind3_average_le_from_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (volumeSource.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (volumeSource.labelAverage (thetaPilotClass choice₂)).averageLogVolume
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedUpperSemiComparisonSource
          volumeSource).equalityGenerators.ind3_step choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem processionNormalizedUpperSemiAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource : ProcessionNormalizedUpperSemiComparisonSource coric l) :
    ProcessionNormalizedUpperSemiAudit source volumeSource :=
  { upperSemi_source_audit := volumeSource.audit,
    typed_core_audit :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.processionNormalizedUpperSemiComparisonSourceTypedCoreAudit
        volumeSource,
    equality_quotient_possible_images :=
      ⟨source.toEqualityQuotientPossibleImagesOfProcessionNormalizedUpperSemi
        volumeSource⟩,
    choice_region_is_thetaPilot_pullback := by
      intro choice
      exact source.choiceImages_region choice,
    ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_region_eq hstep,
    ind3_average_le_from_upperSemi := by
      intro choice₁ choice₂ hstep
      exact volumeSource.ind3_upper_semi_average hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedUpperSemiComparisonSource
          volumeSource).equalityGenerators_ind3_false hstep }

set_option linter.style.longLine false in
/--
Audit of the concrete theta-pilot possible-image construction from vertical
log-Kummer packet-aligned procession data.
-/
structure VerticalLogKummerPacketAlignmentAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource :
      ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l) : Prop where
  packet_alignment_audit :
    ProcessionNormalizedVerticalLogKummerPacketAlignmentSource.Audit volumeSource
  typed_core_audit :
    IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.ProcessionNormalizedVerticalLogKummerPacketAlignmentSourceTypedCoreAudit
      volumeSource
  equality_quotient_possible_images :
    Nonempty
      (IUTStage1Theorem311TypedIndeterminacyCore.EqualityQuotientPossibleImages
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
          volumeSource)
        source.choiceImages)
  choice_region_is_thetaPilot_pullback :
    ∀ choice : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l,
      source.choiceImages.region choice =
        source.classImages.region (thetaPilotClass choice)
  ind1_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind1ProcessionStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind2_region_eq :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      Ind2LocalTensorStep choice₁ choice₂ ->
        source.choiceImages.region choice₁ =
          source.choiceImages.region choice₂
  ind3_average_le_from_packet_upperSemi :
    ∀ {choice₁ choice₂ : IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (hstep : Ind3UpperSemiStep choice₁ choice₂) ->
        (volumeSource.labelAverage (thetaPilotClass choice₁)).averageLogVolume <=
          (volumeSource.labelAverage (thetaPilotClass choice₂)).averageLogVolume
  equality_quotient_no_ind3_generator :
    ∀ {choice₁ choice₂ :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l},
      (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
          volumeSource).equalityGenerators.ind3_step choice₁ choice₂ ->
        False

set_option linter.style.longLine false in
theorem verticalLogKummerPacketAlignmentAudit
    (source : ThetaPilotClassPossibleImageSource
      (target := target) coric l)
    (volumeSource :
      ProcessionNormalizedVerticalLogKummerPacketAlignmentSource coric l) :
    VerticalLogKummerPacketAlignmentAudit source volumeSource :=
  { packet_alignment_audit := volumeSource.audit,
    typed_core_audit :=
      IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.processionNormalizedVerticalLogKummerPacketAlignmentSourceTypedCoreAudit
        volumeSource,
    equality_quotient_possible_images :=
      ⟨source.toEqualityQuotientPossibleImagesOfVerticalLogKummerPacketAlignment
        volumeSource⟩,
    choice_region_is_thetaPilot_pullback := by
      intro choice
      exact source.choiceImages_region choice,
    ind1_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind1_region_eq hstep,
    ind2_region_eq := by
      intro choice₁ choice₂ hstep
      exact source.ind2_region_eq hstep,
    ind3_average_le_from_packet_upperSemi := by
      intro choice₁ choice₂ hstep
      exact
        volumeSource.toProcessionNormalizedUpperSemiComparisonSource.ind3_upper_semi_average
          hstep,
    equality_quotient_no_ind3_generator := by
      intro choice₁ choice₂ hstep
      exact
        (IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCoreOfProcessionNormalizedVerticalLogKummerPacketAlignmentSource
          volumeSource).equalityGenerators_ind3_false hstep }

end ThetaPilotClassPossibleImageSource

end IUTStage1ConcreteHodgeTheaterLogThetaChoice

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
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      core images ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂) ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂) ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂) ∧
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

theorem possibleImagesDependOnEqualityQuotient
    (obligations : Theorem311AndRemarksObligations core images)
    (audit : RemainingPayloadAudit obligations) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      core images := by
  rcases audit with ⟨_, _, _, _, _, hcompat, _, _, _⟩
  exact hcompat

theorem possibleImagesInd1RegionEq
    (obligations : Theorem311AndRemarksObligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  rcases audit with ⟨_, _, _, _, _, _, hind1, _⟩
  exact hind1

theorem possibleImagesInd2RegionEq
    (obligations : Theorem311AndRemarksObligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  rcases audit with ⟨_, _, _, _, _, _, _, hind2, _⟩
  exact hind2

theorem possibleImagesInd3UpperSemiLogVolume
    (obligations : Theorem311AndRemarksObligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂ := by
  rcases audit with ⟨_, _, _, _, _, _, _, _, hind3, _⟩
  exact hind3

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
  finite_place_scale_and_gap_sum_identifications_constructed : Prop
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
  obligations.finite_place_scale_and_gap_sum_identifications_constructed ∧
    obligations.finite_place_summed_stepxi_haar_bound_constructed ∧
    obligations.finite_place_total_haar_defect_ge_one_constructed ∧
    obligations.iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed ∧
    obligations.ordered_real_plus_one_cancellation_constructed ∧
    obligations.local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed ∧
    obligations.finite_place_arithmetic_gap_constructed ∧
    obligations.local_to_global_canonicalCThetaScale_le_cTheta_constructed

theorem finitePlaceScaleAndGapSumIdentificationsConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_scale_and_gap_sum_identifications_constructed :=
  audit.1

theorem finitePlaceSummedStepXIHaarBoundConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_summed_stepxi_haar_bound_constructed :=
  audit.2.1

theorem finitePlaceTotalHaarDefectGeOneConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_total_haar_defect_ge_one_constructed :=
  audit.2.2.1

theorem iutIVCThetaPlusOneEqArithmeticGapConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.iutiv_cTheta_plus_one_eq_arithmetic_gap_constructed :=
  audit.2.2.2.1

theorem orderedRealPlusOneCancellationConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.ordered_real_plus_one_cancellation_constructed :=
  audit.2.2.2.2.1

theorem localStepXITermMatchesIUTIVArithmeticUpperMinusMainConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.local_stepxi_term_matches_iutiv_arithmetic_upper_minus_main_constructed :=
  audit.2.2.2.2.2.1

theorem finitePlaceArithmeticGapConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.finite_place_arithmetic_gap_constructed :=
  audit.2.2.2.2.2.2.1

theorem localToGlobalCanonicalCThetaScaleLeCThetaConstructed
    (obligations : IUTIVCThetaObligations)
    (audit : LocalToGlobalArithmeticChainAudit obligations) :
    obligations.local_to_global_canonicalCThetaScale_le_cTheta_constructed :=
  audit.2.2.2.2.2.2.2

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
  formula_gap_local_estimate_audit_threaded : Prop
  arithmetic_degree_calibration_audit_threaded : Prop
  padic_prime_error_formula_matching_endpoint_threaded : Prop
  realified_packet_source_supplies_stepx_equalities : Prop
  constructed_ipl_choice_link_endpoint_threaded : Prop
  constructed_ipl_datum_certificate_alignment_threaded : Prop
  constructed_hodge_she_ipl_apt_structures_threaded : Prop
  constructed_she_apt_transport_guards_threaded : Prop
  constructed_she_no_domain_to_codomain_transport_threaded : Prop
  constructed_apt_transport_not_forbidden_threaded : Prop
  constructed_apt_transport_audit_threaded : Prop
  constructed_apt_datum_quotient_endpoint_threaded : Prop
  constructed_ipl_she_apt_transport_law_audit_threaded : Prop
  strongest_additive_haar_endpoint_has_remaining_payload_audit : Prop

namespace AdditiveHaarArithmeticDegreePadicObligations

def FineLocalPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations) : Prop :=
  obligations.formula_gap_local_estimate_audit_threaded ∧
    obligations.arithmetic_degree_calibration_audit_threaded ∧
    obligations.padic_prime_error_formula_matching_endpoint_threaded

def CoarsePayloadAudit
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
    obligations.constructed_she_no_domain_to_codomain_transport_threaded ∧
    obligations.constructed_apt_transport_not_forbidden_threaded ∧
    obligations.constructed_apt_transport_audit_threaded ∧
    obligations.constructed_apt_datum_quotient_endpoint_threaded ∧
    obligations.constructed_ipl_she_apt_transport_law_audit_threaded ∧
    obligations.strongest_additive_haar_endpoint_has_remaining_payload_audit

def RemainingPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations) : Prop :=
  CoarsePayloadAudit obligations ∧ FineLocalPayloadAudit obligations

theorem coarsePayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    CoarsePayloadAudit obligations :=
  audit.1

theorem fineLocalPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    FineLocalPayloadAudit obligations :=
  audit.2

theorem formulaGapLocalEstimateAuditThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : FineLocalPayloadAudit obligations) :
    obligations.formula_gap_local_estimate_audit_threaded :=
  audit.1

theorem arithmeticDegreeCalibrationAuditThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : FineLocalPayloadAudit obligations) :
    obligations.arithmetic_degree_calibration_audit_threaded :=
  audit.2.1

theorem padicPrimeErrorFormulaMatchingEndpointThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : FineLocalPayloadAudit obligations) :
    obligations.padic_prime_error_formula_matching_endpoint_threaded :=
  audit.2.2

theorem constructedIPLChoiceLinkEndpointThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_choice_link_endpoint_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedIPLCertificateAlignmentThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_datum_certificate_alignment_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedHodgeSHEIPLAPTStructuresThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_hodge_she_ipl_apt_structures_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedSHEAPTTransportGuardsThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_she_apt_transport_guards_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedSHENoDomainToCodomainTransportThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_she_no_domain_to_codomain_transport_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedAPTTransportNotForbiddenThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_apt_transport_not_forbidden_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedAPTTransportAuditThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_apt_transport_audit_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedAPTDatumQuotientEndpointThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_apt_datum_quotient_endpoint_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem constructedIPLSHEAPTTransportLawAuditThreaded
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.constructed_ipl_she_apt_transport_law_audit_threaded := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem theorem110AdditiveHaarLocalAnalyticConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.theorem110_additive_haar_local_analytic_construction_constructed := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem additiveHaarLocalArithmeticMatchingConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_local_arithmetic_matching_constructed := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem arithmeticDivisorFormulaSplitConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.arithmetic_divisor_formula_split_constructed := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem padicPrimeErrorDefectMainSplitConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.padic_prime_error_defect_main_split_constructed := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem stepXIArithmeticDegreeCalibrationConstructed
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.stepxi_arithmetic_degree_calibration_constructed := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem localizedDeterminantMultiplicityMatchesIUTIVCoefficient
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.localized_determinant_multiplicity_matches_iutiv_coefficient := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem adjustedRawLogVolumeMatchesDifferentPlusConductor
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.adjusted_raw_log_volume_matches_different_plus_conductor := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem realifiedPacketSourceSuppliesStepXEqualities
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.realified_packet_source_supplies_stepx_equalities := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

theorem strongestAdditiveHaarEndpointHasRemainingPayloadAudit
    (obligations : AdditiveHaarArithmeticDegreePadicObligations)
    (audit : RemainingPayloadAudit obligations) :
    obligations.strongest_additive_haar_endpoint_has_remaining_payload_audit := by
  dsimp [RemainingPayloadAudit, CoarsePayloadAudit] at audit
  tauto

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
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      core images ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂) ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂) ∧
    (∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂) ∧
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
    obligations.iutIV_cTheta.finite_place_scale_and_gap_sum_identifications_constructed ∧
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

theorem theorem311PossibleImagesDependOnEqualityQuotient
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    IUTStage1Theorem311TypedIndeterminacyCore.PossibleImageQuotientCompatibility
      core images := by
  dsimp [RemainingPayloadAudit] at audit
  rcases audit with ⟨_, _, _, _, _, hcompat, _⟩
  exact hcompat

theorem theorem311PossibleImagesInd1RegionEq
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind1.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  dsimp [RemainingPayloadAudit] at audit
  rcases audit with ⟨_, _, _, _, _, _, hind1, _⟩
  exact hind1

theorem theorem311PossibleImagesInd2RegionEq
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind2.step choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ := by
  dsimp [RemainingPayloadAudit] at audit
  rcases audit with ⟨_, _, _, _, _, _, _, hind2, _⟩
  exact hind2

theorem theorem311PossibleImagesInd3UpperSemiLogVolume
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.ind3.step choice₁ choice₂ ->
        core.logVolume choice₁ <= core.logVolume choice₂ := by
  dsimp [RemainingPayloadAudit] at audit
  rcases audit with ⟨_, _, _, _, _, _, _, _, hind3, _⟩
  exact hind3

theorem theorem311EqualityQuotientImageInvariant
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    ∀ {choice₁ choice₂ : choice},
      core.equalityQuotient.relation choice₁ choice₂ ->
        images.region choice₁ = images.region choice₂ :=
  (obligations.theorem311PossibleImagesDependOnEqualityQuotient audit)
    |>.equalityQuotient_image_invariant

theorem theorem311Ind3UpperFromImageCompatibility
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations)
    {choice₁ choice₂ : choice}
    (hstep : core.ind3.step choice₁ choice₂) :
    core.logVolume choice₁ <= core.logVolume choice₂ :=
  (obligations.theorem311PossibleImagesDependOnEqualityQuotient audit)
    |>.ind3_upper_from_core hstep

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

theorem localToGlobalArithmeticChainAudit
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    IUTIVCThetaObligations.LocalToGlobalArithmeticChainAudit
      obligations.iutIV_cTheta := by
  dsimp [RemainingPayloadAudit,
    IUTIVCThetaObligations.LocalToGlobalArithmeticChainAudit] at audit ⊢
  tauto

theorem additiveHaarArithmeticDegreePadicRemainingPayloadAudit
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    AdditiveHaarArithmeticDegreePadicObligations.RemainingPayloadAudit
      obligations.additive_haar_arithmetic_degree_padic := by
  dsimp [RemainingPayloadAudit] at audit
  tauto

theorem additiveHaarFineLocalPayloadAudit
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    AdditiveHaarArithmeticDegreePadicObligations.FineLocalPayloadAudit
      obligations.additive_haar_arithmetic_degree_padic :=
  AdditiveHaarArithmeticDegreePadicObligations.fineLocalPayloadAudit
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarFormulaGapLocalEstimateAuditThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.formula_gap_local_estimate_audit_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.formulaGapLocalEstimateAuditThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarFineLocalPayloadAudit audit)

theorem additiveHaarArithmeticDegreeCalibrationAuditThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.arithmetic_degree_calibration_audit_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.arithmeticDegreeCalibrationAuditThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarFineLocalPayloadAudit audit)

theorem additiveHaarPadicPrimeErrorFormulaMatchingEndpointThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.padic_prime_error_formula_matching_endpoint_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.padicPrimeErrorFormulaMatchingEndpointThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarFineLocalPayloadAudit audit)

theorem additiveHaarTheorem110LocalAnalyticConstructed
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.theorem110_additive_haar_local_analytic_construction_constructed :=
  AdditiveHaarArithmeticDegreePadicObligations.theorem110AdditiveHaarLocalAnalyticConstructed
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarLocalArithmeticMatchingConstructed
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.additive_haar_local_arithmetic_matching_constructed :=
  AdditiveHaarArithmeticDegreePadicObligations.additiveHaarLocalArithmeticMatchingConstructed
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarArithmeticDivisorFormulaSplitConstructed
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.arithmetic_divisor_formula_split_constructed :=
  AdditiveHaarArithmeticDegreePadicObligations.arithmeticDivisorFormulaSplitConstructed
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarPadicPrimeErrorDefectMainSplitConstructed
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.padic_prime_error_defect_main_split_constructed :=
  AdditiveHaarArithmeticDegreePadicObligations.padicPrimeErrorDefectMainSplitConstructed
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarStepXIArithmeticDegreeCalibrationConstructed
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.stepxi_arithmetic_degree_calibration_constructed :=
  AdditiveHaarArithmeticDegreePadicObligations.stepXIArithmeticDegreeCalibrationConstructed
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

set_option linter.style.longLine false in
theorem additiveHaarLocalizedDeterminantMultiplicityMatchesIUTIVCoefficient
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.localized_determinant_multiplicity_matches_iutiv_coefficient :=
  AdditiveHaarArithmeticDegreePadicObligations.localizedDeterminantMultiplicityMatchesIUTIVCoefficient
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarAdjustedRawLogVolumeMatchesDifferentPlusConductor
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.adjusted_raw_log_volume_matches_different_plus_conductor :=
  AdditiveHaarArithmeticDegreePadicObligations.adjustedRawLogVolumeMatchesDifferentPlusConductor
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarRealifiedPacketSourceSuppliesStepXEqualities
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.realified_packet_source_supplies_stepx_equalities :=
  AdditiveHaarArithmeticDegreePadicObligations.realifiedPacketSourceSuppliesStepXEqualities
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedIPLChoiceLinkEndpointThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_ipl_choice_link_endpoint_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedIPLChoiceLinkEndpointThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedIPLCertificateAlignmentThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_ipl_datum_certificate_alignment_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedIPLCertificateAlignmentThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedHodgeSHEIPLAPTStructuresThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_hodge_she_ipl_apt_structures_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedHodgeSHEIPLAPTStructuresThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedSHEAPTTransportGuardsThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_she_apt_transport_guards_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedSHEAPTTransportGuardsThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedSHENoDomainToCodomainTransportThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_she_no_domain_to_codomain_transport_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedSHENoDomainToCodomainTransportThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedAPTTransportNotForbiddenThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_apt_transport_not_forbidden_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedAPTTransportNotForbiddenThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedAPTTransportAuditThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_apt_transport_audit_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedAPTTransportAuditThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedAPTDatumQuotientEndpointThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_apt_datum_quotient_endpoint_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedAPTDatumQuotientEndpointThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarConstructedIPLSHEAPTTransportLawAuditThreaded
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.constructed_ipl_she_apt_transport_law_audit_threaded :=
  AdditiveHaarArithmeticDegreePadicObligations.constructedIPLSHEAPTTransportLawAuditThreaded
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem additiveHaarStrongestEndpointHasRemainingPayloadAudit
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.additive_haar_arithmetic_degree_padic
      |>.strongest_additive_haar_endpoint_has_remaining_payload_audit :=
  AdditiveHaarArithmeticDegreePadicObligations.strongestAdditiveHaarEndpointHasRemainingPayloadAudit
    obligations.additive_haar_arithmetic_degree_padic
    (obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit audit)

theorem closedEndpointRemovesThetaSignedLeCThetaAbsLogQHypothesis
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.closed_endpoint_removes_thetaSigned_le_cTheta_absLogQ_hypothesis := by
  dsimp [RemainingPayloadAudit] at audit
  tauto

theorem closedEndpointRemovesRawCanonicalCThetaScaleLeCThetaHypothesis
    (obligations : Obligations core images)
    (audit : RemainingPayloadAudit obligations) :
    obligations.closed_endpoint_removes_raw_canonicalCThetaScale_le_cTheta_hypothesis := by
  dsimp [RemainingPayloadAudit] at audit
  tauto

end Obligations

end IUTStage1Theorem311ToCorollary312PaperTrace
end Stage1
end Iut
