/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTheorem311

/-!
# Finite local Initial Theta groups as canonical MLF pairs

This module identifies the absolute-separable-closure Galois group stored by
the finite local Initial Theta core with the algebraic-closure model used by
MLF-Galois `TM`-pairs. The comparison is an actual topological group
isomorphism for the Krull topologies, not an input certificate.
-/

namespace Iut

universe u

open scoped Topology

namespace SourceMLFGaloisComparison

/--
Conjugation across an algebra equivalence is continuous for the two Krull
topologies. A basic open stabilizer of a finite intermediate field pulls back
to the stabilizer of its inverse image, which is again finite.
-/
theorem continuous_autCongr
    {K L E : Type u}
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (equivalence : L ≃ₐ[K] E) :
    Continuous (AlgEquiv.autCongr equivalence) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro targetNeighborhood target_mem
  rw [map_one, krullTopology_mem_nhds_one_iff] at target_mem
  rcases target_mem with
    ⟨targetField, target_finite, target_fixing_le⟩
  let sourceField : IntermediateField K L :=
    targetField.map equivalence.symm.toAlgHom
  letI : FiniteDimensional K targetField := target_finite
  letI : FiniteDimensional K sourceField :=
    LinearEquiv.finiteDimensional
      (IntermediateField.equivMap
        targetField equivalence.symm.toAlgHom).toLinearEquiv
  apply mem_nhds_iff.mpr
  refine
    ⟨sourceField.fixingSubgroup,
      ?_, IntermediateField.fixingSubgroup_isOpen sourceField,
      one_mem _⟩
  intro sigma sigma_mem
  apply target_fixing_le
  apply (IntermediateField.mem_fixingSubgroup_iff targetField _).mpr
  intro value value_mem
  have source_value_mem :
      equivalence.symm (value : E) ∈ sourceField := by
    change equivalence.symm (value : E) ∈
      targetField.map equivalence.symm.toAlgHom
    exact ⟨value, value_mem, rfl⟩
  have sigma_fixes :=
    ((IntermediateField.mem_fixingSubgroup_iff sourceField _).mp sigma_mem)
      (equivalence.symm (value : E)) source_value_mem
  change
    equivalence
        (sigma (equivalence.symm (value : E))) =
      value
  rw [sigma_fixes]
  exact equivalence.apply_symm_apply value

/-- Galois transport across an algebra equivalence is a topological group equivalence. -/
noncomputable def continuousAutCongr
    {K L E : Type u}
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (equivalence : L ≃ₐ[K] E) :
    Gal(L/K) ≃ₜ* Gal(E/K) where
  toMulEquiv := AlgEquiv.autCongr equivalence
  continuous_toFun := continuous_autCongr equivalence
  continuous_invFun := by
    change Continuous (AlgEquiv.autCongr equivalence).symm
    rw [AlgEquiv.autCongr_symm]
    exact continuous_autCongr equivalence.symm

/-- In characteristic zero, the absolute separable closure is the algebraic closure. -/
noncomputable def separableClosureEquivAlgebraicClosure
    (K : Type u) [Field K] [CharZero K] :
    SeparableClosure K ≃ₐ[K] AlgebraicClosure K :=
  (IntermediateField.equivOfEq
      ((separableClosure.eq_top_iff
        (F := K) (E := AlgebraicClosure K)).mpr inferInstance)).trans
    IntermediateField.topEquiv

/-- The two standard characteristic-zero absolute Galois models agree topologically. -/
noncomputable def absoluteGaloisEquiv
    (K : Type u) [Field K] [CharZero K] :
    Gal(SeparableClosure K / K) ≃ₜ*
      Gal(AlgebraicClosure K / K) :=
  continuousAutCongr (separableClosureEquivAlgebraicClosure K)

end SourceMLFGaloisComparison

namespace SourceMLFGaloisTMPair

/-- The canonical MLF pair on the separable-closure absolute Galois model. -/
noncomputable def monoAnalyticSeparable
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] :
    SourceMLFGaloisTMPair
      (TopologicalGroupCat.ofProfinite (AbsoluteGaloisProfinite K)) := by
  let comparison := SourceMLFGaloisComparison.absoluteGaloisEquiv K
  let modelPair := SourceMLFGaloisTMPair.monoAnalytic K
  exact
    { arithmeticMonoid := modelPair.arithmeticMonoid
      action := modelPair.action.comp comparison.toMonoidHom
      modelField := K
      modelFieldStructure := inferInstance
      modelValuativeRel := inferInstance
      modelTopology := inferInstance
      modelIsMLF := inferInstance
      modelCharZero := inferInstance
      model := modelPair.model
      groupIso := comparison.symm
      monoidIso := MulEquiv.refl _
      equivariant := by
        intro modelGroupElement modelMonoidElement
        change
          modelPair.action modelGroupElement modelMonoidElement =
            modelPair.action
              (comparison (comparison.symm modelGroupElement))
              modelMonoidElement
        rw [comparison.apply_symm_apply] }

end SourceMLFGaloisTMPair

noncomputable instance ThetaFinitePlace.completionValuativeRel
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    ValuativeRel (ThetaFinitePlace.Completion v) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (ThetaFinitePlace.Completion v)
      (WithZero (Multiplicative ℤ)))

noncomputable instance ThetaFinitePlace.completionValuationCompatible
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    (Valued.v : Valuation (ThetaFinitePlace.Completion v)
      (WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance ThetaFinitePlace.completionIsValuativeTopology
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    IsValuativeTopology (ThetaFinitePlace.Completion v) :=
  IsValuativeTopology.of_zero fun neighborhood => by
    rw [Valued.mem_nhds_zero]
    simpa using
      ((Valued.v : Valuation (ThetaFinitePlace.Completion v)
        (WithZero (Multiplicative ℤ))).exists_setOf_restrict_le_iff
          (0 : ThetaFinitePlace.Completion v) neighborhood)

noncomputable instance ThetaFinitePlace.completionIsNonarchimedeanLocalField
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    IsNonarchimedeanLocalField (ThetaFinitePlace.Completion v) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (ThetaFinitePlace.Completion v)
        (WithZero (Multiplicative ℤ)))).mpr inferInstance

namespace SourceThetaFiniteLocalCoreData

variable
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}

/-- The canonical MLF pair on the exact local Galois group of an Initial Theta core. -/
noncomputable def mlfGaloisTMPair
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    SourceMLFGaloisTMPair
      (TopologicalGroupCat.ofProfinite core.orbicurves.absoluteGalois) :=
  SourceMLFGaloisTMPair.monoAnalyticSeparable
    (ThetaFinitePlace.Completion v)

/-- The coefficient-identity unit Kummer embedding on the local Initial Theta group. -/
noncomputable def unitKummerEmbedding
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :=
  SourceIUTIIUnitKummerEmbedding.canonical core.mlfGaloisTMPair

/-- The constructed local Initial Theta unit Kummer map is faithful. -/
theorem unitKummer_injective
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    Function.Injective core.unitKummerEmbedding.unitKummer :=
  SourceIUTIIUnitKummerEmbedding.canonical_unitKummer_injective
    core.mlfGaloisTMPair

end SourceThetaFiniteLocalCoreData

end Iut
