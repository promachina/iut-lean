/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidColimitStructure

/-!
# Morphism dictionary for the model birationalization

Frobenioids I, Proposition 4.4(iv) identifies the morphism classes before and
after birationalization.  This file proves the core zero-divisor clauses for
the concrete model target, transports them to the actual Hom-colimit category,
and proves the corresponding iff statements for the canonical localization.

The pullback clause and the base-identity roof classification remain separate
obligations.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

namespace BirationalObject

/-- Every arrow in the zero-divisor target is an isometry. -/
theorem isIsometric
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric arrow := by
  change (default : PUnit) = 0
  rfl

/-- A pre-step in the concrete target is an isomorphism. -/
theorem isIso_of_isPreStep
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (preStep : (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow) :
    IsIso arrow := by
  exact (isoOfLinearBaseIso arrow preStep.1 preStep.2).isIso_hom

/-- An isomorphism in the concrete target has degree one and invertible base. -/
theorem isPreStep_of_isIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (arrowIsIso : IsIso arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow := by
  letI : IsIso arrow := arrowIsIso
  constructor
  · change arrow.frobeniusDegree = 1
    have identity := congrArg BirationalHom.frobeniusDegree
      (IsIso.hom_inv_id arrow)
    change arrow.frobeniusDegree * (inv arrow).frobeniusDegree = 1 at identity
    apply PNat.eq
    have valueIdentity := congrArg PNat.val identity
    exact Nat.eq_one_of_dvd_one ⟨(inv arrow).frobeniusDegree.val,
      valueIdentity.symm⟩
  · change IsIso
      ((preFrobenioid (Phi := Phi) (data := data)).base.map arrow)
    infer_instance

/-- Proposition 4.4(iv): target isomorphisms are precisely target pre-steps. -/
theorem isIso_iff_isPreStep
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    IsIso arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow :=
  ⟨isPreStep_of_isIso arrow, isIso_of_isPreStep arrow⟩

/-- Every arrow in the group-like target is co-angular. -/
theorem isCoAngular
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular arrow := by
  intro firstObject secondObject gamma beta alpha _ _ betaPreStep _ _
  exact isIso_of_isPreStep beta betaPreStep

/-- Every arrow in the group-like target is LB-invertible. -/
theorem isLBInvertible
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLBInvertible arrow :=
  ⟨isCoAngular arrow, isIsometric arrow⟩

/-- In the group-like target, Frobenius type means base-isomorphism. -/
theorem isOfFrobeniusType_iff_isBaseIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso arrow := by
  constructor
  · exact fun hypothesis ↦ hypothesis.2
  · exact fun hypothesis ↦ ⟨isLBInvertible arrow, hypothesis⟩

end BirationalObject

namespace Carrier.ColimitBirationalObject

/-- Every arrow in the Hom-colimit target is an isometry. -/
theorem isIsometric
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric arrow := by
  change (default : PUnit) = 0
  rfl

/-- The comparison preserves and reflects the pre-step predicate definitionally. -/
theorem isPreStep_iff_comparisonMap
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow ↔
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).IsPreStep
        ((comparisonFunctor (Phi := Phi) (data := data)).map arrow) :=
  Iff.rfl

/-- Proposition 4.4(iv): colimit isomorphisms are precisely pre-steps. -/
theorem isIso_iff_isPreStep
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    IsIso arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  constructor
  · intro arrowIsIso
    letI : IsIso arrow := arrowIsIso
    exact (isPreStep_iff_comparisonMap arrow).2
      (BirationalObject.isPreStep_of_isIso (comparison.map arrow)
        (inferInstance : IsIso (comparison.map arrow)))
  · intro preStep
    haveI : IsIso (comparison.map arrow) :=
      BirationalObject.isIso_of_isPreStep (comparison.map arrow)
        ((isPreStep_iff_comparisonMap arrow).1 preStep)
    exact isIso_of_reflects_iso arrow comparison

/-- Every arrow in the Hom-colimit group-like target is co-angular. -/
theorem isCoAngular
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular arrow := by
  intro firstObject secondObject gamma beta alpha _ _ betaPreStep _ _
  exact (isIso_iff_isPreStep beta).2 betaPreStep

/-- Every arrow in the Hom-colimit target is LB-invertible. -/
theorem isLBInvertible
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLBInvertible arrow :=
  ⟨isCoAngular arrow, isIsometric arrow⟩

/-- In the Hom-colimit target, Frobenius type means base-isomorphism. -/
theorem isOfFrobeniusType_iff_isBaseIso
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso arrow := by
  constructor
  · exact fun hypothesis ↦ hypothesis.2
  · exact fun hypothesis ↦ ⟨isLBInvertible arrow, hypothesis⟩

/-- A source arrow becomes invertible exactly when it is a source pre-step. -/
theorem localization_map_isIso_iff_isPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    IsIso ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow := by
  constructor
  · intro mappedIsIso
    let localization := localizationFunctor (Phi := Phi) (data := data)
    let comparison := comparisonFunctor (Phi := Phi) (data := data)
    letI : IsIso (localization.map arrow) := mappedIsIso
    have comparisonIsIso :
        IsIso (comparison.map (localization.map arrow)) := inferInstance
    have concreteIsIso : IsIso
        ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          arrow) := by
      rw [comparisonFunctor_map_localizationFunctor] at comparisonIsIso
      exact comparisonIsIso
    exact BirationalObject.isPreStep_of_isIso
      ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        arrow) concreteIsIso
  · exact localizationFunctor_map_isIso_of_preStep arrow

/-- Proposition 4.4(iv)'s exact source characterization of target isomorphisms. -/
theorem localization_map_isIso_iff_coAngularPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    IsIso ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow ∧
        (Carrier.preFrobenioid Phi data).IsCoAngular arrow := by
  rw [localization_map_isIso_iff_isPreStep]
  constructor
  · exact fun preStep ↦ ⟨preStep, Carrier.isCoAngular Phi data arrow⟩
  · exact fun hypothesis ↦ hypothesis.1

/-- The canonical functor preserves and reflects the base-isomorphism class. -/
theorem localization_map_isBaseIso_iff_isBaseIso
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsBaseIso arrow := by
  have mappedEquality := comparisonFunctor_map_localizationFunctor
    (Phi := Phi) (data := data) arrow
  have baseEquality := congrArg BirationalHom.base mappedEquality
  change IsIso
      ((comparisonFunctor (Phi := Phi) (data := data)).map
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).base ↔
    IsIso arrow.base
  rw [baseEquality]
  rfl

/-- The canonical functor preserves and reflects every fixed Frobenius degree. -/
theorem localization_map_frobeniusDegree_eq_iff
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (degree : ℕ+) :
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) = degree ↔
      (Carrier.preFrobenioid Phi data).frobeniusDegree arrow = degree := by
  have mappedEquality := comparisonFunctor_map_localizationFunctor
    (Phi := Phi) (data := data) arrow
  have degreeEquality := congrArg BirationalHom.frobeniusDegree mappedEquality
  change
    ((comparisonFunctor (Phi := Phi) (data := data)).map
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).frobeniusDegree =
        degree ↔
      arrow.frobeniusDegree = degree
  rw [degreeEquality]
  rfl

/-- The source Frobenius-type clause becomes co-angular base-isomorphism. -/
theorem localization_map_isOfFrobeniusType_iff
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow ∧
        (Carrier.preFrobenioid Phi data).IsBaseIso arrow := by
  rw [isOfFrobeniusType_iff_isBaseIso,
    localization_map_isBaseIso_iff_isBaseIso]
  constructor
  · exact fun baseIso ↦ ⟨Carrier.isCoAngular Phi data arrow, baseIso⟩
  · exact fun hypothesis ↦ hypothesis.2

/-- Proposition 4.4(iv)'s pre-step iff for the canonical source functor. -/
theorem localization_map_isPreStep_iff_isPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow := by
  rw [← localization_map_isIso_iff_isPreStep arrow]
  exact (isIso_iff_isPreStep
    ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).symm

/-- Proposition 4.4(iv)'s co-angular iff for the canonical source functor. -/
theorem localization_map_isCoAngular_iff_isCoAngular
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow :=
  ⟨fun _ ↦ Carrier.isCoAngular Phi data arrow,
    fun _ ↦ isCoAngular
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow)⟩

/-- Proposition 4.4(iv): every source arrow maps to an isometry. -/
theorem localization_map_isIsometric
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow) :=
  isIsometric _

end Carrier.ColimitBirationalObject

end

end Iut.SourceModelFrobenioid
