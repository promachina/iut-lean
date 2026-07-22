/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidFilteredBirational

/-!
# Pre-Frobenioid structure on the model Hom-colimit birationalization

Frobenioids I, Proposition 4.4(ii) equips the category constructed from the
Hom colimits of Proposition 4.4(i) with a pre-Frobenioid structure over the
zero divisor monoid.  This file constructs that structure on the model, proves
that it is of group-like and Frobenius-normalized type, and proves Definition
4.5(i) model type for the canonical colimit localization functor.

The seven Definition 1.3 axiom groups needed to package this pre-Frobenioid as
a full `FrobenioidPresentation` remain separate obligations.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

namespace Carrier.ColimitBirationalObject

open CoAngularPreStepOver

/-- The colimit category's functor to the elementary Frobenioid over `0_D`. -/
def structureFunctor :
    ColimitBirationalObject (Phi := Phi) (data := data) ⥤
      ElementaryFrobenioid D IsFSM zeroDivisorialMonoidOn :=
  comparisonFunctor (Phi := Phi) (data := data) ⋙
    BirationalObject.structureFunctor (Phi := Phi) (data := data)

/-- Proposition 4.4(ii)'s pre-Frobenioid structure on the Hom-colimit model. -/
def preFrobenioid :
    PreFrobenioid
      (ColimitBirationalObject (Phi := Phi) (data := data)) D IsFSM where
  divisorMonoid := zeroDivisorialMonoidOn
  structureFunctor := structureFunctor

@[simp]
theorem preFrobenioid_frobeniusDegree
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree arrow =
      (colimitComparisonEquiv source.underlying target.underlying arrow).frobeniusDegree :=
  rfl

@[simp]
theorem preFrobenioid_base_map
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).base.map arrow =
      (colimitComparisonEquiv source.underlying target.underlying arrow).base :=
  rfl

/-- Fully faithful comparison transports linear base-identity endomorphisms. -/
def linearBaseIdentityEndomorphismMap
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object →*
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        ((comparisonFunctor (Phi := Phi) (data := data)).obj object) where
  toFun alpha :=
    { hom := (comparisonFunctor (Phi := Phi) (data := data)).map alpha.hom
      linear := alpha.linear
      baseIdentity := alpha.baseIdentity }
  map_one' := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    exact (comparisonFunctor (Phi := Phi) (data := data)).map_id object
  map_mul' first second := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    exact (comparisonFunctor (Phi := Phi) (data := data)).map_comp
      first.hom second.hom

/-- Frobenius normalization transfers from the concrete equivalent target. -/
theorem isFrobeniusNormalized
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalized
      object := by
  intro phi phiBase alpha
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  let endomorphismMap :=
    linearBaseIdentityEndomorphismMap (Phi := Phi) (data := data) object
  apply comparison.map_injective
  rw [comparison.map_comp, comparison.map_comp]
  have mappedPower := congrArg (fun endomorphism ↦ endomorphism.hom)
    (map_pow endomorphismMap alpha
      ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val)
  change comparison.map
        (alpha ^
          ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val).hom =
      (endomorphismMap alpha ^
        ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val).hom
    at mappedPower
  rw [mappedPower]
  exact BirationalObject.isFrobeniusNormalized (comparison.obj object)
    (comparison.map phi) phiBase (endomorphismMap alpha)

/-- The colimit birational pre-Frobenioid is Frobenius-normalized. -/
theorem isFrobeniusNormalizedType :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalizedType :=
  isFrobeniusNormalized

/-- Every object is group-like because the divisor monoid is `0_D`. -/
theorem isGroupLike
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsGroupLike object := by
  change ∀ value : PUnit, value = 0
  intro value
  cases value
  rfl

/-- Proposition 4.4(ii)'s group-like-type conclusion for the model target. -/
theorem isGroupLikeType :
    (preFrobenioid (Phi := Phi) (data := data)).IsGroupLikeType :=
  isGroupLike

/-- Definition 4.5(i) model type for the canonical filtered-colimit target. -/
theorem isModelTypeForColimitBirationalization :
    (Carrier.preFrobenioid Phi data).IsModelType
      (preFrobenioid (Phi := Phi) (data := data))
      (localizationFunctor (Phi := Phi) (data := data)) :=
  ⟨Carrier.isPreModelType,
    fun object ↦ isFrobeniusNormalized ⟨object⟩⟩

end Carrier.ColimitBirationalObject

end

end Iut.SourceModelFrobenioid
