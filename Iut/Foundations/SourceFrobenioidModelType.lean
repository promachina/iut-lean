/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid
import Mathlib.CategoryTheory.Skeletal

/-!
# Frobenioid model-type foundations

This file formalizes the source definitions needed for the model-type assertion
of Frobenioids I, Theorem 5.2(ii): Frobenius normalization from Definition
1.2(iv), and base-sections, Frobenius-sections, base-Frobenius pairs, and
pre-model type from Definition 2.7.
-/

open CategoryTheory

namespace Iut.PreFrobenioid

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable (P : PreFrobenioid C D IsFSM)

/-- Frobenioids I, Definition 1.2(iv): a Frobenius-normalized object. -/
def IsFrobeniusNormalized (X : C) : Prop :=
  ∀ (phi : X ⟶ X), P.IsBaseIdentity phi →
    ∀ alpha : P.LinearBaseIdentityEndomorphism X,
      phi ≫ (alpha ^ (P.frobeniusDegree phi).val).hom =
        alpha.hom ≫ phi

/-- Every object of the pre-Frobenioid is Frobenius-normalized. -/
def IsFrobeniusNormalizedType : Prop :=
  ∀ X : C, P.IsFrobeniusNormalized X

/--
Frobenioids I, Definition 2.7(i).  The section category is skeletal, embeds
faithfully through actual pullback arrows, projects equivalently to the base,
and consists of Frobenius-trivial objects.
-/
structure BaseSection where
  sectionCategory : Cat.{u, u}
  inclusion : sectionCategory ⥤ C
  skeletal : Skeletal sectionCategory
  inclusion_faithful : inclusion.Faithful
  map_isPullback :
    ∀ {X Y : sectionCategory} (f : X ⟶ Y), P.IsPullback (inclusion.map f)
  base_isEquivalence : (inclusion ⋙ P.base).IsEquivalence
  object_frobeniusTrivial :
    ∀ X : sectionCategory, P.IsFrobeniusTrivial (inclusion.obj X)

/--
Frobenioids I, Definition 2.7(ii): a multiplicative Frobenius section as
natural endomorphisms of the base-section inclusion.
-/
structure FrobeniusSection (baseSection : P.BaseSection) where
  lift : ℕ+ → (baseSection.inclusion ⟶ baseSection.inclusion)
  map_one : lift 1 = 𝟙 baseSection.inclusion
  map_mul : ∀ m n, lift (m * n) = lift m ≫ lift n
  degree_section :
    ∀ n X, P.frobeniusDegree ((lift n).app X) = n
  base_identity :
    ∀ n X, P.IsBaseIdentity ((lift n).app X)
  of_frobenius_type :
    ∀ n X, P.IsOfFrobeniusType ((lift n).app X)

/-- Frobenioids I, Definition 2.7(iii): a base-Frobenius pair. -/
structure BaseFrobeniusPair where
  baseSection : P.BaseSection
  frobeniusSection : P.FrobeniusSection baseSection

/-- Frobenioids I, Definition 2.7(iii): existence of a base-Frobenius pair. -/
def IsPreModelType : Prop :=
  Nonempty P.BaseFrobeniusPair

end Iut.PreFrobenioid
