/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# The model-Frobenioid category of Frobenioids I, Theorem 5.2(i)

For a divisorial monoid `Phi`, a group-like rational-function monoid `B`, and
the natural divisor map `DivB : B -> Phi^gp`, Theorem 5.2(i) constructs a
category explicitly. Objects are pairs `(A_D, alpha)`. An arrow consists of a
positive Frobenius degree, a base arrow, an effective divisor, and a rational
function satisfying the source balance equation.

This file implements that category, its exact composition law, and its
structure functor to the elementary Frobenioid. The proof of Theorem 5.2(ii)
that this category satisfies every Frobenioid axiom is not asserted here.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceModelFrobenioid

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}

/-- A group-like monoid on the base category, written additively as in FrdI 5.2. -/
structure GroupLikeAddMonoidOn
    (D : Type u) [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop) where
  obj : D → Type u
  addCommGroup : ∀ X, AddCommGroup (obj X)
  pullback : ∀ {X Y : D}, (X ⟶ Y) → (obj Y →+ obj X)
  pullback_id : ∀ X, pullback (𝟙 X) = AddMonoidHom.id (obj X)
  pullback_comp :
    ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g)
  pullback_injective :
    ∀ {X Y : D} (f : X ⟶ Y), Function.Injective (pullback f)
  fsmPullbackIsIso :
    ∀ {X Y : D} (f : X ⟶ Y), IsFSM f → Function.Bijective (pullback f)

attribute [instance] GroupLikeAddMonoidOn.addCommGroup

/-- Pullback on the groupification of a divisorial monoid. -/
def gpPullback
    (Phi : DivisorialMonoidOn D IsFSM) {X Y : D} (f : X ⟶ Y) :
    Algebra.GrothendieckAddGroup (Phi.obj Y).carrier →+
      Algebra.GrothendieckAddGroup (Phi.obj X).carrier :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp (Phi.pullback f))

@[simp]
theorem gpPullback_of
    (Phi : DivisorialMonoidOn D IsFSM) {X Y : D} (f : X ⟶ Y)
    (value : (Phi.obj Y).carrier) :
    gpPullback Phi f (Algebra.GrothendieckAddGroup.of value) =
      Algebra.GrothendieckAddGroup.of (Phi.pullback f value) := by
  let map := Algebra.GrothendieckAddGroup.of.comp (Phi.pullback f)
  change (Algebra.GrothendieckAddGroup.lift map)
      (Algebra.GrothendieckAddGroup.of value) = map value
  change
    ((Algebra.GrothendieckAddGroup.lift map).comp
      Algebra.GrothendieckAddGroup.of) value = map value
  rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
  exact DFunLike.congr_fun
    (Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift map) value

theorem gpPullback_id
    (Phi : DivisorialMonoidOn D IsFSM) (X : D) :
    gpPullback Phi (𝟙 X) =
      AddMonoidHom.id (Algebra.GrothendieckAddGroup (Phi.obj X).carrier) := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  apply AddMonoidHom.ext
  intro value
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply]
  change
    gpPullback Phi (𝟙 X) (Algebra.GrothendieckAddGroup.of value) =
      Algebra.GrothendieckAddGroup.of value
  rw [gpPullback_of, Phi.pullback_id]
  rfl

theorem gpPullback_comp
    (Phi : DivisorialMonoidOn D IsFSM)
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    gpPullback Phi (f ≫ g) =
      (gpPullback Phi f).comp (gpPullback Phi g) := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  apply AddMonoidHom.ext
  intro value
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply]
  change
    gpPullback Phi (f ≫ g) (Algebra.GrothendieckAddGroup.of value) =
      gpPullback Phi f
        (gpPullback Phi g (Algebra.GrothendieckAddGroup.of value))
  rw [gpPullback_of, gpPullback_of, gpPullback_of, Phi.pullback_comp]
  rfl

/-- Input data of the explicit model-Frobenioid construction in FrdI 5.2. -/
structure Input
    (Phi : DivisorialMonoidOn D IsFSM) where
  rationalFunctions : GroupLikeAddMonoidOn D IsFSM
  divisor :
    ∀ X : D,
      rationalFunctions.obj X →+
        Algebra.GrothendieckAddGroup (Phi.obj X).carrier
  divisor_natural :
    ∀ {X Y : D} (f : X ⟶ Y) (value : rationalFunctions.obj Y),
      divisor X (rationalFunctions.pullback f value) =
        gpPullback Phi f (divisor Y value)

namespace Input

variable {Phi : DivisorialMonoidOn D IsFSM}

/-- The paper's `Phi_birat`, the image of the rational-function divisor map. -/
def birationalDivisors
    (data : Input Phi) (X : D) :
    AddSubgroup (Algebra.GrothendieckAddGroup (Phi.obj X).carrier) :=
  (data.divisor X).range

/-- Pullback carries the birational divisor subgroup into the one at the source. -/
theorem gpPullback_mem_birationalDivisors
    (data : Input Phi) {X Y : D} (f : X ⟶ Y)
    {value : Algebra.GrothendieckAddGroup (Phi.obj Y).carrier}
    (hvalue : value ∈ data.birationalDivisors Y) :
    gpPullback Phi f value ∈ data.birationalDivisors X := by
  rcases hvalue with ⟨rationalFunction, rfl⟩
  exact ⟨data.rationalFunctions.pullback f rationalFunction,
    data.divisor_natural f rationalFunction⟩

end Input

/-- An object `(A_D, alpha)` of the model Frobenioid. -/
structure Object (Phi : DivisorialMonoidOn D IsFSM) where
  base : D
  divisorClass : Algebra.GrothendieckAddGroup (Phi.obj base).carrier

/-- The four source fields of a model-Frobenioid arrow and their balance equation. -/
@[ext]
structure Hom
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)
    (source target : Object Phi) where
  frobeniusDegree : ℕ+
  base : source.base ⟶ target.base
  divisor : (Phi.obj source.base).carrier
  rationalFunction : data.rationalFunctions.obj source.base
  balance :
    frobeniusDegree.val • source.divisorClass +
        Algebra.GrothendieckAddGroup.of divisor =
      gpPullback Phi base target.divisorClass +
        data.divisor source.base rationalFunction

namespace Hom

variable (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)

/-- Identity arrow from Theorem 5.2(i). -/
def id (source : Object Phi) : Hom Phi data source source where
  frobeniusDegree := 1
  base := 𝟙 source.base
  divisor := 0
  rationalFunction := 0
  balance := by
    simp only [map_zero, add_zero]
    norm_num
    rw [gpPullback_id]
    exact one_nsmul _

/-- Composition with the exact divisor and rational-function formulas of 5.2(i). -/
def comp {source middle target : Object Phi}
    (first : Hom Phi data source middle)
    (second : Hom Phi data middle target) :
    Hom Phi data source target where
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree
  base := first.base ≫ second.base
  divisor :=
    Phi.pullback first.base second.divisor +
      second.frobeniusDegree.val • first.divisor
  rationalFunction :=
    data.rationalFunctions.pullback first.base second.rationalFunction +
      second.frobeniusDegree.val • first.rationalFunction
  balance := by
    change
      (first.frobeniusDegree.val * second.frobeniusDegree.val) •
            source.divisorClass +
          Algebra.GrothendieckAddGroup.of
            (Phi.pullback first.base second.divisor +
              second.frobeniusDegree.val • first.divisor) = _
    calc
      _ = gpPullback Phi first.base
              (Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              (first.frobeniusDegree.val • source.divisorClass +
                Algebra.GrothendieckAddGroup.of first.divisor) := by
          simp only [map_add, map_nsmul, gpPullback_of]
          rw [mul_nsmul, nsmul_add]
          abel
      _ = gpPullback Phi first.base
              (Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              (gpPullback Phi first.base middle.divisorClass +
                data.divisor source.base first.rationalFunction) := by
          rw [first.balance]
      _ = gpPullback Phi first.base
              (second.frobeniusDegree.val • middle.divisorClass +
                Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          simp only [map_add, map_nsmul, nsmul_add]
          abel
      _ = gpPullback Phi first.base
              (gpPullback Phi second.base target.divisorClass +
                data.divisor middle.base second.rationalFunction) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          rw [second.balance]
      _ = gpPullback Phi (first.base ≫ second.base) target.divisorClass +
            data.divisor source.base
              (data.rationalFunctions.pullback first.base
                second.rationalFunction) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          rw [map_add, gpPullback_comp, ← data.divisor_natural]
          rfl
      _ = gpPullback Phi (first.base ≫ second.base) target.divisorClass +
            data.divisor source.base
              (data.rationalFunctions.pullback first.base
                  second.rationalFunction +
                second.frobeniusDegree.val • first.rationalFunction) := by
          rw [map_add, map_nsmul, add_assoc]

end Hom

/-- The source category constructed in Frobenioids I, Theorem 5.2(i). -/
def Carrier
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi) :=
  let _sourceData := data
  Object Phi

instance carrierCategory
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi) :
    Category.{u} (Carrier Phi data) where
  Hom := Hom Phi data
  id := Hom.id Phi data
  comp := Hom.comp Phi data
  id_comp arrow := by
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · change
        Phi.pullback (𝟙 _) arrow.divisor +
            arrow.frobeniusDegree.val • 0 = arrow.divisor
      rw [Phi.pullback_id]
      simp
    · change
        data.rationalFunctions.pullback (𝟙 _) arrow.rationalFunction +
            arrow.frobeniusDegree.val • 0 = arrow.rationalFunction
      rw [data.rationalFunctions.pullback_id]
      simp
  comp_id arrow := by
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · change Phi.pullback arrow.base 0 + 1 • arrow.divisor = arrow.divisor
      rw [map_zero, zero_add, one_nsmul]
    · change
        data.rationalFunctions.pullback arrow.base 0 +
            1 • arrow.rationalFunction = arrow.rationalFunction
      rw [map_zero, zero_add, one_nsmul]
  assoc first second third := by
    ext
    · simp [Hom.comp, mul_assoc]
    · simp [Hom.comp, Category.assoc]
    · change
        Phi.pullback (first.base ≫ second.base) third.divisor +
            third.frobeniusDegree.val •
              (Phi.pullback first.base second.divisor +
                second.frobeniusDegree.val • first.divisor) =
          Phi.pullback first.base
              (Phi.pullback second.base third.divisor +
                third.frobeniusDegree.val • second.divisor) +
            (second.frobeniusDegree.val * third.frobeniusDegree.val) •
              first.divisor
      rw [Phi.pullback_comp]
      simp only [AddMonoidHom.comp_apply, map_add, map_nsmul,
        mul_nsmul, nsmul_add, add_assoc]
    · change
        data.rationalFunctions.pullback (first.base ≫ second.base)
              third.rationalFunction +
            third.frobeniusDegree.val •
              (data.rationalFunctions.pullback first.base second.rationalFunction +
                second.frobeniusDegree.val • first.rationalFunction) =
          data.rationalFunctions.pullback first.base
              (data.rationalFunctions.pullback second.base third.rationalFunction +
                third.frobeniusDegree.val • second.rationalFunction) +
            (second.frobeniusDegree.val * third.frobeniusDegree.val) •
              first.rationalFunction
      rw [data.rationalFunctions.pullback_comp]
      simp only [AddMonoidHom.comp_apply, map_add, map_nsmul,
        mul_nsmul, nsmul_add, add_assoc]

namespace Carrier

variable (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)

@[simp]
theorem comp_frobeniusDegree
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).frobeniusDegree =
      first.frobeniusDegree * second.frobeniusDegree :=
  rfl

@[simp]
theorem comp_base
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).base = first.base ≫ second.base :=
  rfl

@[simp]
theorem comp_divisor
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).divisor =
      Phi.pullback first.base second.divisor +
        second.frobeniusDegree.val • first.divisor :=
  rfl

@[simp]
theorem comp_rationalFunction
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).rationalFunction =
      data.rationalFunctions.pullback first.base second.rationalFunction +
        second.frobeniusDegree.val • first.rationalFunction :=
  rfl

/-- Projection of model objects to the base category. -/
def base : Carrier Phi data ⥤ D where
  obj object := Object.base object
  map arrow := arrow.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The structure functor to the elementary Frobenioid, forgetting `u_phi`. -/
def structureFunctor :
    @Functor (Carrier Phi data) (carrierCategory Phi data)
      (ElementaryFrobenioid D IsFSM Phi)
      (ElementaryFrobenioid.instCategory Phi) where
  obj object :=
    show ElementaryFrobenioid D IsFSM Phi from
      @Object.base D categoryD IsFSM Phi object
  map arrow :=
    { base := arrow.base
      divisor := arrow.divisor
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The model category with its literal pre-Frobenioid structure. -/
def preFrobenioid : PreFrobenioid (Carrier Phi data) D IsFSM where
  divisorMonoid := Phi
  structureFunctor := structureFunctor Phi data

end Carrier

end

end SourceModelFrobenioid

end Iut
