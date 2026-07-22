/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceSplitKummerFrobenioid
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Archimedean torsion-quotient system from IUT II Definition 4.9(v)

IUT II, Definition 4.9(v), replaces the archimedean split Frobenioid by an
inductive system indexed by a multiplicatively cofinal subset of `N >= 1`.
On units, the system consists of the circle quotients by `N`-torsion, with
compatible surjections from the original compact factor and an indeterminacy
given by inversion.

This file constructs that unit-level system as an actual functor of topological
groups. It includes its quotient topology, exact kernels, continuous transition
maps, arbitrary cofinal restrictions, and the two compatible orientations. It
does not yet construct the corresponding system of split Frobenioids or prove
the source's identification between the colimits of distinct cofinal subsets.
-/

namespace Iut

open CategoryTheory

namespace SourceArchimedeanKummerSystem

noncomputable section

/-- The units of the `N`-torsion quotient at an archimedean place. -/
abbrev UnitQuotient (N : ℕ+) :=
  Circle ⧸ (powMonoidHom (α := Circle) N.val).ker

/-- The `N`-torsion subgroup is closed in the circle. -/
theorem rootsOfUnity_isClosed (N : ℕ+) :
    IsClosed (((powMonoidHom (α := Circle) N.val).ker : Subgroup Circle) : Set Circle) := by
  change IsClosed {unit : Circle | unit ^ N.val = 1}
  exact isClosed_eq (continuous_id.pow N.val) continuous_const

instance (N : ℕ+) :
    IsClosed (((powMonoidHom (α := Circle) N.val).ker : Subgroup Circle) : Set Circle) :=
  rootsOfUnity_isClosed N

/-- The canonical surjection from the compact factor to its `N`-torsion quotient. -/
def quotientMap (N : ℕ+) : Circle →* UnitQuotient N :=
  QuotientGroup.mk' (powMonoidHom (α := Circle) N.val).ker

/-- The quotient map with its source topological-group structure retained. -/
def continuousQuotientMap (N : ℕ+) : Circle →ₜ* UnitQuotient N where
  toMonoidHom := quotientMap N
  continuous_toFun := QuotientGroup.continuous_mk

/-- The canonical map realizes the quotient topology, not only the group quotient. -/
theorem continuousQuotientMap_isOpenQuotientMap (N : ℕ+) :
    IsOpenQuotientMap (continuousQuotientMap N) :=
  QuotientGroup.isOpenQuotientMap_mk

theorem quotientMap_surjective (N : ℕ+) :
    Function.Surjective (quotientMap N) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the canonical surjection is exactly the `N`-torsion. -/
theorem quotientMap_ker (N : ℕ+) :
    (quotientMap N).ker = (powMonoidHom (α := Circle) N.val).ker :=
  QuotientGroup.ker_mk' _

/-- `mu_N` is contained in `mu_M` whenever `N` divides `M`. -/
theorem rootsOfUnity_le_of_dvd
    (N M : ℕ+) (hNM : N ∣ M) :
    (powMonoidHom (α := Circle) N.val).ker ≤
      (powMonoidHom (α := Circle) M.val).ker := by
  rcases hNM with ⟨K, rfl⟩
  intro unit hunit
  change unit ^ N.val = 1 at hunit
  change unit ^ (N.val * K.val) = 1
  rw [pow_mul, hunit, one_pow]

/-- The transition `O^(times-mu_N) → O^(times-mu_M)` for `N ∣ M`. -/
def transition (N M : ℕ+) (hNM : N ∣ M) :
    UnitQuotient N →* UnitQuotient M :=
  QuotientGroup.map
    (powMonoidHom (α := Circle) N.val).ker
    (powMonoidHom (α := Circle) M.val).ker
    (MonoidHom.id Circle)
    (by simpa using rootsOfUnity_le_of_dvd N M hNM)

/-- The transition is a continuous homomorphism of quotient topological groups. -/
def continuousTransition (N M : ℕ+) (hNM : N ∣ M) :
    UnitQuotient N →ₜ* UnitQuotient M where
  toMonoidHom := transition N M hNM
  continuous_toFun := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk
      (N := (powMonoidHom (α := Circle) N.val).ker)).continuous_comp_iff]
    exact QuotientGroup.continuous_mk

@[simp]
theorem continuousTransition_mk
    (N M : ℕ+) (hNM : N ∣ M) (unit : Circle) :
    continuousTransition N M hNM (continuousQuotientMap N unit) =
      continuousQuotientMap M unit :=
  rfl

@[simp]
theorem transition_mk
    (N M : ℕ+) (hNM : N ∣ M) (unit : Circle) :
    transition N M hNM (quotientMap N unit) = quotientMap M unit :=
  rfl

/-- Every transition in the archimedean system is surjective. -/
theorem transition_surjective (N M : ℕ+) (hNM : N ∣ M) :
    Function.Surjective (transition N M hNM) := by
  intro value
  induction value using QuotientGroup.induction_on with
  | _ unit =>
      exact ⟨quotientMap N unit, transition_mk N M hNM unit⟩

/-- The transition kernel is the image of `mu_M` modulo `mu_N`. -/
theorem transition_ker (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).ker =
      Subgroup.map (quotientMap N)
        (powMonoidHom (α := Circle) M.val).ker := by
  simpa [transition, quotientMap] using
    QuotientGroup.ker_map
      (N := (powMonoidHom (α := Circle) N.val).ker)
      (M := (powMonoidHom (α := Circle) M.val).ker)
      (MonoidHom.id Circle)
      (by simpa using rootsOfUnity_le_of_dvd N M hNM)

/-- The quotient surjections commute with every transition. -/
theorem transition_comp_quotientMap
    (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).comp (quotientMap N) = quotientMap M := by
  ext unit
  rfl

/-- Transitions compose as an inductive system over divisibility. -/
theorem transition_comp
    (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L) :
    (transition M L hML).comp (transition N M hNM) =
      transition N L (dvd_trans hNM hML) := by
  ext unit
  rfl

/-- The transition from an index to itself is the identity map. -/
theorem transition_self (N : ℕ+) :
    transition N N (dvd_refl N) = MonoidHom.id (UnitQuotient N) := by
  ext unit
  rfl

/-- Continuous transitions compose as the same divisibility-indexed system. -/
theorem continuousTransition_comp
    (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L) :
    (continuousTransition M L hML).comp (continuousTransition N M hNM) =
      continuousTransition N L (dvd_trans hNM hML) := by
  apply _root_.ContinuousMonoidHom.ext
  intro unit
  exact DFunLike.congr_fun (transition_comp N M L hNM hML) unit

/-- The continuous self-transition is the identity. -/
theorem continuousTransition_self (N : ℕ+) :
    continuousTransition N N (dvd_refl N) =
      _root_.ContinuousMonoidHom.id (UnitQuotient N) := by
  apply _root_.ContinuousMonoidHom.ext
  intro unit
  exact DFunLike.congr_fun (transition_self N) unit

/-- The two orientation choices allowed for the compact archimedean factor. -/
inductive Orientation
  | direct
  | conjugate
  deriving DecidableEq

/-- Direct orientation or the designated continuous reversal `z ↦ z⁻¹`. -/
def orientationAutomorphism : Orientation → (Circle ≃ₜ* Circle)
  | .direct => ContinuousMulEquiv.refl Circle
  | .conjugate =>
      { MulEquiv.inv Circle with
        continuous_toFun := continuous_inv
        continuous_invFun := continuous_inv }

/-- The compatible quotient-surjection system after one orientation choice. -/
def orientedQuotientMap (orientation : Orientation) (N : ℕ+) :
    Circle →* UnitQuotient N :=
  (quotientMap N).comp
    (orientationAutomorphism orientation).toMulEquiv.toMonoidHom

/-- The oriented quotient map as a continuous homomorphism. -/
def continuousOrientedQuotientMap
    (orientation : Orientation) (N : ℕ+) :
    Circle →ₜ* UnitQuotient N :=
  (continuousQuotientMap N).comp
    (orientationAutomorphism orientation : Circle →ₜ* Circle)

/-- Every oriented map is an open quotient map, hence a topological surjection. -/
theorem continuousOrientedQuotientMap_isOpenQuotientMap
    (orientation : Orientation) (N : ℕ+) :
    IsOpenQuotientMap (continuousOrientedQuotientMap orientation N) :=
  (continuousQuotientMap_isOpenQuotientMap N).comp
    (orientationAutomorphism orientation).toHomeomorph.isOpenQuotientMap

/-- Every oriented map has kernel exactly `mu_N`. -/
theorem orientedQuotientMap_ker
    (orientation : Orientation) (N : ℕ+) :
    (orientedQuotientMap orientation N).ker =
      (powMonoidHom (α := Circle) N.val).ker := by
  ext unit
  change
    (((orientationAutomorphism orientation unit : Circle) : UnitQuotient N) = 1) ↔
      unit ^ N.val = 1
  rw [QuotientGroup.eq_one_iff]
  cases orientation with
  | direct => rfl
  | conjugate =>
      change unit⁻¹ ^ N.val = 1 ↔ unit ^ N.val = 1
      rw [inv_pow, inv_eq_one]

/-- The orientation choice is compatible across the entire inductive system. -/
theorem transition_comp_orientedQuotientMap
    (orientation : Orientation) (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).comp (orientedQuotientMap orientation N) =
      orientedQuotientMap orientation M := by
  ext unit
  rfl

/-- The continuously oriented quotient maps commute with every transition. -/
theorem continuousTransition_comp_orientedQuotientMap
    (orientation : Orientation) (N M : ℕ+) (hNM : N ∣ M) :
    (continuousTransition N M hNM).comp
        (continuousOrientedQuotientMap orientation N) =
      continuousOrientedQuotientMap orientation M := by
  ext unit
  rfl

/-- The designated reversal is genuinely nontrivial. -/
theorem orientationAutomorphism_ne
    : orientationAutomorphism .direct ≠ orientationAutomorphism .conjugate := by
  intro equality
  have h := DFunLike.congr_fun equality (Circle.exp (Real.pi / 2))
  change Circle.exp (Real.pi / 2) = (Circle.exp (Real.pi / 2))⁻¹ at h
  have hcoe := congrArg (fun value : Circle => (value : ℂ)) h
  simp only [Circle.coe_exp, Circle.coe_inv] at hcoe
  rw [Complex.ofReal_div] at hcoe
  norm_num at hcoe
  have him := congrArg Complex.im hcoe
  norm_num at him

/-- Positive integers ordered by divisibility, the source indexing category. -/
structure DivisibilityIndex where
  value : ℕ+
  deriving DecidableEq

instance : Preorder DivisibilityIndex where
  le first second := first.value ∣ second.value
  le_refl index := dvd_refl index.value
  le_trans _ _ _ := dvd_trans

@[simp]
theorem divisibilityIndex_le_iff (first second : DivisibilityIndex) :
    first ≤ second ↔ first.value ∣ second.value :=
  Iff.rfl

/-- A subset cofinal for divisibility in the multiplicative monoid of positive integers. -/
structure MultiplicativelyCofinalSubset where
  carrier : Set ℕ+
  cofinal : ∀ N : ℕ+, ∃ M : ℕ+, M ∈ carrier ∧ N ∣ M

namespace MultiplicativelyCofinalSubset

/-- The divisibility index category cut out by a cofinal subset. -/
abbrev Index (subset : MultiplicativelyCofinalSubset) :=
  { index : DivisibilityIndex // index.value ∈ subset.carrier }

/-- Inclusion of a cofinal indexing category into all positive integers. -/
def indexInclusion (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ DivisibilityIndex :=
  (show Monotone (Subtype.val : subset.Index → DivisibilityIndex) from
    fun _ _ hle => hle).functor

/-- Every positive integer is dominated by an index in a cofinal subset. -/
theorem exists_index_above
    (subset : MultiplicativelyCofinalSubset) (N : DivisibilityIndex) :
    ∃ M : subset.Index, N ≤ M.1 := by
  obtain ⟨M, hM, hNM⟩ := subset.cofinal N.value
  exact ⟨⟨⟨M⟩, hM⟩, hNM⟩

/-- The full positive-integer indexing set is multiplicatively cofinal. -/
def all : MultiplicativelyCofinalSubset where
  carrier := Set.univ
  cofinal N := ⟨N, Set.mem_univ N, dvd_refl N⟩

end MultiplicativelyCofinalSubset

/-- A quotient unit group as an actual topological-group object. -/
def unitQuotientObject (N : ℕ+) : TopologicalGroupCat.{0} where
  toFundamentalGroup :=
    { carrier := UnitQuotient N
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The compact archimedean factor as a topological-group object. -/
def circleObject : TopologicalGroupCat.{0} where
  toFundamentalGroup :=
    { carrier := Circle
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The actual divisibility-indexed inductive system of topological unit quotients. -/
def unitQuotientDiagram : DivisibilityIndex ⥤ TopologicalGroupCat.{0} where
  obj index := unitQuotientObject index.value
  map {first second} arrow :=
    continuousTransition first.value second.value arrow.le
  map_id index := by
    change continuousTransition index.value index.value (dvd_refl index.value) =
      _root_.ContinuousMonoidHom.id (UnitQuotient index.value)
    exact continuousTransition_self index.value
  map_comp first second := by
    change
      continuousTransition _ _ (dvd_trans first.le second.le) =
        (continuousTransition _ _ second.le).comp
          (continuousTransition _ _ first.le)
    exact (continuousTransition_comp _ _ _ first.le second.le).symm

/-- Each orientation gives one compatible system of quotient surjections. -/
def orientedQuotientNaturalTransformation (orientation : Orientation) :
    (Functor.const DivisibilityIndex).obj circleObject ⟶ unitQuotientDiagram where
  app index := continuousOrientedQuotientMap orientation index.value
  naturality {first second} arrow := by
    apply _root_.ContinuousMonoidHom.ext
    intro unit
    rfl

/-- Restriction of the unit system to any multiplicatively cofinal subset. -/
def restrictedUnitQuotientDiagram
    (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ TopologicalGroupCat.{0} :=
  subset.indexInclusion ⋙ unitQuotientDiagram

/-- The compatible oriented surjections on an arbitrary cofinal subsystem. -/
def restrictedOrientedQuotientNaturalTransformation
    (subset : MultiplicativelyCofinalSubset) (orientation : Orientation) :
    (Functor.const subset.Index).obj circleObject ⟶
      restrictedUnitQuotientDiagram subset where
  app index := continuousOrientedQuotientMap orientation index.1.value
  naturality {first second} arrow := by
    apply _root_.ContinuousMonoidHom.ext
    intro unit
    rfl

end

end SourceArchimedeanKummerSystem

end Iut
