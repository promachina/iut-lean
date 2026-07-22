import Iut.Foundations.KummerFaithfulness
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Multiplicative Kummer faithfulness for mixed-characteristic local fields

This file formalizes the multiplicative case of Absolute Anabelian Geometry
III, Definition 1.5 and Remark 1.5.4(i).  It is kept separate from the
construction of the Kummer maps so that the arithmetic argument cannot be
replaced by a field stored in a presentation structure.
-/

namespace Iut

namespace SourceMLFKummerFaithfulness

universe u

open ValuativeRel

set_option maxHeartbeats 800000 in
-- The quotient-module finiteness synthesis traverses the scalar tower.
/-- A finite algebra modulo an extended finite-index ideal is finite. -/
theorem finite_quotient_map
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  let B := R ⧸ J.comap (algebraMap R S)
  let T := S ⧸ J
  let factor : R ⧸ I →+* B :=
    Ideal.Quotient.factor Ideal.le_comap_map
  letI : Finite B :=
    Finite.of_surjective factor
      (Ideal.Quotient.factor_surjective _)
  letI : Algebra B T := inferInstance
  letI : IsScalarTower R B T :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
  letI : Module.Finite R T := Module.Finite.quotient R J
  letI : Module.Finite B T :=
    Module.Finite.of_restrictScalars_finite R B T
  exact Module.finite_of_finite B

set_option maxHeartbeats 800000 in
-- Krull intersection and the quotient construction require deep synthesis.
/--
Finite quotients modulo powers of one proper ideal make the units of a finite
algebra residually finite.  Krull intersection supplies the separating power.
-/
theorem units_residuallyFinite_of_finite_quotients
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤)
    (finiteQuotient : ∀ n : ℕ, Finite (R ⧸ I ^ n)) :
    _root_.Group.ResiduallyFinite Sˣ := by
  apply _root_.Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro unit unit_ne_one
  have value_sub_one_ne_zero : (unit : S) - 1 ≠ 0 := by
    intro equality
    apply unit_ne_one
    apply Units.ext
    exact sub_eq_zero.mp equality
  have exists_separating_power :
      ∃ n : ℕ,
        (unit : S) - 1 ∉
          (I ^ n • (⊤ : Submodule R S)) := by
    by_contra no_power
    push Not at no_power
    have in_intersection :
        (unit : S) - 1 ∈
          (⨅ n : ℕ, I ^ n • (⊤ : Submodule R S)) :=
      (Submodule.mem_iInf _).mpr no_power
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI]
      at in_intersection
    exact value_sub_one_ne_zero
      ((Submodule.mem_bot R).mp in_intersection)
  obtain ⟨n, separating⟩ := exists_separating_power
  let J : Ideal S := (I ^ n).map (algebraMap R S)
  have separating_ideal : (unit : S) - 1 ∉ J := by
    intro member
    apply separating
    rw [Ideal.smul_top_eq_map]
    exact member
  letI : Finite (R ⧸ I ^ n) := finiteQuotient n
  letI : Finite (S ⧸ J) := finite_quotient_map R S (I ^ n)
  let reduction : Sˣ →* (S ⧸ J)ˣ :=
    Units.map (Ideal.Quotient.mk J)
  refine ⟨(S ⧸ J)ˣ, inferInstance, inferInstance, reduction, ?_⟩
  intro reduction_eq_one
  apply separating_ideal
  apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (unit : S)).mp
  exact congrArg Units.val reduction_eq_one

variable
  (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The unit group of the valuation ring of an MLF is profinite. -/
noncomputable def valuationRingUnitsProfinite : Profinite :=
  by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valued K (ValueGroupWithZero K) := inferInstance
    letI : (Valued.v (R := K)).RankOne :=
      { hom' :=
          IsRankLeOne.nonempty.some.emb (R := K).comp
            MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' :=
          IsRankLeOne.nonempty.some.strictMono.comp
            MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let R := Valuation.integer (valuation K)
    open scoped Valued in
      letI : NontriviallyNormedField K := inferInstance
      letI : IsUltrametricDist K := inferInstance
      letI : TotallyDisconnectedSpace K := inferInstance
      letI : T1Space R := inferInstance
      letI : TotallyDisconnectedSpace R := inferInstance
      letI : TotallyDisconnectedSpace Rᵐᵒᵖ :=
        MulOpposite.opHomeomorph.totallyDisconnectedSpace
      letI : TotallyDisconnectedSpace Rˣ :=
        (Units.isEmbedding_embedProduct.isTotallyDisconnected_range).mp
          (isTotallyDisconnected_of_totallyDisconnectedSpace _)
      exact Profinite.of Rˣ

/-- An MLF unit admitting roots of every positive degree is trivial. -/
theorem valuationRingUnit_eq_one_of_roots
    (value : (Valuation.integer (valuation K))ˣ)
    (roots : ∀ n : ℕ, 0 < n →
      ∃ root : (Valuation.integer (valuation K))ˣ,
        root ^ n = value) :
    value = 1 := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valued K (ValueGroupWithZero K) := inferInstance
  letI : (Valued.v (R := K)).RankOne :=
    { hom' :=
        IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' :=
        IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let R := Valuation.integer (valuation K)
  open scoped Valued in
    letI : NontriviallyNormedField K := inferInstance
    letI : IsUltrametricDist K := inferInstance
    letI : TotallyDisconnectedSpace K := inferInstance
    letI : T1Space R := inferInstance
    letI : TotallyDisconnectedSpace R := inferInstance
    letI : TotallyDisconnectedSpace Rᵐᵒᵖ :=
      MulOpposite.opHomeomorph.totallyDisconnectedSpace
    letI : TotallyDisconnectedSpace Rˣ :=
      (Units.isEmbedding_embedProduct.isTotallyDisconnected_range).mp
        (isTotallyDisconnected_of_totallyDisconnectedSpace _)
    exact
      SourceKummerFaithfulness.eq_one_of_roots_in_profinite value roots

set_option maxHeartbeats 800000 in
-- Integral-closure finiteness and DVR quotient instances synthesize together.
/--
The integral units in every finite extension of an MLF are residually finite.
This is the finite-base-change clause required by Definition 1.5(a).
-/
theorem integralClosureUnits_residuallyFinite
    [CharZero K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] :
    _root_.Group.ResiduallyFinite
      (integralClosure
        (Valuation.integer (valuation K)) L)ˣ := by
  let R := Valuation.integer (valuation K)
  let S := integralClosure R L
  letI : IsFractionRing R K := inferInstance
  letI : Module.Finite R S :=
    IsIntegralClosure.finite R K L S
  apply units_residuallyFinite_of_finite_quotients
    R S (IsLocalRing.maximalIdeal R)
  · exact Ideal.IsPrime.ne_top'
  · intro n
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valued K (ValueGroupWithZero K) := inferInstance
    letI : IsDiscreteValuationRing (Valued.integer K) := by
      change IsDiscreteValuationRing R
      infer_instance
    letI : Finite (Valued.ResidueField K) := by
      change Finite (IsLocalRing.ResidueField R)
      infer_instance
    exact
      Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField
        (K := K) inferInstance n

end SourceMLFKummerFaithfulness

end Iut
