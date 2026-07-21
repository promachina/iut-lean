/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement

/-!
# Multiplicative Kummer faithfulness

Absolute Anabelian Topics III, Definition 1.5(a), characterizes the injectivity
of a multiplicative Kummer map by the absence of nontrivial elements divisible
by every positive integer.  This file proves the finite-quotient argument used
for profinite multiplicative groups.
-/

namespace Iut

namespace SourceKummerFaithfulness

universe u

/-- A residually finite group has no nontrivial element with roots of all degrees. -/
theorem eq_one_of_roots_of_residuallyFinite
    {G : Type u} [Group G] [_root_.Group.ResiduallyFinite G]
    (x : G)
    (roots : ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x) :
    x = 1 := by
  apply _root_.Group.eq_one_iff_forall_finiteIndexNormalSubroup x
  intro H
  let quotient := G ⧸ H.toSubgroup
  have quotientFinite : Finite quotient := inferInstance
  obtain ⟨root, hroot⟩ :=
    roots (Nat.card quotient) Nat.card_pos
  change x ∈ H.toSubgroup
  rw [← QuotientGroup.eq_one_iff]
  rw [← hroot, QuotientGroup.mk_pow]
  exact pow_card_eq_one'

/-- Every compact totally disconnected topological group is residually finite. -/
theorem residuallyFinite_of_profinite
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    _root_.Group.ResiduallyFinite G := by
  apply
    _root_.Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mpr
  intro x hx
  obtain ⟨H, hH⟩ :=
    _root_.ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isClosed_singleton.isOpen_compl : IsOpen ({x}ᶜ : Set G))
      (by simpa [eq_comm] using hx)
  exact
    ⟨H.toFiniteIndexNormalSubgroup,
      fun hmem => (hH hmem) rfl⟩

/-- Definition 1.5(a) holds for the multiplicative group of a profinite group. -/
theorem eq_one_of_roots_in_profinite
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (x : G)
    (roots : ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x) :
    x = 1 := by
  letI : _root_.Group.ResiduallyFinite G :=
    residuallyFinite_of_profinite
  exact eq_one_of_roots_of_residuallyFinite x roots

end SourceKummerFaithfulness

end Iut
