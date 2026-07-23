/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Tempered semi-graph source mathematics

This module starts the source-faithful reconstruction of the semi-graph results
used by IUT I, Proposition 2.4 and Corollary 2.5.  It formalizes the unique
geodesic rigidity in *Semi-graphs of Anabelioids*, Lemma 1.8(ii)(b), and the
subgroup-conjugation argument that derives the cuspidal portion of IUT I,
Corollary 2.5 from Proposition 2.4(i).

The maximal-compact/verticial classification of *Semi-graphs of Anabelioids*,
Theorem 3.7, and the inverse-limit passage in IUT I, Proposition 2.4(i), are not
asserted here.
-/

namespace Iut

universe u v

/-- An action on the vertices of a simple graph by graph automorphisms. -/
structure SourceGraphAction
    (Acting Vertex : Type*)
    [Group Acting]
    (graph : SimpleGraph Vertex) where
  action : Acting →* Equiv.Perm Vertex
  map_adj_iff :
    ∀ g first second,
      graph.Adj (action g first) (action g second) ↔
        graph.Adj first second

namespace SourceGraphAction

variable
  {Acting : Type u} {Vertex : Type v}
  [Group Acting]
  {graph : SimpleGraph Vertex}
  (data : SourceGraphAction Acting Vertex graph)

/-- The graph isomorphism induced by an acting element. -/
def graphIso (g : Acting) : graph ≃g graph where
  toEquiv := data.action g
  map_rel_iff' := by
    intro first second
    exact data.map_adj_iff g first second

@[simp]
theorem graphIso_apply (g : Acting) (vertex : Vertex) :
    graphIso data g vertex = data.action g vertex :=
  rfl

@[simp]
theorem graphIso_one_apply (vertex : Vertex) :
    graphIso data 1 vertex = vertex := by
  simp [graphIso]

@[simp]
theorem graphIso_inv_apply_apply (g : Acting) (vertex : Vertex) :
    graphIso data g⁻¹ (graphIso data g vertex) = vertex := by
  change data.action g⁻¹ (data.action g vertex) = vertex
  rw [map_inv]
  exact (data.action g).symm_apply_apply vertex

/-- A graph automorphism cannot increase graph distance. -/
theorem dist_image_le (g : Acting) (first second : Vertex) :
    graph.dist (graphIso data g first) (graphIso data g second) ≤
      graph.dist first second := by
  by_cases hreachable : graph.Reachable first second
  · obtain ⟨path, hpath⟩ :=
      hreachable.exists_walk_length_eq_dist
    calc
      graph.dist (graphIso data g first) (graphIso data g second) ≤
          (path.map (graphIso data g).toHom).length :=
        graph.dist_le _
      _ = path.length := SimpleGraph.Walk.length_map _ _
      _ = graph.dist first second := hpath
  · have himage_not_reachable :
        ¬ graph.Reachable
            (graphIso data g first) (graphIso data g second) := by
      intro himage
      obtain ⟨imagePath⟩ := himage
      apply hreachable
      exact
        ⟨(imagePath.map (graphIso data g⁻¹).toHom).copy
          (graphIso_inv_apply_apply data g first)
          (graphIso_inv_apply_apply data g second)⟩
    rw [graph.dist_eq_zero_of_not_reachable hreachable]
    rw [graph.dist_eq_zero_of_not_reachable himage_not_reachable]

/-- Graph automorphisms preserve graph distance exactly. -/
theorem dist_image (g : Acting) (first second : Vertex) :
    graph.dist (graphIso data g first) (graphIso data g second) =
      graph.dist first second := by
  apply le_antisymm (dist_image_le data g first second)
  have inverseBound :=
    dist_image_le data g⁻¹
      (graphIso data g first) (graphIso data g second)
  simpa using inverseBound

private theorem list_map_eq_self_fixed
    {α : Type*} {f : α → α} {values : List α}
    (hmap : values.map f = values) :
    ∀ value ∈ values, f value = value := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : f head = head := by
        simpa using congrArg List.head? hmap
      have htail : tail.map f = tail := by
        simpa using congrArg List.tail hmap
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact hhead
      · exact ih htail value hvalue

/-- If an automorphism fixes the endpoints of a path in a tree, it fixes every
vertex of that path.  This is the unique-geodesic argument of *Semi-graphs of
Anabelioids*, Lemma 1.8(ii)(b). -/
theorem fixes_path_pointwise
    (tree : graph.IsTree)
    (g : Acting)
    {first second : Vertex}
    (first_fixed : graphIso data g first = first)
    (second_fixed : graphIso data g second = second)
    (path : graph.Walk first second)
    (path_isPath : path.IsPath) :
    ∀ vertex ∈ path.support,
      graphIso data g vertex = vertex := by
  let mapped : graph.Walk first second :=
    (path.map (graphIso data g).toHom).copy
      first_fixed second_fixed
  have mapped_isPath : mapped.IsPath := by
    dsimp [mapped]
    rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective
      (graphIso data g).injective path_isPath
  have mapped_eq : mapped = path :=
    (tree.existsUnique_path first second).unique
      mapped_isPath path_isPath
  have support_eq :
      path.support.map (graphIso data g).toHom = path.support := by
    calc
      path.support.map (graphIso data g).toHom =
          (path.map (graphIso data g).toHom).support := by
        rw [SimpleGraph.Walk.support_map]
      _ = mapped.support := by
        simp [mapped]
      _ = path.support := congrArg SimpleGraph.Walk.support mapped_eq
  exact list_map_eq_self_fixed support_eq

/-- The action of a subgroup fixes the unique geodesic pointwise whenever it
fixes both endpoints. -/
theorem subgroup_fixes_geodesic_pointwise
    (tree : graph.IsTree)
    (subgroup : Subgroup Acting)
    {first second : Vertex}
    (first_fixed :
      ∀ g : subgroup, graphIso data g.1 first = first)
    (second_fixed :
      ∀ g : subgroup, graphIso data g.1 second = second) :
    ∃ path : graph.Walk first second,
      path.IsPath ∧
        ∀ g : subgroup, ∀ vertex ∈ path.support,
          graphIso data g.1 vertex = vertex := by
  obtain ⟨path, path_isPath, _⟩ :=
    tree.connected.exists_path_of_dist first second
  exact
    ⟨path, path_isPath, fun g =>
      fixes_path_pointwise data tree g.1
        (first_fixed g) (second_fixed g) path path_isPath⟩

end SourceGraphAction

open scoped Pointwise

/-- The exact subgroup configuration of IUT I, Proposition 2.4(i).

`geometricTempered = arithmeticTempered ⊓ geometric` records the geometric
kernel inside the arithmetic tempered group.  The final field is precisely the
compact-conjugate rigidity conclusion of Proposition 2.4(i), not Corollary 2.5. -/
structure SourceIUTIProposition24PartI
    (Ambient : Type u)
    [Group Ambient] [TopologicalSpace Ambient] where
  geometric : Subgroup Ambient
  arithmeticTempered : Subgroup Ambient
  geometricTempered : Subgroup Ambient
  geometric_normal : geometric.Normal
  geometricTempered_eq :
    geometricTempered = arithmeticTempered ⊓ geometric
  compactConjugateRigidity :
    ∀ (compact : Subgroup Ambient),
      compact ≤ geometricTempered →
      compact ≠ ⊥ →
      IsCompact (compact : Set Ambient) →
      ∀ conjugator : Ambient,
        MulAut.conj conjugator • compact ≤ geometricTempered →
        conjugator ∈ arithmeticTempered

namespace SourceIUTIProposition24PartI

variable
  {Ambient : Type u}
  [Group Ambient] [TopologicalSpace Ambient]
  (data : SourceIUTIProposition24PartI Ambient)

attribute [local instance] SourceIUTIProposition24PartI.geometric_normal

theorem geometricTempered_le_arithmeticTempered :
    data.geometricTempered ≤ data.arithmeticTempered := by
  rw [data.geometricTempered_eq]
  exact inf_le_left

theorem geometricTempered_le_geometric :
    data.geometricTempered ≤ data.geometric := by
  rw [data.geometricTempered_eq]
  exact inf_le_right

/-- A cusp inertia subgroup to which Proposition 2.4(i) applies. -/
structure CuspidalInertia where
  inertia : Subgroup Ambient
  inertia_le : inertia ≤ data.geometricTempered
  inertia_ne_bot : inertia ≠ ⊥
  inertia_isCompact : IsCompact (inertia : Set Ambient)

namespace CuspidalInertia

variable (cusp : data.CuspidalInertia)

/-- An ambient conjugate of cusp inertia lies in the arithmetic tempered group
exactly when its conjugator is tempered. -/
theorem conjugate_le_arithmeticTempered_iff
    (conjugator : Ambient) :
    MulAut.conj conjugator • cusp.inertia ≤
        data.arithmeticTempered ↔
      conjugator ∈ data.arithmeticTempered := by
  constructor
  · intro hconjugate
    apply data.compactConjugateRigidity cusp.inertia
      cusp.inertia_le cusp.inertia_ne_bot cusp.inertia_isCompact
      conjugator
    rw [data.geometricTempered_eq]
    refine le_inf hconjugate ?_
    calc
      MulAut.conj conjugator • cusp.inertia ≤
          MulAut.conj conjugator • data.geometric :=
        smul_le_smul_left (MulAut.conj conjugator)
          (cusp.inertia_le.trans
            data.geometricTempered_le_geometric)
      _ = data.geometric :=
        data.geometric_normal.conj_smul_eq_self conjugator
  · intro hconjugator
    exact Subgroup.conj_smul_le_of_le
      (cusp.inertia_le.trans
        data.geometricTempered_le_arithmeticTempered)
      ⟨conjugator, hconjugator⟩

/-- Thus every ambient conjugate contained in the tempered group is already a
conjugate by an element of the tempered group. -/
theorem conjugate_classification
    (conjugator : Ambient) :
    MulAut.conj conjugator • cusp.inertia ≤
        data.arithmeticTempered ↔
      ∃ temperedConjugator : data.arithmeticTempered,
        MulAut.conj conjugator • cusp.inertia =
          MulAut.conj temperedConjugator.1 • cusp.inertia := by
  constructor
  · intro h
    exact
      ⟨⟨conjugator,
          (conjugate_le_arithmeticTempered_iff
            data cusp conjugator).mp h⟩,
        rfl⟩
  · rintro ⟨temperedConjugator, heq⟩
    rw [heq]
    exact
      (conjugate_le_arithmeticTempered_iff
        data cusp temperedConjugator.1).mpr temperedConjugator.2

/-- A conjugate of the arithmetic tempered group contains cusp inertia if and
only if it is the original tempered group.  This is the second cuspidal claim
of IUT I, Corollary 2.5. -/
theorem inertia_le_conjugate_arithmeticTempered_iff
    (conjugator : Ambient) :
    cusp.inertia ≤
        MulAut.conj conjugator • data.arithmeticTempered ↔
      MulAut.conj conjugator • data.arithmeticTempered =
        data.arithmeticTempered := by
  constructor
  · intro hinertia
    have hinverse :
        MulAut.conj conjugator⁻¹ • cusp.inertia ≤
          data.arithmeticTempered :=
      by
        simpa using
          (Subgroup.subset_pointwise_smul_iff.mp hinertia)
    have hinverse_mem :
        conjugator⁻¹ ∈ data.arithmeticTempered :=
      (conjugate_le_arithmeticTempered_iff
        data cusp conjugator⁻¹).mp hinverse
    exact Subgroup.conj_smul_eq_self_of_mem
      (by
        simpa using
          data.arithmeticTempered.inv_mem hinverse_mem)
  · intro heq
    rw [heq]
    exact
      cusp.inertia_le.trans
        data.geometricTempered_le_arithmeticTempered

end CuspidalInertia

end SourceIUTIProposition24PartI

end Iut
