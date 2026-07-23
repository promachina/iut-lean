/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Iut.Foundations.SourceSemiGraphOfSubgroups

/-!
# Profinite systems of constituent cosets

This module formalizes the normal-open-subgroup construction in
*Semi-graphs of Anabelioids*, Remark 2.2.1.  For a subgroup `H` of a profinite
group `G`, the finite level attached to an open normal subgroup `N` is the
coset space `G / (H sup N)`.  These levels form a cofiltered finite action
system.  A coset modulo `H` determines a compatible system, and closedness of
`H` proves both injectivity and the exact stabilizer formula.
-/

namespace Iut

universe u

open CategoryTheory CategoryTheory.FunctorToTypes QuotientGroup

namespace SourceProfiniteCosetSystem

variable {Ambient : Type u} [Group Ambient] [TopologicalSpace Ambient]
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [TotallyDisconnectedSpace Ambient]

/-- The finite-level constituent subgroup obtained from `H` and the open
normal subgroup `N`. -/
def levelSubgroup (H : Subgroup Ambient) (N : OpenNormalSubgroup Ambient) :
    Subgroup Ambient :=
  H ⊔ N.toSubgroup

omit [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [TotallyDisconnectedSpace Ambient] in
theorem levelSubgroup_mono (H : Subgroup Ambient)
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M) :
    levelSubgroup H N ≤ levelSubgroup H M :=
  sup_le_sup le_rfl map.le

/-- The functor of finite coset spaces `G / (H sup N)` over all open normal
subgroups `N` of `G`. -/
def carrier (H : Subgroup Ambient) :
    OpenNormalSubgroup Ambient ⥤ Type u where
  obj N := Ambient ⧸ levelSubgroup H N
  map map := ↾(Subgroup.quotientMapOfLE (levelSubgroup_mono H map))
  map_id N := by
    ext coset
    induction coset using Quotient.inductionOn'
    rfl
  map_comp first second := by
    ext coset
    induction coset using Quotient.inductionOn'
    rfl

/-- Left multiplication by the ambient group on one finite coset level. -/
def levelAction (H : Subgroup Ambient) (N : OpenNormalSubgroup Ambient) :
    Ambient →* Equiv.Perm ((carrier H).obj N) :=
  @MulAction.toPermHom Ambient ((carrier H).obj N) _ (by
    change MulAction Ambient (Ambient ⧸ levelSubgroup H N)
    infer_instance)

omit [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [TotallyDisconnectedSpace Ambient] in
theorem transition_equivariant (H : Subgroup Ambient)
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M)
    (g : Ambient) (coset : (carrier H).obj N) :
    (carrier H).map map (levelAction H N g coset) =
      levelAction H M g ((carrier H).map map coset) := by
  induction coset using Quotient.inductionOn'
  change QuotientGroup.mk (g * _) = QuotientGroup.mk (g * _)
  rfl

omit [TotallyDisconnectedSpace Ambient] in
/-- Each constituent coset level is finite because it is a quotient of the
finite quotient `G / N`. -/
theorem finite_level (H : Subgroup Ambient) (N : OpenNormalSubgroup Ambient) :
    Finite ((carrier H).obj N) := by
  letI : N.toSubgroup.FiniteIndex :=
    N.finiteIndex_of_finite_quotient
  letI : (levelSubgroup H N).FiniteIndex :=
    Subgroup.finiteIndex_of_le
      (H := N.toSubgroup) (K := levelSubgroup H N) le_sup_right
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The cofiltered finite action system of constituent cosets. -/
def system (H : Subgroup Ambient) :
    SourceCofilteredFiniteActionSystem
      (OpenNormalSubgroup Ambient) Ambient where
  carrier := carrier H
  action := levelAction H
  transition_equivariant := transition_equivariant H
  finite_level := finite_level H

/-- A coset modulo `H` gives its compatible family of images modulo
`H sup N`. -/
def cosetSection (H : Subgroup Ambient) (coset : Ambient ⧸ H) :
    (carrier H).sections where
  val N := Subgroup.quotientMapOfLE le_sup_left coset
  property := by
    intro N M map
    induction coset using Quotient.inductionOn'
    rfl

omit [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [TotallyDisconnectedSpace Ambient] in
@[simp]
theorem cosetSection_apply_mk (H : Subgroup Ambient) (g : Ambient)
    (N : OpenNormalSubgroup Ambient) :
    (cosetSection H (QuotientGroup.mk g)).1 N = QuotientGroup.mk g :=
  rfl

/-- The compatible system associated to the identity coset. -/
def baseSection (H : Subgroup Ambient) : (carrier H).sections :=
  cosetSection H (QuotientGroup.mk 1)

omit [TotallyDisconnectedSpace Ambient] in
/-- Passage from an `H`-coset to its compatible finite-level system is
equivariant for the ambient left action. -/
theorem cosetSection_smul (H : Subgroup Ambient) (g : Ambient)
    (coset : Ambient ⧸ H) :
    cosetSection H (g • coset) =
      (system H).actSection g (cosetSection H coset) := by
  apply CategoryTheory.Functor.sections_ext_iff.mpr
  intro N
  induction coset using Quotient.inductionOn'
  rfl

omit [TotallyDisconnectedSpace Ambient] in
/-- At level `N`, the stabilizer of the identity constituent coset is exactly
`H sup N`. -/
theorem coordinateStabilizer_baseSection_eq (H : Subgroup Ambient)
    (N : OpenNormalSubgroup Ambient) :
    (system H).coordinateStabilizer (baseSection H) N =
      levelSubgroup H N := by
  change MulAction.stabilizer Ambient
      ((1 : Ambient) : Ambient ⧸ levelSubgroup H N) = levelSubgroup H N
  exact MulAction.stabilizer_quotient (levelSubgroup H N)

/-- A closed subgroup of a profinite group is recovered by intersecting the
subgroups `H sup N` over all open normal `N`. -/
theorem iInf_levelSubgroup_eq (H : Subgroup Ambient)
    (closed : IsClosed (H : Set Ambient)) :
    (⨅ N : OpenNormalSubgroup Ambient, levelSubgroup H N) = H := by
  apply le_antisymm
  · let closedH : ClosedSubgroup Ambient :=
      { H with isClosed' := closed }
    change (⨅ N : OpenNormalSubgroup Ambient,
      levelSubgroup H N) ≤ closedH.toSubgroup
    rw [ProfiniteGrp.closedSubgroup_eq_sInf_open closedH]
    apply le_sInf
    intro K hK
    obtain ⟨N, hN⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        hK.1 K.one_mem
    exact (iInf_le (fun N : OpenNormalSubgroup Ambient =>
      levelSubgroup H N) N).trans (sup_le hK.2 hN)
  · exact le_iInf fun N => le_sup_left

/-- Closedness separates distinct `H`-cosets in a finite constituent level. -/
theorem cosetSection_injective (H : Subgroup Ambient)
    (closed : IsClosed (H : Set Ambient)) :
    Function.Injective (cosetSection H) := by
  refine Quotient.ind₂' ?_
  intro first second equality
  apply QuotientGroup.eq.mpr
  rw [← iInf_levelSubgroup_eq H closed]
  rw [Subgroup.mem_iInf]
  intro N
  have coordinateEquality :=
    congrArg (fun compatible : (carrier H).sections => compatible.1 N)
      equality
  exact QuotientGroup.eq.mp coordinateEquality

/-- The stabilizer of the identity compatible system is the original closed
constituent subgroup. -/
theorem sectionStabilizer_baseSection_eq (H : Subgroup Ambient)
    (closed : IsClosed (H : Set Ambient)) :
    (system H).sectionStabilizer (baseSection H) = H := by
  calc
    (system H).sectionStabilizer (baseSection H) =
        ⨅ N, (system H).coordinateStabilizer (baseSection H) N :=
      (system H).sectionStabilizer_eq_iInf_coordinateStabilizer
        (baseSection H)
    _ = ⨅ N, levelSubgroup H N := by
      congr 1
      funext N
      exact coordinateStabilizer_baseSection_eq H N
    _ = H := iInf_levelSubgroup_eq H closed

/-- Every constituent coset gives a compatible system whose stabilizer is the
corresponding conjugate of the closed constituent subgroup. -/
theorem sectionStabilizer_cosetSection_eq_conjugate
    (H : Subgroup Ambient) (closed : IsClosed (H : Set Ambient))
    (coset : Ambient ⧸ H) :
    (system H).sectionStabilizer (cosetSection H coset) =
      H.map (MulAut.conj coset.out).toMonoidHom := by
  letI : MulAction Ambient (carrier H).sections :=
    (system H).sectionMulAction
  have coset_eq : coset = coset.out • ((1 : Ambient) : Ambient ⧸ H) := by
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      coset.out_eq'.symm
  have section_eq :
      cosetSection H coset =
        (system H).actSection coset.out (baseSection H) := by
    calc
      cosetSection H coset =
          cosetSection H
            (coset.out • ((1 : Ambient) : Ambient ⧸ H)) :=
        congrArg (cosetSection H) coset_eq
      _ = (system H).actSection coset.out
          (cosetSection H ((1 : Ambient) : Ambient ⧸ H)) :=
        cosetSection_smul H coset.out _
      _ = (system H).actSection coset.out (baseSection H) := rfl
  rw [section_eq]
  change MulAction.stabilizer Ambient
      (coset.out • baseSection H) = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have baseStabilizer :
      MulAction.stabilizer Ambient (baseSection H) = H :=
    sectionStabilizer_baseSection_eq H closed
  rw [baseStabilizer]

end SourceProfiniteCosetSystem

namespace SourceSemiGraphSubgroupDiagram

variable {Ambient : Type u} [Group Ambient] [TopologicalSpace Ambient]
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [TotallyDisconnectedSpace Ambient]
    (diagram : SourceSemiGraphSubgroupDiagram.{u} Ambient)

/-- The compatible normal-open coset system represented by a lifted vertex. -/
def profiniteVertexSection (point : diagram.CosetVertex) :
    (SourceProfiniteCosetSystem.carrier
      (diagram.vertexGroup point.1)).sections :=
  SourceProfiniteCosetSystem.cosetSection
    (diagram.vertexGroup point.1) point.2

/-- The compatible normal-open coset system represented by a lifted edge. -/
def profiniteEdgeSection (point : diagram.CosetEdge) :
    (SourceProfiniteCosetSystem.carrier
      (diagram.edgeGroup point.1)).sections :=
  SourceProfiniteCosetSystem.cosetSection
    (diagram.edgeGroup point.1) point.2

/-- Closed verticial subgroups separate distinct lifted vertices over a fixed
base vertex at a finite normal-open level. -/
theorem profiniteVertexSection_injective (vertex : diagram.base.Vertex)
    (closed : IsClosed (diagram.vertexGroup vertex : Set Ambient)) :
    Function.Injective (fun coset : Ambient ⧸ diagram.vertexGroup vertex =>
      show (SourceProfiniteCosetSystem.carrier
        (diagram.vertexGroup vertex)).sections from
        diagram.profiniteVertexSection
          (⟨vertex, coset⟩ : diagram.CosetVertex)) := by
  change Function.Injective
    (SourceProfiniteCosetSystem.cosetSection
      (diagram.vertexGroup vertex))
  exact SourceProfiniteCosetSystem.cosetSection_injective
    (diagram.vertexGroup vertex) closed

/-- Closed edge subgroups separate distinct lifted edges over a fixed base
edge at a finite normal-open level. -/
theorem profiniteEdgeSection_injective (edge : diagram.base.Edge)
    (closed : IsClosed (diagram.edgeGroup edge : Set Ambient)) :
    Function.Injective (fun coset : Ambient ⧸ diagram.edgeGroup edge =>
      show (SourceProfiniteCosetSystem.carrier
        (diagram.edgeGroup edge)).sections from
        diagram.profiniteEdgeSection
          (⟨edge, coset⟩ : diagram.CosetEdge)) := by
  change Function.Injective
    (SourceProfiniteCosetSystem.cosetSection
      (diagram.edgeGroup edge))
  exact SourceProfiniteCosetSystem.cosetSection_injective
    (diagram.edgeGroup edge) closed

/-- The stabilizer of the compatible finite-level vertex system agrees with
the stabilizer of the corresponding Bass--Serre coset vertex. -/
theorem profiniteVertexSection_stabilizer_eq
    (closedVertex : ∀ vertex,
      IsClosed (diagram.vertexGroup vertex : Set Ambient))
    (point : diagram.CosetVertex) :
    (SourceProfiniteCosetSystem.system
      (diagram.vertexGroup point.1)).sectionStabilizer
        (diagram.profiniteVertexSection point) =
      diagram.cosetAction.vertexStabilizer point := by
  change
    (SourceProfiniteCosetSystem.system
      (diagram.vertexGroup point.1)).sectionStabilizer
        (SourceProfiniteCosetSystem.cosetSection
          (diagram.vertexGroup point.1) point.2) = _
  rw [SourceProfiniteCosetSystem.sectionStabilizer_cosetSection_eq_conjugate
    (diagram.vertexGroup point.1) (closedVertex point.1) point.2]
  symm
  exact diagram.cosetAction_vertexStabilizer_eq_conjugate point

/-- The stabilizer of the compatible finite-level edge system agrees with
the stabilizer of the corresponding Bass--Serre coset edge. -/
theorem profiniteEdgeSection_stabilizer_eq
    (closedEdge : ∀ edge,
      IsClosed (diagram.edgeGroup edge : Set Ambient))
    (point : diagram.CosetEdge) :
    (SourceProfiniteCosetSystem.system
      (diagram.edgeGroup point.1)).sectionStabilizer
        (diagram.profiniteEdgeSection point) =
      diagram.cosetAction.edgeStabilizer point := by
  change
    (SourceProfiniteCosetSystem.system
      (diagram.edgeGroup point.1)).sectionStabilizer
        (SourceProfiniteCosetSystem.cosetSection
          (diagram.edgeGroup point.1) point.2) = _
  rw [SourceProfiniteCosetSystem.sectionStabilizer_cosetSection_eq_conjugate
    (diagram.edgeGroup point.1) (closedEdge point.1) point.2]
  symm
  exact diagram.cosetAction_edgeStabilizer_eq_conjugate point

end SourceSemiGraphSubgroupDiagram

end Iut
