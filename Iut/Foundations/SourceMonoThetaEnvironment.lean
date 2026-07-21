/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceInitialThetaData
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Source boundary for mono-theta environments and their inverse limits

This module formalizes the group-theoretic data in *The Etale Theta
Function and its Frobenioid-theoretic Manifestations*, Definition 2.13, and
the inverse-limit clause of IUT II, Definition 2.7(i).

The ambient groups are genuine topological groups.  The theta-section
collection is the conjugacy class of the image of a continuous injective
homomorphism, and an outer subgroup is represented by its full inverse image
in the continuous automorphism group.  This avoids replacing `Out(Pi)` by an
unrelated finite action.

No constructor from initial theta data is provided here: constructing the
tempered fundamental groups, Kummer extensions, and transition reductions is
the remaining source obligation.
-/

open CategoryTheory

namespace Iut

universe u

/-- Topological groups and continuous homomorphisms, without a compactness assumption. -/
structure TopologicalGroupCat where
  toFundamentalGroup : AbstractFundamentalGroup.{u}

namespace TopologicalGroupCat

instance : CoeSort TopologicalGroupCat.{u} (Type u) :=
  ⟨fun G => G.toFundamentalGroup.carrier⟩

instance (G : TopologicalGroupCat) : Group G :=
  G.toFundamentalGroup.group

instance (G : TopologicalGroupCat) : TopologicalSpace G :=
  G.toFundamentalGroup.topology

instance (G : TopologicalGroupCat) : IsTopologicalGroup G :=
  G.toFundamentalGroup.isTopologicalGroup

instance : Category TopologicalGroupCat where
  Hom G H := G →ₜ* H
  id G := _root_.ContinuousMonoidHom.id G
  comp f g := g.comp f
  assoc _ _ _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  id_comp _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  comp_id _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

/-- A profinite group regarded as a topological group object. -/
def ofProfinite (G : ProfiniteGrp.{u}) : TopologicalGroupCat where
  toFundamentalGroup :=
    { carrier := G
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .profinite }

/-- A subgroup with its induced topological-group structure. -/
def ofSubgroup
    (G : TopologicalGroupCat.{u})
    (H : Subgroup G) :
    TopologicalGroupCat.{u} where
  toFundamentalGroup :=
    { carrier := H
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind :=
        G.toFundamentalGroup.topologyKind }

/-- The continuous inclusion of a subgroup into its ambient topological group. -/
def subgroupInclusion
    (G : TopologicalGroupCat.{u})
    (H : Subgroup G) :
    ofSubgroup G H ⟶ G where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

end TopologicalGroupCat

/--
A topological group subquotient `U / N`.

Both groups are derived from the ambient group: `U` is an actual subgroup and
`N` is an actual normal subgroup of `U`.  In particular, the carrier is not an
unrelated type merely equipped with a comparison map.
-/
structure SourceTopologicalSubquotient
    (G : TopologicalGroupCat.{u}) where
  numerator : Subgroup G
  denominator : Subgroup numerator
  denominator_normal :
    denominator.Normal

namespace SourceTopologicalSubquotient

variable {G : TopologicalGroupCat.{u}}

instance (Q : SourceTopologicalSubquotient G) :
    Q.denominator.Normal :=
  Q.denominator_normal

/-- The actual quotient carrier `U / N`. -/
abbrev Carrier
    (Q : SourceTopologicalSubquotient G) : Type u :=
  Q.numerator ⧸ Q.denominator

/-- A source subquotient regarded as a topological group object. -/
def toTopologicalGroupCat
    (Q : SourceTopologicalSubquotient G) :
    TopologicalGroupCat.{u} where
  toFundamentalGroup :=
    { carrier := Q.Carrier
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The continuous quotient projection `U -> U / N`. -/
def projection
    (Q : SourceTopologicalSubquotient G) :
    Q.numerator →ₜ* Q.Carrier where
  toMonoidHom :=
    QuotientGroup.mk' Q.denominator
  continuous_toFun :=
    QuotientGroup.continuous_mk

/-- The homomorphism from a pulled-back numerator to the original numerator. -/
def comapNumeratorHom
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    Subgroup.comap f.toMonoidHom Q.numerator →*
      Q.numerator where
  toFun h := ⟨f.toMonoidHom h.1, h.2⟩
  map_one' := by
    apply SetCoe.ext
    exact map_one f.toMonoidHom
  map_mul' first second := by
    apply SetCoe.ext
    exact map_mul f.toMonoidHom first.1 second.1

/--
Pull a topological subquotient `U/N` back along a continuous group
homomorphism, obtaining `f⁻¹(U)/f⁻¹(N)`.
-/
def comap
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    SourceTopologicalSubquotient H where
  numerator :=
    Subgroup.comap f.toMonoidHom Q.numerator
  denominator :=
    Subgroup.comap (Q.comapNumeratorHom f)
      Q.denominator
  denominator_normal :=
    Q.denominator_normal.comap
      (Q.comapNumeratorHom f)

end SourceTopologicalSubquotient

/-- Continuous automorphisms of a topological group. -/
abbrev ContinuousAutomorphism (G : TopologicalGroupCat.{u}) :=
  G ≃ₜ* G

namespace ContinuousAutomorphism

variable (G : TopologicalGroupCat.{u})

instance : Mul (ContinuousAutomorphism G) :=
  ⟨fun f g => g.trans f⟩

instance : One (ContinuousAutomorphism G) :=
  ⟨_root_.ContinuousMulEquiv.refl G⟩

instance : Inv (ContinuousAutomorphism G) :=
  ⟨fun f => f.symm⟩

instance : Group (ContinuousAutomorphism G) :=
  Group.ofLeftAxioms
    (fun _ _ _ => by
      apply _root_.ContinuousMulEquiv.ext
      intro
      rfl)
    (fun _ => by
      apply _root_.ContinuousMulEquiv.ext
      intro
      rfl)
    (fun f => by
      apply _root_.ContinuousMulEquiv.ext
      intro x
      exact f.left_inv x)

/-- Conjugation by a group element as a continuous automorphism. -/
def inner (g : G) : ContinuousAutomorphism G where
  toMulEquiv := MulAut.conj g
  continuous_toFun :=
    (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun :=
    (continuous_const.mul continuous_id).mul continuous_const

@[simp]
theorem inner_apply (g x : G) :
    inner G g x = g * x * g⁻¹ :=
  rfl

/-- Inner automorphisms form the range of the conjugation homomorphism. -/
def innerHom : G →* ContinuousAutomorphism G where
  toFun := inner G
  map_one' := by
    apply _root_.ContinuousMulEquiv.ext
    intro x
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  map_mul' g h := by
    apply _root_.ContinuousMulEquiv.ext
    intro x
    change
      (g * h) * x * (g * h)⁻¹ =
        g * (h * x * h⁻¹) * g⁻¹
    simp [mul_assoc]

/-- The range of the conjugation homomorphism is a normal subgroup. -/
theorem inner_range_normal :
    (innerHom G).range.Normal := by
  constructor
  intro innerAutomorphism hinner automorphism
  rcases hinner with ⟨g, rfl⟩
  refine ⟨automorphism g, ?_⟩
  apply _root_.ContinuousMulEquiv.ext
  intro x
  change
    automorphism g * x * (automorphism g)⁻¹ =
      automorphism
        (g * automorphism.symm x * g⁻¹)
  simp

instance : (innerHom G).range.Normal :=
  inner_range_normal G

/-- The exact inner-automorphism subgroup, i.e. the range of conjugation. -/
def innerSubgroup : Subgroup (ContinuousAutomorphism G) :=
  (innerHom G).range

/-- The continuous outer automorphism group `Aut_cont(G) / Inn(G)`. -/
abbrev Outer :=
  ContinuousAutomorphism G ⧸ innerSubgroup G

/-- Transport a continuous automorphism through a topological-group isomorphism. -/
def transport
    {H : TopologicalGroupCat.{u}}
    (e : G ≃ₜ* H) (f : ContinuousAutomorphism G) :
    ContinuousAutomorphism H :=
  e.symm.trans (f.trans e)

@[simp]
theorem transport_apply
    {H : TopologicalGroupCat.{u}}
    (e : G ≃ₜ* H) (f : ContinuousAutomorphism G) (x : H) :
    transport G e f x = e (f (e.symm x)) :=
  rfl

end ContinuousAutomorphism

/--
A subgroup of `Out(G)`, represented by its full inverse image in
`Aut_cont(G)`.  Containment of all inner automorphisms is precisely the
condition for such a full inverse image.
-/
structure ContinuousOuterSubgroup (G : TopologicalGroupCat.{u}) where
  automorphisms : Subgroup (ContinuousAutomorphism G)
  inner_le :
    ContinuousAutomorphism.innerSubgroup G ≤ automorphisms

/-- Two subgroups are conjugate by an element of a specified subgroup. -/
def SubgroupsConjugateBy
    {G : Type u} [Group G]
    (conjugators first second : Subgroup G) : Prop :=
  ∃ g : conjugators,
    second =
      first.map (MulAut.conj (g : G)).toMonoidHom

namespace SubgroupsConjugateBy

variable {G : Type u} [Group G]
variable {C H K L : Subgroup G}

theorem refl (H : Subgroup G) :
    SubgroupsConjugateBy C H H := by
  refine ⟨⟨1, C.one_mem⟩, ?_⟩
  ext x
  simp

theorem symm (h : SubgroupsConjugateBy C H K) :
    SubgroupsConjugateBy C K H := by
  rcases h with ⟨g, rfl⟩
  refine ⟨⟨(g : G)⁻¹, C.inv_mem g.property⟩, ?_⟩
  ext x
  simp [Subgroup.mem_map, mul_assoc]

end SubgroupsConjugateBy

/--
The ordered triple underlying a mod-`N` mono-theta environment in EtTh,
Definition 2.13(ii).

The cyclic kernel is explicit, and the theta-section collection is derived
from the image of an actual continuous injective section.
-/
structure SourceMonoThetaEnvironmentData
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  outerSymmetries : ContinuousOuterSubgroup G
  cyclotome : Subgroup G
  cyclotomeLabelEquiv :
    cyclotome ≃*
      EtaleTheta.LTorsionLabel N.val
  thetaSectionDomain : TopologicalGroupCat.{u}
  thetaSection : thetaSectionDomain ⟶ G
  thetaSection_injective :
    Function.Injective thetaSection.toMonoidHom

namespace SourceMonoThetaEnvironmentData

variable {N : ℕ+} {G : TopologicalGroupCat.{u}}

/-- The representative subgroup determined by the image of the theta section. -/
def thetaSectionSubgroup
    (E : SourceMonoThetaEnvironmentData N G) :
    Subgroup G :=
  E.thetaSection.toMonoidHom.range

/-- The `mu_N`-conjugacy class of theta-section images. -/
def thetaSectionClass
    (E : SourceMonoThetaEnvironmentData N G) :
    Set (Subgroup G) :=
  { H | SubgroupsConjugateBy E.cyclotome E.thetaSectionSubgroup H }

theorem thetaSectionSubgroup_mem_class
    (E : SourceMonoThetaEnvironmentData N G) :
    E.thetaSectionSubgroup ∈ E.thetaSectionClass :=
  SubgroupsConjugateBy.refl E.thetaSectionSubgroup

end SourceMonoThetaEnvironmentData

/--
The additional geometric generators of a model mono-theta environment.
Their images, together with all inner automorphisms, generate the prescribed
inverse image of `D_Y` in the continuous automorphism group.
-/
structure SourceModelMonoThetaEnvironment
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  data : SourceMonoThetaEnvironmentData N G
  unitSymmetryGroup : TopologicalGroupCat.{u}
  deckSymmetryGroup : TopologicalGroupCat.{u}
  unitOuterAction :
    unitSymmetryGroup →*
      ContinuousAutomorphism G
  deckOuterAction :
    deckSymmetryGroup →*
      ContinuousAutomorphism G
  outerSymmetries_generated :
    data.outerSymmetries.automorphisms =
      ContinuousAutomorphism.innerSubgroup G ⊔
        unitOuterAction.range ⊔
          deckOuterAction.range

/--
An isomorphism from an abstract mono-theta triple to a model triple.  Each
compatibility is stated on the actual group isomorphism rather than by an
unrelated equivalence of labels.
-/
structure SourceMonoThetaEnvironmentRealization
    {N : ℕ+}
    {G H : TopologicalGroupCat.{u}}
    (source : SourceMonoThetaEnvironmentData N G)
    (target : SourceMonoThetaEnvironmentData N H) where
  groupIso : G ≃ₜ* H
  outerSymmetries_iff :
    ∀ f : ContinuousAutomorphism G,
      f ∈ source.outerSymmetries.automorphisms ↔
        ContinuousAutomorphism.transport G groupIso f ∈
          target.outerSymmetries.automorphisms
  cyclotome_iff :
    ∀ x : G,
      x ∈ source.cyclotome ↔
        groupIso x ∈ target.cyclotome
  thetaSections_compatible :
    SubgroupsConjugateBy
      target.cyclotome
      (source.thetaSectionSubgroup.map
        groupIso.toMulEquiv.toMonoidHom)
      target.thetaSectionSubgroup

/--
A mod-`N` mono-theta environment: an abstract ordered triple together with
the model realization required by EtTh, Definition 2.13(ii).
-/
structure SourceMonoThetaEnvironment
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  data : SourceMonoThetaEnvironmentData N G
  modelGroup : TopologicalGroupCat.{u}
  model : SourceModelMonoThetaEnvironment N modelGroup
  realization :
    SourceMonoThetaEnvironmentRealization data model.data

/--
Positive moduli ordered in the direction of the transition arrows:
`M' ≤ M` means that `M` divides `M'`, hence the system has a map from the
mod-`M'` object to the mod-`M` object.
-/
structure MonoThetaModulus where
  modulus : ℕ+

namespace MonoThetaModulus

instance : Preorder MonoThetaModulus where
  le M' M := M.modulus.val ∣ M'.modulus.val
  le_refl _ := dvd_rfl
  le_trans _ _ _ h₁ h₂ := dvd_trans h₂ h₁

end MonoThetaModulus

/--
A projective system of mono-theta environments as used in IUT II,
Definition 2.7.

The group maps form an actual functor.  Surjectivity and compatibility with
the cyclic kernels and theta-section conjugacy classes record the reduction
behavior of the EtTh transition morphisms.  Compatibility of the full outer
actions with the induced moduli remains a separate source obligation.
-/
structure SourceMonoThetaProjectiveSystem where
  groupDiagram :
    MonoThetaModulus ⥤ TopologicalGroupCat.{u}
  environment :
    ∀ M : MonoThetaModulus,
      SourceMonoThetaEnvironment M.modulus
        (groupDiagram.obj M)
  transition_surjective :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      Function.Surjective
        (groupDiagram.map f).toMonoidHom
  transition_cyclotome :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      Subgroup.map
          (groupDiagram.map f).toMonoidHom
          (environment M').data.cyclotome =
        (environment M).data.cyclotome
  transition_thetaSections :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      SubgroupsConjugateBy
        (environment M).data.cyclotome
        (Subgroup.map
          (groupDiagram.map f).toMonoidHom
          (environment M').data.thetaSectionSubgroup)
        (environment M).data.thetaSectionSubgroup
  inverseLimitCone : Limits.Cone groupDiagram
  inverseLimitCone_isLimit :
    Limits.IsLimit inverseLimitCone

namespace SourceMonoThetaProjectiveSystem

/-- The topological inverse-limit group `Pi_(MTheta_*)`. -/
def inverseLimit (S : SourceMonoThetaProjectiveSystem.{u}) :
    TopologicalGroupCat.{u} :=
  S.inverseLimitCone.pt

/-- The canonical projection from the inverse limit to a finite level. -/
def projection
    (S : SourceMonoThetaProjectiveSystem.{u})
    (M : MonoThetaModulus) :
    S.inverseLimit ⟶ S.groupDiagram.obj M :=
  S.inverseLimitCone.π.app M

theorem projection_naturality
    (S : SourceMonoThetaProjectiveSystem.{u})
    {M' M : MonoThetaModulus} (f : M' ⟶ M) :
    S.projection M' ≫ S.groupDiagram.map f =
      S.projection M :=
  S.inverseLimitCone.w f

end SourceMonoThetaProjectiveSystem

/--
IUT II, Definition 2.7(i): the inverse-limit group, its natural map to the
ambient fundamental group, the exterior cyclotome as its exact kernel, and
the tempered subgroup as its exact image.
-/
structure SourceIUTIIDefinition27PartI where
  system : SourceMonoThetaProjectiveSystem.{u}
  ambientFundamentalGroup : TopologicalGroupCat.{u}
  toAmbient :
    system.inverseLimit ⟶ ambientFundamentalGroup
  exteriorCyclotome :
    Subgroup system.inverseLimit
  kernel_eq_exteriorCyclotome :
    toAmbient.toMonoidHom.ker =
      exteriorCyclotome
  temperedSubgroup :
    Subgroup ambientFundamentalGroup
  range_eq_temperedSubgroup :
    toAmbient.toMonoidHom.range =
      temperedSubgroup

namespace SourceIUTIIDefinition27PartI

/-- The inverse image of an ambient subgroup in the mono-theta inverse limit. -/
def inverseImage
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    Subgroup partI.system.inverseLimit :=
  Subgroup.comap partI.toAmbient.toMonoidHom subgroup

/-- The inverse image equipped with its induced topological-group structure. -/
def inverseImageGroup
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    TopologicalGroupCat.{u} :=
  TopologicalGroupCat.ofSubgroup
    partI.system.inverseLimit
    (partI.inverseImage subgroup)

/-- The natural map from an inverse-image group to the ambient fundamental group. -/
def inverseImageToAmbient
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    partI.inverseImageGroup subgroup ⟶
      partI.ambientFundamentalGroup :=
  partI.toAmbient.comp
    (TopologicalGroupCat.subgroupInclusion
      partI.system.inverseLimit
      (partI.inverseImage subgroup))

/--
Restriction of the exterior cyclotome to an inverse-image group.  Its
numerator is the actual inverse image of the exterior cyclotome and its
denominator is trivial.
-/
def exteriorCyclotomeRestriction
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup subgroup) where
  numerator :=
    Subgroup.comap
      (TopologicalGroupCat.subgroupInclusion
        partI.system.inverseLimit
        (partI.inverseImage subgroup)).toMonoidHom
      partI.exteriorCyclotome
  denominator := ⊥
  denominator_normal := inferInstance

/-- Restrict an ambient subquotient to one Definition 2.7 inverse-image group. -/
def restrictAmbientSubquotient
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup)
    (Q :
      SourceTopologicalSubquotient
        partI.ambientFundamentalGroup) :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup subgroup) :=
  Q.comap (partI.inverseImageToAmbient subgroup)

end SourceIUTIIDefinition27PartI

/--
IUT II, Definition 2.7(ii): nested inverse-image groups, the four indicated
subquotients of the smaller inverse image, and restricted cyclotomic rigidity.

The ambient nested groups and their inverse images are not duplicated as
fields: the inverse images are computed through the homomorphism of
Definition 2.7(i).  The exterior cyclotome is restricted directly from the
kernel in part (i); the other three subquotients are pulled back from actual
ambient subquotients.  Constructing those ambient subquotients from IUT II,
Proposition 1.4 and Corollary 2.5 remains part of the source construction.
-/
structure SourceIUTIIDefinition27PartII
    (partI : SourceIUTIIDefinition27PartI.{u}) where
  wideAmbientSubgroup :
    Subgroup partI.ambientFundamentalGroup
  narrowAmbientSubgroup :
    Subgroup partI.ambientFundamentalGroup
  narrow_le_wide :
    narrowAmbientSubgroup ≤ wideAmbientSubgroup
  wide_le_tempered :
    wideAmbientSubgroup ≤ partI.temperedSubgroup
  ambientLDeltaThetaSubquotient :
    SourceTopologicalSubquotient
      partI.ambientFundamentalGroup
  ambientRestrictedTemperedSubquotient :
    SourceTopologicalSubquotient
      partI.ambientFundamentalGroup
  ambientLocalGaloisSubquotient :
    SourceTopologicalSubquotient
      partI.ambientFundamentalGroup
  cyclotomicRigidity :
    (partI.restrictAmbientSubquotient
      narrowAmbientSubgroup
      ambientLDeltaThetaSubquotient).Carrier ≃ₜ*
    (partI.exteriorCyclotomeRestriction
      narrowAmbientSubgroup).Carrier

namespace SourceIUTIIDefinition27PartII

variable
  {partI : SourceIUTIIDefinition27PartI.{u}}
  (partII : SourceIUTIIDefinition27PartII partI)

/-- The wider inverse-image group in the mono-theta inverse limit. -/
def wideInverseImage :
    Subgroup partI.system.inverseLimit :=
  partI.inverseImage partII.wideAmbientSubgroup

/-- The narrower inverse-image group in the mono-theta inverse limit. -/
def narrowInverseImage :
    Subgroup partI.system.inverseLimit :=
  partI.inverseImage partII.narrowAmbientSubgroup

/-- The exterior cyclotome restricted from the kernel in Definition 2.7(i). -/
def exteriorCyclotomeSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.exteriorCyclotomeRestriction
    partII.narrowAmbientSubgroup

/-- The `(l · Delta_Theta)` ambient subquotient restricted to the narrow group. -/
def lDeltaThetaSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientLDeltaThetaSubquotient

/-- The indicated tempered subquotient restricted to the narrow group. -/
def restrictedTemperedSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientRestrictedTemperedSubquotient

/-- The local Galois subquotient restricted to the narrow group. -/
def localGaloisSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientLocalGaloisSubquotient

theorem narrowInverseImage_le_wide :
    partII.narrowInverseImage ≤
      partII.wideInverseImage :=
  Subgroup.comap_mono partII.narrow_le_wide

/-- The stored rigidity isomorphism has the derived restricted subquotients as endpoints. -/
def cyclotomicRigidity_source :
    partII.lDeltaThetaSubquotient.Carrier ≃ₜ*
      partII.exteriorCyclotomeSubquotient.Carrier :=
  partII.cyclotomicRigidity

end SourceIUTIIDefinition27PartII

end Iut
