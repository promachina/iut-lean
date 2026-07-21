/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Tactic

/-!
# Orbicurve source objects

This file supplies the stack- and Galois-category-level types needed to replace
the string-labelled orbicurves in the old finite model. It deliberately does
not assert that an arbitrary stack is algebraic or Deligne-Mumford: those
conditions require representability infrastructure that is not yet in mathlib
and remain named source obligations in the trace ledger.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped SpecOfNotation
open scoped Pseudofunctor.StrongTrans

namespace Iut

universe u

/--
The absolute Galois group of `F`, with its Krull topology, as an actual
profinite group.
-/
noncomputable abbrev AbsoluteGaloisProfinite
    (F : Type u) [Field F] [CharZero F] : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp F (AlgebraicClosure F)

/-- The category of schemes over `Spec(F)`. -/
noncomputable abbrev SchemeOverField (F : Type u) [CommRing F] :=
  Over (Spec(F))

/-- The big etale topology on schemes over `Spec(F)`. -/
noncomputable abbrev SchemeOverField.etaleTopology
    (F : Type u) [CommRing F] :
    GrothendieckTopology (SchemeOverField F) :=
  GrothendieckTopology.over AlgebraicGeometry.Scheme.etaleTopology (Spec(F))

/--
A category-valued etale stack over a field.

The descent condition is mathlib's actual effective-descent predicate for
pseudofunctors into `Cat`.
-/
structure EtaleStackOverField (F : Type u) [CommRing F] where
  fiber :
    LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u}
  isStack : fiber.IsStack (SchemeOverField.etaleTopology F)

/-- The bicategory in which category-valued etale stacks are diagrams. -/
abbrev EtaleStackPseudofunctor (F : Type u) [CommRing F] :=
  LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u}

/-- A morphism of etale stacks, represented by a strong transformation. -/
abbrev EtaleStackOverField.Hom
    {F : Type u} [CommRing F]
    (X Y : EtaleStackOverField F) :=
  Pseudofunctor.StrongTrans X.fiber Y.fiber

/--
The signature `(g; m_1,...,m_r; n)` of an orbicurve: genus, stacky-point
orders, and ordinary punctures.
-/
structure OrbicurveSignature where
  genus : ℕ
  stackyOrders : List ℕ
  punctures : ℕ
  stackyOrders_ge_two : ∀ m ∈ stackyOrders, 2 ≤ m

namespace OrbicurveSignature

/-- Orbifold Euler characteristic `2 - 2g - n - sum_i (1 - 1/m_i)`. -/
noncomputable def eulerCharacteristic (signature : OrbicurveSignature) : ℚ :=
  2 - 2 * signature.genus - signature.punctures -
    (signature.stackyOrders.map fun m : ℕ => 1 - (1 : ℚ) / m).sum

/-- An orbicurve signature is hyperbolic when its orbifold Euler characteristic is negative. -/
def IsHyperbolic (signature : OrbicurveSignature) : Prop :=
  signature.eulerCharacteristic < 0

/-- The signature of a once-punctured elliptic curve. -/
def oncePuncturedElliptic : OrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := 1
  stackyOrders_ge_two := by simp

theorem oncePuncturedElliptic_eulerCharacteristic :
    oncePuncturedElliptic.eulerCharacteristic = -1 := by
  norm_num [eulerCharacteristic, oncePuncturedElliptic]

theorem oncePuncturedElliptic_isHyperbolic :
    oncePuncturedElliptic.IsHyperbolic := by
  norm_num [IsHyperbolic, oncePuncturedElliptic_eulerCharacteristic]

end OrbicurveSignature

/--
A hyperbolic orbicurve over `F` at the currently available source-faithful
interface: an etale stack together with its orbifold signature and a proof of
negative orbifold Euler characteristic.
-/
structure HyperbolicOrbicurve (F : Type u) [Field F] where
  stack : EtaleStackOverField F
  signature : OrbicurveSignature
  hyperbolic : signature.IsHyperbolic

/-- A morphism of hyperbolic orbicurves is a morphism of their etale stacks. -/
abbrev HyperbolicOrbicurve.Hom
    {F : Type u} [Field F]
    (X Y : HyperbolicOrbicurve F) :=
  X.stack.Hom Y.stack

noncomputable instance HyperbolicOrbicurve.Hom.category
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F} :
    Category (X.Hom Y) := by
  exact
    @Pseudofunctor.StrongTrans.homCategory
      (LocallyDiscrete (SchemeOverField F)ᵒᵖ) inferInstance
      Cat inferInstance
      X.stack.fiber Y.stack.fiber

/-- An invertible modification between two orbicurve morphisms. -/
abbrev HyperbolicOrbicurve.Hom.TwoIso
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (f g : X.Hom Y) :=
  Iso f g

/-- A modification between orbicurve morphisms. -/
abbrev HyperbolicOrbicurve.Hom.TwoCell
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (f g : X.Hom Y) :=
  Pseudofunctor.StrongTrans.Hom f g

namespace HyperbolicOrbicurve.Hom.TwoCell

variable
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    {f g h : X.Hom Y}

def id (f : X.Hom Y) :
    HyperbolicOrbicurve.Hom.TwoCell f f :=
  ⟨Pseudofunctor.StrongTrans.Modification.id f⟩

def comp
    (first : HyperbolicOrbicurve.Hom.TwoCell f g)
    (second : HyperbolicOrbicurve.Hom.TwoCell g h) :
    HyperbolicOrbicurve.Hom.TwoCell f h :=
  ⟨Pseudofunctor.StrongTrans.Modification.vcomp
    first.as second.as⟩

end HyperbolicOrbicurve.Hom.TwoCell

/-- The identity morphism of a hyperbolic orbicurve. -/
noncomputable def HyperbolicOrbicurve.Hom.id
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) :
    X.Hom X :=
  Pseudofunctor.StrongTrans.id X.stack.fiber

/-- Composition of morphisms of hyperbolic orbicurves. -/
noncomputable def HyperbolicOrbicurve.Hom.comp
    {F : Type u} [Field F]
    {X Y Z : HyperbolicOrbicurve F}
    (f : X.Hom Y) (g : Y.Hom Z) :
    X.Hom Z :=
  Pseudofunctor.StrongTrans.vcomp f g

/-- Transport an orbicurve morphism along equalities of its source and target. -/
noncomputable def HyperbolicOrbicurve.Hom.cast
    {F : Type u} [Field F]
    {X X' Y Y' : HyperbolicOrbicurve F}
    (source_eq : X = X') (target_eq : Y = Y')
    (f : X.Hom Y) :
    X'.Hom Y' := by
  subst X'
  subst Y'
  exact f

/-- The order-two group that acts by elliptic inversion. -/
abbrev SignGroup :=
  Multiplicative (ZMod 2)

/-- The one-object bicategory indexing a coherent sign action. -/
abbrev SignActionIndex :=
  LocallyDiscrete (SingleObj SignGroup)

/-- The unique object of the sign-action indexing bicategory. -/
def signActionObject : SignActionIndex :=
  LocallyDiscrete.mk (Quiver.SingleObj.star SignGroup)

/-- The nontrivial element of the sign group. -/
def signActionGenerator :
    signActionObject ⟶ signActionObject :=
  ⟨Multiplicative.ofAdd (1 : ZMod 2)⟩

/--
A coherent action of the sign group on an orbicurve stack.

The pseudofunctor supplies the unit, multiplication, and associativity
coherences. `generator_identification` identifies its nontrivial arrow with
the chosen elliptic inversion on `X`.
-/
structure OrbicurveSignAction
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) where
  diagram :
    SignActionIndex ⥤ᵖ
      EtaleStackPseudofunctor F
  atBase :
    Bicategory.Equivalence
      (diagram.obj signActionObject) X.stack.fiber
  inversion : X.Hom X
  generator_identification :
    (atBase.inv ≫ diagram.map signActionGenerator) ≫
        atBase.hom ≅
      inversion
  inversionSquared :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp inversion inversion)
      (HyperbolicOrbicurve.Hom.id X)

namespace OrbicurveSignAction

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable (action : OrbicurveSignAction X)

/-- The coherence for composing two copies of the nontrivial sign arrow. -/
def generatorSquareComparison :
    action.diagram.map
        (signActionGenerator ≫ signActionGenerator) ≅
      action.diagram.map signActionGenerator ≫
        action.diagram.map signActionGenerator :=
  action.diagram.mapComp
    signActionGenerator signActionGenerator

end OrbicurveSignAction

/--
A morphism out of an orbicurve that is equivariant for its sign action.

The cocycle equation says that applying the invariant 2-isomorphism twice is
the identity after identifying two inversions with the identity action.
-/
structure OrbicurveSignInvariantMorphism
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    (action : OrbicurveSignAction X)
    (Y : HyperbolicOrbicurve F) where
  map : X.Hom Y
  invariant :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp action.inversion map)
      map
  cocycle :
    (Pseudofunctor.StrongTrans.associator
          action.inversion action.inversion map).hom ≫
        Pseudofunctor.StrongTrans.whiskerLeft
          action.inversion invariant.hom ≫
        invariant.hom =
      Pseudofunctor.StrongTrans.whiskerRight
          action.inversionSquared.hom map ≫
        (Pseudofunctor.StrongTrans.leftUnitor map).hom

namespace OrbicurveSignInvariantMorphism

variable
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    {action : OrbicurveSignAction X}

/-- A 2-cell compatible with the sign-invariance structures. -/
structure Hom
    (source target : OrbicurveSignInvariantMorphism action Y) where
  app :
    HyperbolicOrbicurve.Hom.TwoCell source.map target.map
  equivariant :
    Pseudofunctor.StrongTrans.whiskerLeft
          action.inversion app ≫
        target.invariant.hom =
      source.invariant.hom ≫ app

end OrbicurveSignInvariantMorphism

/--
The bicategorical universal property of the quotient of `X` by its sign
action.

Every coherent invariant map out of `X` descends through `quotient`. Every
compatible 2-cell descends, and equality can be checked after precomposition
with `quotient`. These are essential surjectivity, fullness, and faithfulness
of the functor from maps out of the quotient to invariant maps out of `X`.
-/
structure OrbicurveSignQuotientWitness
    {F : Type u} [Field F]
    {X C : HyperbolicOrbicurve F}
    (action : OrbicurveSignAction X)
    (quotient :
      OrbicurveSignInvariantMorphism action C) where
  descend :
    ∀ (Y : HyperbolicOrbicurve F),
      OrbicurveSignInvariantMorphism action Y →
        C.Hom Y
  factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (invariant :
        OrbicurveSignInvariantMorphism action Y),
      HyperbolicOrbicurve.Hom.TwoIso
        (HyperbolicOrbicurve.Hom.comp
          quotient.map (descend Y invariant))
        invariant.map
  descendTwoCell :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target :
        OrbicurveSignInvariantMorphism action Y),
      OrbicurveSignInvariantMorphism.Hom source target →
        HyperbolicOrbicurve.Hom.TwoCell
          (descend Y source) (descend Y target)
  descendTwoCell_factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target :
        OrbicurveSignInvariantMorphism action Y)
      (alpha :
        OrbicurveSignInvariantMorphism.Hom source target),
      Pseudofunctor.StrongTrans.whiskerLeft
          quotient.map
          (descendTwoCell Y source target alpha) =
        (factor Y source).hom ≫ alpha.app ≫
          (factor Y target).inv
  twoCell_ext :
    ∀ (Y : HyperbolicOrbicurve F)
      {first second : C.Hom Y}
      (alpha beta :
        HyperbolicOrbicurve.Hom.TwoCell first second),
      Pseudofunctor.StrongTrans.whiskerLeft
          quotient.map alpha =
          Pseudofunctor.StrongTrans.whiskerLeft
            quotient.map beta →
        alpha = beta

/--
A chosen fiber functor and certified profinite fundamental group for a Galois
category of finite etale covers.
-/
structure EtaleFundamentalGroup where
  Cover : Type u
  coverCategory : Category.{u} Cover
  galoisCategory : @GaloisCategory Cover coverCategory
  fiber : letI := coverCategory; Cover ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  group : ProfiniteGrp.{u}
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ X : Cover, MulAction group (fiber.obj X)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (X : Cover) := action X
    PreGaloisCategory.IsFundamentalGroup fiber group

namespace EtaleFundamentalGroup

/-- The stored profinite group is the fundamental group of the stored fiber functor. -/
theorem certified (data : EtaleFundamentalGroup) :
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    letI (X : data.Cover) := data.action X
    PreGaloisCategory.IsFundamentalGroup data.fiber data.group :=
  data.isFundamentalGroup

end EtaleFundamentalGroup

/-- An actual open embedding in the category of profinite groups. -/
structure ProfiniteOpenEmbedding (source target : ProfiniteGrp.{u}) where
  hom : source ⟶ target
  isOpenEmbedding : Topology.IsOpenEmbedding hom

namespace ProfiniteOpenEmbedding

variable {source middle target : ProfiniteGrp.{u}}

theorem injective (embedding : ProfiniteOpenEmbedding source target) :
    Function.Injective embedding.hom :=
  embedding.isOpenEmbedding.injective

theorem open_range (embedding : ProfiniteOpenEmbedding source target) :
    IsOpen (Set.range embedding.hom) :=
  embedding.isOpenEmbedding.isOpen_range

/-- Composition preserves the open-embedding condition. -/
def comp
    (first : ProfiniteOpenEmbedding source middle)
    (second : ProfiniteOpenEmbedding middle target) :
    ProfiniteOpenEmbedding source target where
  hom := first.hom ≫ second.hom
  isOpenEmbedding := by
    simpa [Function.comp_def] using
      second.isOpenEmbedding.comp first.isOpenEmbedding

end ProfiniteOpenEmbedding

/--
An injective morphism of profinite groups.

Unlike `ProfiniteOpenEmbedding`, this is the appropriate notion for local
decomposition groups inside an absolute Galois group: their images are closed,
but need not be open.
-/
structure ProfiniteEmbedding (source target : ProfiniteGrp.{u}) where
  hom : source ⟶ target
  injective : Function.Injective hom

namespace ProfiniteEmbedding

variable {source middle target : ProfiniteGrp.{u}}

/-- Composition of injective continuous profinite-group morphisms. -/
def comp
    (first : ProfiniteEmbedding source middle)
    (second : ProfiniteEmbedding middle target) :
    ProfiniteEmbedding source target where
  hom := first.hom ≫ second.hom
  injective := second.injective.comp first.injective

end ProfiniteEmbedding

/-- A closed subgroup with its induced topology, regarded as a profinite group. -/
def closedSubgroupProfiniteGrp
    {G : ProfiniteGrp.{u}} (subgroup : ClosedSubgroup G) :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.ofClosedSubgroup subgroup

/-- The canonical continuous injective morphism from a closed subgroup. -/
def closedSubgroupProfiniteInclusion
    {G : ProfiniteGrp.{u}} (subgroup : ClosedSubgroup G) :
    ProfiniteEmbedding (closedSubgroupProfiniteGrp subgroup) G := by
  letI : IsTopologicalGroup subgroup :=
    inferInstanceAs (IsTopologicalGroup subgroup.toSubgroup)
  change ProfiniteEmbedding (ProfiniteGrp.of subgroup) G
  refine
    { hom := ProfiniteGrp.ofHom
        ⟨subgroup.toSubgroup.subtype, continuous_subtype_val⟩
      injective := ?_ }
  exact Subtype.val_injective

/--
An exact sequence `1 -> geometric -> arithmetic -> Galois -> 1` of profinite
groups. Exactness is an equality of the actual range and kernel subgroups.
-/
structure ProfiniteFundamentalExactSequence
    (geometric arithmetic galois : ProfiniteGrp.{u}) where
  inclusion : geometric ⟶ arithmetic
  projection : arithmetic ⟶ galois
  inclusion_injective : Function.Injective inclusion
  projection_surjective : Function.Surjective projection
  exact : inclusion.hom.range = projection.hom.ker

namespace ProfiniteFundamentalExactSequence

variable {geometric arithmetic galois : ProfiniteGrp.{u}}
variable (sequence :
  ProfiniteFundamentalExactSequence geometric arithmetic galois)

theorem projection_comp_inclusion_eq_one :
    sequence.projection.hom.toMonoidHom.comp
        sequence.inclusion.hom.toMonoidHom = 1 := by
  ext g
  rw [MonoidHom.comp_apply]
  have hg : sequence.inclusion g ∈ sequence.inclusion.hom.range :=
    ⟨g, rfl⟩
  rw [sequence.exact] at hg
  exact hg

end ProfiniteFundamentalExactSequence

/--
A compatible pair of geometric and arithmetic open immersions between two
fundamental-group exact sequences. This is the group-theoretic square occurring
in IUT I, Definition 3.1(d)-(e).
-/
structure ProfiniteFundamentalGroupInclusion
    (sourceGeometric sourceArithmetic
      targetGeometric targetArithmetic galois : ProfiniteGrp.{u})
    (sourceSequence :
      ProfiniteFundamentalExactSequence
        sourceGeometric sourceArithmetic galois)
    (targetSequence :
      ProfiniteFundamentalExactSequence
        targetGeometric targetArithmetic galois) where
  geometric :
    ProfiniteOpenEmbedding sourceGeometric targetGeometric
  arithmetic :
    ProfiniteOpenEmbedding sourceArithmetic targetArithmetic
  inclusion_square :
    geometric.hom ≫ targetSequence.inclusion =
      sourceSequence.inclusion ≫ arithmetic.hom
  projection_compatible :
    arithmetic.hom ≫ targetSequence.projection =
      sourceSequence.projection

/--
An injective morphism between two fundamental-group exact sequences, allowing
the source and target Galois quotients to differ.

This is the local-to-global decomposition diagram of IUT I, Definition 3.1(e).
-/
structure ProfiniteFundamentalExactSequenceEmbedding
    (sourceGeometric sourceArithmetic sourceGalois
      targetGeometric targetArithmetic targetGalois : ProfiniteGrp.{u})
    (sourceSequence :
      ProfiniteFundamentalExactSequence
        sourceGeometric sourceArithmetic sourceGalois)
    (targetSequence :
      ProfiniteFundamentalExactSequence
        targetGeometric targetArithmetic targetGalois) where
  geometric :
    ProfiniteEmbedding sourceGeometric targetGeometric
  arithmetic :
    ProfiniteEmbedding sourceArithmetic targetArithmetic
  galois :
    ProfiniteEmbedding sourceGalois targetGalois
  inclusion_square :
    geometric.hom ≫ targetSequence.inclusion =
      sourceSequence.inclusion ≫ arithmetic.hom
  projection_square :
    arithmetic.hom ≫ targetSequence.projection =
      sourceSequence.projection ≫ galois.hom

end Iut
