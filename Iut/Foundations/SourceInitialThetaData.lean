/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.EtaleThetaCovers
import Iut.Foundations.InitialThetaData
import Iut.Foundations.Orbicurve
import Iut.Foundations.OrbicurvePullback
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Source-native initial theta data

This module is the replacement path for the label-based orbicurve portion of
`InitialThetaData`. It packages actual etale stacks, strong transformations,
profinite groups, exact sequences, open immersions, and the Etale Theta
Lagrangian quotient. It is intentionally separate from the legacy record while
downstream toy modules are being isolated.
-/

open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open scoped SpecOfNotation

namespace Iut

universe u

/--
Chosen geometric and arithmetic fundamental groups of an orbicurve, with the
source exact sequence `1 -> Delta -> Pi -> G -> 1`.

The Galois-category certificates are actual `EtaleFundamentalGroup` objects.
Identifying their cover categories with the finite-etale covers of `X` remains
part of the geometric realization obligation recorded in the source ledger.
-/
structure OrbicurveFundamentalGroupData
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F)
    (galois : ProfiniteGrp.{u}) where
  geometric : EtaleFundamentalGroup
  arithmetic : EtaleFundamentalGroup
  exactSequence :
    ProfiniteFundamentalExactSequence
      geometric.group arithmetic.group galois

/--
A chosen decomposition-group representative of a rational cusp.

A cusp is a boundary point of the compactification, not a section of the open
orbicurve stack.  At the fundamental-group level it is represented, up to
conjugacy, by an exact sequence `1 -> I_epsilon -> D_epsilon -> G_F -> 1`
embedded in the orbicurve fundamental-group sequence.  Choosing a representative
is appropriate here because all fundamental groups in the initial-theta datum
already depend on compatible basepoint choices.
-/
structure OrbicurveCuspidalDecompositionData
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    {galois : ProfiniteGrp.{u}}
    (groups : OrbicurveFundamentalGroupData X galois) where
  inertia : ProfiniteGrp.{u}
  decomposition : ProfiniteGrp.{u}
  exactSequence :
    ProfiniteFundamentalExactSequence
      inertia decomposition galois
  ambientEmbedding :
    ProfiniteFundamentalExactSequenceEmbedding
      inertia decomposition galois
      groups.geometric.group groups.arithmetic.group galois
      exactSequence groups.exactSequence
  galoisEmbedding_eq_id :
    ambientEmbedding.galois.hom = 𝟙 galois

/-- An automorphism of a profinite fundamental-group exact sequence over its Galois quotient. -/
structure ProfiniteFundamentalExactSequenceAutomorphism
    {geometric arithmetic galois : ProfiniteGrp.{u}}
    (sequence :
      ProfiniteFundamentalExactSequence
        geometric arithmetic galois) where
  geometric : geometric ≅ geometric
  arithmetic : arithmetic ≅ arithmetic
  inclusion_square :
    geometric.hom ≫ sequence.inclusion =
      sequence.inclusion ≫ arithmetic.hom
  projection_compatible :
    arithmetic.hom ≫ sequence.projection =
      sequence.projection

/-- An isomorphism between two profinite fundamental exact sequences over one Galois group. -/
structure ProfiniteFundamentalExactSequenceIsomorphism
    {sourceGeometric sourceArithmetic
      targetGeometric targetArithmetic galois :
        ProfiniteGrp.{u}}
    (sourceSequence :
      ProfiniteFundamentalExactSequence
        sourceGeometric sourceArithmetic galois)
    (targetSequence :
      ProfiniteFundamentalExactSequence
        targetGeometric targetArithmetic galois) where
  geometric : sourceGeometric ≅ targetGeometric
  arithmetic : sourceArithmetic ≅ targetArithmetic
  inclusion_square :
    geometric.hom ≫ targetSequence.inclusion =
      sourceSequence.inclusion ≫ arithmetic.hom
  projection_compatible :
    arithmetic.hom ≫ targetSequence.projection =
      sourceSequence.projection

/--
The stack and fundamental-group data in IUT I, Definition 3.1(b), for
`X_F -> C_F`.
-/
structure SignQuotientOrbicurveData
    (F : Type u) [Field F]
    (curve : PuncturedEllipticCurve F) where
  absoluteGalois : ProfiniteGrp.{u}
  xF : HyperbolicOrbicurve F
  xF_signature :
    xF.signature = OrbicurveSignature.oncePuncturedElliptic
  signAction : OrbicurveSignAction xF
  cF : HyperbolicOrbicurve F
  quotientMap : xF.Hom cF
  quotientInvariant :
    OrbicurveSignInvariantMorphism signAction cF
  quotientInvariant_map :
    quotientInvariant.map = quotientMap
  quotientUniversal :
    OrbicurveSignQuotientWitness signAction quotientInvariant
  xFundamentalGroups :
    OrbicurveFundamentalGroupData xF absoluteGalois
  cFundamentalGroups :
    OrbicurveFundamentalGroupData cF absoluteGalois
  fundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      xFundamentalGroups.geometric.group
      xFundamentalGroups.arithmetic.group
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      absoluteGalois
      xFundamentalGroups.exactSequence
      cFundamentalGroups.exactSequence

namespace SignQuotientOrbicurveData

variable {F : Type u} [Field F]
variable {curve : PuncturedEllipticCurve F}
variable (data : SignQuotientOrbicurveData F curve)

theorem xF_isHyperbolic :
    data.xF.signature.IsHyperbolic :=
  data.xF.hyperbolic

theorem xF_isOncePuncturedElliptic :
    data.xF.signature = OrbicurveSignature.oncePuncturedElliptic :=
  data.xF_signature

noncomputable def quotientMap_invariant :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp
        data.signAction.inversion data.quotientMap)
      data.quotientMap := by
  rw [← data.quotientInvariant_map]
  exact data.quotientInvariant.invariant

theorem arithmetic_inclusion_injective :
    Function.Injective data.fundamentalGroupInclusion.arithmetic.hom :=
  data.fundamentalGroupInclusion.arithmetic.injective

theorem geometric_inclusion_injective :
    Function.Injective data.fundamentalGroupInclusion.geometric.hom :=
  data.fundamentalGroupInclusion.geometric.injective

end SignQuotientOrbicurveData

/--
A finite Galois subextension with solvable Galois group.

These are precisely the finite layers whose compositum is the maximal
solvable extension used in IUT I, Definition 3.1(b).
-/
def IsFiniteSolvableGaloisSubextension
    (k kbar : Type u)
    [Field k] [Field kbar] [Algebra k kbar]
    (E : IntermediateField k kbar) : Prop :=
  FiniteDimensional k E ∧
    IsGalois k E ∧
      IsSolvable (E ≃ₐ[k] E)

/--
The maximal solvable extension of `k` inside `kbar`: the compositum of all
finite Galois subextensions with solvable Galois group.
-/
def maximalSolvableExtension
    (k kbar : Type u)
    [Field k] [Field kbar] [Algebra k kbar] :
    IntermediateField k kbar :=
  sSup {E | IsFiniteSolvableGaloisSubextension k kbar E}

namespace maximalSolvableExtension

variable {k kbar : Type u}
variable [Field k] [Field kbar] [Algebra k kbar]

/-- Every finite solvable Galois layer lies in the maximal solvable extension. -/
theorem contains
    (E : IntermediateField k kbar)
    (hE : IsFiniteSolvableGaloisSubextension k kbar E) :
    E ≤ maximalSolvableExtension k kbar :=
  le_sSup hE

end maximalSolvableExtension

/--
A concrete field-of-moduli witness for a once-punctured elliptic curve whose
puncture is the origin: `j` descends to `Fmod`, and the descended value
generates `Fmod` over `Q`.
-/
structure EllipticFieldOfModuliData
    (Fmod F : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Algebra Fmod F]
    (curve : PuncturedEllipticCurve F) where
  puncture_eq_origin : curve.puncture = 0
  jModuli : Fmod
  algebraMap_jModuli :
    algebraMap Fmod F jModuli = curve.jInvariant
  generatesOverRat :
    Algebra.adjoin ℚ ({jModuli} : Set Fmod) = ⊤

namespace EllipticFieldOfModuliData

variable {Fmod F : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Algebra Fmod F]
variable {curve : PuncturedEllipticCurve F}

/-- The canonical `Q`-embedding of `Fmod` into its chosen algebraic closure. -/
noncomputable def moduliEmbedding
    (_data : EllipticFieldOfModuliData Fmod F curve) :
    Fmod →ₐ[ℚ] AlgebraicClosure Fmod :=
  (algebraMap Fmod (AlgebraicClosure Fmod)).toRatAlgHom

/-- The descended `j`-invariant in the chosen algebraic closure of `Fmod`. -/
noncomputable def jModuliInClosure
    (data : EllipticFieldOfModuliData Fmod F curve) :
    AlgebraicClosure Fmod :=
  algebraMap Fmod (AlgebraicClosure Fmod) data.jModuli

/--
The field generated by the geometric isomorphism class of the elliptic curve.
Over an algebraically closed field, equality of `j` is equivalent to a
Weierstrass change of variables by `exists_variableChange_of_j_eq`.
-/
noncomputable def jModuliField
    (data : EllipticFieldOfModuliData Fmod F curve) :
    IntermediateField ℚ (AlgebraicClosure Fmod) :=
  IntermediateField.adjoin ℚ {data.jModuliInClosure}

/--
The chosen copy of `Fmod` in its algebraic closure is exactly the field
generated by the geometric `j`-class.
-/
theorem moduliEmbedding_fieldRange_eq_jModuliField
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.moduliEmbedding.fieldRange = data.jModuliField := by
  have htop :
      IntermediateField.adjoin ℚ ({data.jModuli} : Set Fmod) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra]
    exact data.generatesOverRat
  rw [AlgHom.fieldRange_eq_map, ← htop, IntermediateField.adjoin_map]
  simp [moduliEmbedding, jModuliField, jModuliInClosure]

/-- Automorphisms of `Fmod-bar/Q` preserving the geometric `j`-class. -/
noncomputable def jAutomorphismStabilizer
    (data : EllipticFieldOfModuliData Fmod F curve) :
    Subgroup
      (AlgebraicClosure Fmod ≃ₐ[ℚ] AlgebraicClosure Fmod) :=
  data.jModuliField.fixingSubgroup

/-- The field fixed by all automorphisms preserving the geometric `j`-class. -/
noncomputable def automorphismFixedModuliField
    (data : EllipticFieldOfModuliData Fmod F curve) :
    IntermediateField ℚ (AlgebraicClosure Fmod) :=
  IntermediateField.fixedField data.jAutomorphismStabilizer

theorem automorphismFixedModuliField_eq_jModuliField
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.automorphismFixedModuliField = data.jModuliField := by
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure Fmod) :=
    Algebra.IsAlgebraic.trans ℚ Fmod (AlgebraicClosure Fmod)
  letI : Normal ℚ (AlgebraicClosure Fmod) :=
    { splits' := fun _ => IsAlgClosed.splits _ }
  letI : IsGalois ℚ (AlgebraicClosure Fmod) := ⟨⟩
  exact InfiniteGalois.fixedField_fixingSubgroup data.jModuliField

/-- The canonical copy of `Fmod` in the selected algebraic closure of `F`. -/
noncomputable def moduliEmbeddingInFbar
    (_data : EllipticFieldOfModuliData Fmod F curve) :
    Fmod →ₐ[ℚ] AlgebraicClosure F :=
  (algebraMap Fmod (AlgebraicClosure F)).toRatAlgHom

/-- The descended `j`-invariant in the selected `Fbar`. -/
noncomputable def jModuliInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    AlgebraicClosure F :=
  algebraMap Fmod (AlgebraicClosure F) data.jModuli

/-- The field generated by the geometric `j`-class inside the selected `Fbar`. -/
noncomputable def jModuliFieldInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    IntermediateField ℚ (AlgebraicClosure F) :=
  IntermediateField.adjoin ℚ {data.jModuliInFbar}

/-- The embedded `Fmod` is exactly the `j`-generated field inside `Fbar`. -/
theorem moduliEmbeddingInFbar_fieldRange_eq_jModuliFieldInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.moduliEmbeddingInFbar.fieldRange =
      data.jModuliFieldInFbar := by
  have htop :
      IntermediateField.adjoin ℚ ({data.jModuli} : Set Fmod) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra]
    exact data.generatesOverRat
  rw [AlgHom.fieldRange_eq_map, ← htop, IntermediateField.adjoin_map]
  simp [moduliEmbeddingInFbar, jModuliFieldInFbar, jModuliInFbar]

/-- Automorphisms of the selected `Fbar/Q` preserving the geometric `j`-class. -/
noncomputable def jAutomorphismStabilizerInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    Subgroup
      (AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :=
  data.jModuliFieldInFbar.fixingSubgroup

/-- The fixed field in `Fbar` of the geometric-`j` stabilizer. -/
noncomputable def automorphismFixedModuliFieldInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    IntermediateField ℚ (AlgebraicClosure F) :=
  IntermediateField.fixedField
    data.jAutomorphismStabilizerInFbar

theorem automorphismFixedModuliFieldInFbar_eq_jModuliFieldInFbar
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.automorphismFixedModuliFieldInFbar =
      data.jModuliFieldInFbar := by
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)
  letI : Normal ℚ (AlgebraicClosure F) :=
    { splits' := fun _ => IsAlgClosed.splits _ }
  letI : IsGalois ℚ (AlgebraicClosure F) := ⟨⟩
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      data.jModuliFieldInFbar

/-- The geometric Weierstrass curve over the selected algebraic closure `Fbar`. -/
noncomputable def geometricCurveInFbar
    (_data : EllipticFieldOfModuliData Fmod F curve) :
    WeierstrassCurve (AlgebraicClosure F) :=
  curve.curve.baseChange (AlgebraicClosure F)

/-- The conjugate of the geometric curve by a `Q`-automorphism of `Fbar`. -/
noncomputable def conjugateGeometricCurve
    (data : EllipticFieldOfModuliData Fmod F curve)
    (sigma :
      AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
    WeierstrassCurve (AlgebraicClosure F) :=
  data.geometricCurveInFbar.map sigma.toRingEquiv.toRingHom

noncomputable instance geometricCurveInFbar_isElliptic
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.geometricCurveInFbar.IsElliptic := by
  unfold geometricCurveInFbar WeierstrassCurve.baseChange
  infer_instance

noncomputable instance conjugateGeometricCurve_isElliptic
    (data : EllipticFieldOfModuliData Fmod F curve)
    (sigma :
      AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
    (data.conjugateGeometricCurve sigma).IsElliptic := by
  unfold conjugateGeometricCurve
  infer_instance

theorem geometricCurveInFbar_j
    (data : EllipticFieldOfModuliData Fmod F curve) :
    data.geometricCurveInFbar.j =
      data.jModuliInFbar := by
  letI :
      (curve.curve.baseChange
        (AlgebraicClosure F)).IsElliptic := by
    unfold WeierstrassCurve.baseChange
    infer_instance
  change
    (curve.curve.baseChange (AlgebraicClosure F)).j =
      data.jModuliInFbar
  unfold WeierstrassCurve.baseChange
  rw [WeierstrassCurve.map_j]
  change
    algebraMap F (AlgebraicClosure F) curve.jInvariant =
      algebraMap Fmod (AlgebraicClosure F) data.jModuli
  rw [← data.algebraMap_jModuli]
  exact
    (IsScalarTower.algebraMap_apply
      Fmod F (AlgebraicClosure F) data.jModuli).symm

theorem conjugateGeometricCurve_j
    (data : EllipticFieldOfModuliData Fmod F curve)
    (sigma :
      AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
    (data.conjugateGeometricCurve sigma).j =
      sigma data.jModuliInFbar := by
  change
    (data.geometricCurveInFbar.map
      sigma.toRingEquiv.toRingHom).j =
        sigma data.jModuliInFbar
  rw [WeierstrassCurve.map_j,
    data.geometricCurveInFbar_j]
  rfl

omit [NumberField F] in
theorem weierstrass_j_eq_of_eq
    {E E' : WeierstrassCurve (AlgebraicClosure F)}
    [E.IsElliptic] [E'.IsElliptic]
    (h : E = E') :
    E.j = E'.j := by
  subst E'
  rfl

/--
Fixing the descended `j`-value is equivalent to an actual geometric
Weierstrass isomorphism between the curve and its Galois conjugate.
-/
theorem fixes_jModuliInFbar_iff_variableChange
    (data : EllipticFieldOfModuliData Fmod F curve)
    (sigma :
      AlgebraicClosure F ≃ₐ[ℚ] AlgebraicClosure F) :
    sigma data.jModuliInFbar = data.jModuliInFbar ↔
      ∃ C : WeierstrassCurve.VariableChange
          (AlgebraicClosure F),
        C • data.geometricCurveInFbar =
          data.conjugateGeometricCurve sigma := by
  constructor
  · intro hfix
    apply WeierstrassCurve.exists_variableChange_of_j_eq
    rw [data.geometricCurveInFbar_j,
      data.conjugateGeometricCurve_j, hfix]
  · rintro ⟨C, hC⟩
    have hj :
        (C • data.geometricCurveInFbar).j =
          (data.conjugateGeometricCurve sigma).j :=
      weierstrass_j_eq_of_eq hC
    rw [WeierstrassCurve.variableChange_j,
      data.geometricCurveInFbar_j,
      data.conjugateGeometricCurve_j] at hj
    exact hj.symm

/--
The source's `Fsol`, formed inside the chosen algebraic closure of `F`, as in
IUT I, Definition 3.1(b).
-/
noncomputable def fsol
    (_data : EllipticFieldOfModuliData Fmod F curve) :
    IntermediateField Fmod (AlgebraicClosure F) :=
  maximalSolvableExtension Fmod (AlgebraicClosure F)

theorem finiteSolvableGalois_le_fsol
    (data : EllipticFieldOfModuliData Fmod F curve)
    (E : IntermediateField Fmod (AlgebraicClosure F))
    (hE :
      IsFiniteSolvableGaloisSubextension
        Fmod (AlgebraicClosure F) E) :
    E ≤ data.fsol :=
  maximalSolvableExtension.contains E hE

end EllipticFieldOfModuliData

/--
Scheme realization of a punctured Weierstrass elliptic curve.

The open curve is not an identifier: it is the restriction to the open
complement of the image of the origin section. The point equivalence ties the
chosen scheme realization to mathlib's Weierstrass projective points.
-/
structure PuncturedEllipticSchemeRealization
    (F : Type u) [Field F]
    (curve : PuncturedEllipticCurve F) where
  ellipticScheme : SchemeOverField F
  origin :
    Spec(F) ⟶ ellipticScheme.left
  origin_is_section :
    origin ≫ ellipticScheme.hom = 𝟙 (Spec(F))
  rationalPointEquiv :
    (Spec(F) ⟶ ellipticScheme.left) ≃
      curve.curve.toProjective.Point
  origin_eq_puncture :
    rationalPointEquiv origin = curve.puncture
  origin_range_closed :
    IsClosed (Set.range origin.base)
  puncturedOpen : ellipticScheme.left.Opens
  puncturedOpen_carrier :
    (puncturedOpen : Set ellipticScheme.left) =
      (Set.range origin.base)ᶜ

namespace PuncturedEllipticSchemeRealization

variable {F : Type u} [Field F]
variable {curve : PuncturedEllipticCurve F}
variable (realization :
  PuncturedEllipticSchemeRealization F curve)

/-- The actual once-punctured elliptic curve over `Spec(F)`. -/
noncomputable def puncturedScheme :
    SchemeOverField F :=
  Over.mk
    (realization.puncturedOpen.ι ≫
      realization.ellipticScheme.hom)

/-- Its open immersion into the ambient elliptic scheme. -/
noncomputable def openImmersion :
    realization.puncturedScheme ⟶
      realization.ellipticScheme :=
  Over.homMk realization.puncturedOpen.ι rfl

instance openImmersion_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      realization.openImmersion.left :=
  by
    change AlgebraicGeometry.IsOpenImmersion
      realization.puncturedOpen.ι
    infer_instance

theorem carrier_eq_origin_complement :
    (realization.puncturedOpen :
      Set realization.ellipticScheme.left) =
        (Set.range realization.origin.base)ᶜ :=
  realization.puncturedOpen_carrier

end PuncturedEllipticSchemeRealization

/--
The category-valued Yoneda functor represented by a scheme over `F`.

Its value at `U` is the discrete category of morphisms `U -> scheme`; its maps
are precomposition. Promoting this functor to a pseudofunctor supplies the
identity and composition coherences required of a stack presentation.
-/
noncomputable def schemeRepresentableFiberFunctor
    (F : Type u) [Field F]
    (scheme : SchemeOverField F) :
    (SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj U :=
    Cat.of (Discrete (Opposite.unop U ⟶ scheme))
  map {U V} f :=
    (Discrete.functor
      (fun P : Opposite.unop U ⟶ scheme =>
        Discrete.mk (f.unop ≫ P))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext
      (fun P => by
        apply Discrete.ext
        simp)
      (by
        intro X Y f
        exact
          @Subsingleton.elim _
            (Discrete.instSubsingletonDiscreteHom _ _) _ _)
  map_comp f g := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext
      (fun P => by
        apply Discrete.ext
        simp [Category.assoc])
      (by
        intro X Y f
        exact
          @Subsingleton.elim _
            (Discrete.instSubsingletonDiscreteHom _ _) _ _)

/-- The representable category-valued pseudofunctor attached to `scheme`. -/
noncomputable def schemeRepresentableEtalePseudofunctor
    (F : Type u) [Field F]
    (scheme : SchemeOverField F) :
    EtaleStackPseudofunctor F :=
  (schemeRepresentableFiberFunctor F scheme).toPseudofunctor'

/--
A coherent presentation of an etale stack by a scheme over `F`.

Representability is a single bicategorical equivalence with the actual
Yoneda-style pseudofunctor. Thus pullback naturality and its identity and
composition laws are carried by strong transformations, rather than supplied
as unrelated objectwise witnesses.
-/
structure SchemeEtaleStackPresentation
    (F : Type u) [Field F]
    (scheme : SchemeOverField F)
    (stack : EtaleStackOverField F) where
  equivalence :
    Bicategory.Equivalence
      stack.fiber
      (schemeRepresentableEtalePseudofunctor F scheme)

namespace SchemeEtaleStackPresentation

variable {F : Type u} [Field F]
variable {scheme : SchemeOverField F}
variable {stack : EtaleStackOverField F}

/-- The component functor from a presented stack fiber to its functor of points. -/
noncomputable def fiberFunctor
    (presentation :
      SchemeEtaleStackPresentation F scheme stack)
    (U : (SchemeOverField F)ᵒᵖ) :
    stack.fiber.obj (LocallyDiscrete.mk U) ⥤
      Discrete (Opposite.unop U ⟶ scheme) :=
  (presentation.equivalence.hom.app
    (LocallyDiscrete.mk U)).toFunctor

end SchemeEtaleStackPresentation

/--
Geometric realization of the `-1` action on a punctured elliptic scheme.

The scheme involution preserves the punctured open, squares to the identity,
and induces group inverse on every `F`-rational point after inclusion into the
ambient Weierstrass scheme.
-/
structure PuncturedEllipticInversionRealization
    (F : Type u) [Field F]
    {curve : PuncturedEllipticCurve F}
    (realization :
      PuncturedEllipticSchemeRealization F curve) where
  inversion :
    realization.puncturedScheme ⟶
      realization.puncturedScheme
  inversion_involutive :
    inversion ≫ inversion =
      𝟙 realization.puncturedScheme
  rationalPoint_inversion :
    ∀ P : Spec(F) ⟶ realization.puncturedScheme.left,
      realization.rationalPointEquiv
          (P ≫ inversion.left ≫
            realization.openImmersion.left) =
        -realization.rationalPointEquiv
          (P ≫ realization.openImmersion.left)

/--
The source-native replacement for the curve/moduli portion of
IUT I, Definition 3.1(b).
-/
structure SourceThetaCurveModuliData
    (Fmod F : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Algebra Fmod F] where
  xF : PuncturedEllipticCurve F
  schemeRealization :
    PuncturedEllipticSchemeRealization F xF
  schemeInversion :
    PuncturedEllipticInversionRealization F schemeRealization
  fieldOfModuli : EllipticFieldOfModuliData Fmod F xF
  stableReduction : xF.HasStableReductionEverywhere
  torsion23Rational : xF.Torsion23Rational
  signQuotient : SignQuotientOrbicurveData F xF
  xStackPresentation :
    SchemeEtaleStackPresentation F
      schemeRealization.puncturedScheme
      signQuotient.xF.stack
  signInversionCompatibility :
    ∀ U : (SchemeOverField F)ᵒᵖ,
      (signQuotient.signAction.inversion.app
          (LocallyDiscrete.mk U)).toFunctor ⋙
          (xStackPresentation.fiberFunctor U) ≅
        (xStackPresentation.fiberFunctor U) ⋙
          Discrete.functor
            (fun P :
                Opposite.unop U ⟶
                  schemeRealization.puncturedScheme =>
              Discrete.mk (P ≫ schemeInversion.inversion))
  absoluteGalois_eq :
    signQuotient.absoluteGalois =
      AbsoluteGaloisProfinite F

/--
The canonical scalar extension of a once-punctured elliptic curve whose
puncture is the origin.

The target is constructed from mathlib's actual Weierstrass base change; it is
not an independently supplied curve. The distinguished puncture is the base
changed identity section, hence is again the origin.
-/
noncomputable def PuncturedEllipticCurve.baseChangeOrigin
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : PuncturedEllipticCurve F) :
    PuncturedEllipticCurve K where
  curve := X.curve.baseChange K
  isElliptic := by
    unfold WeierstrassCurve.baseChange
    infer_instance
  puncture := 0

/--
A certificate that scalar extension applies to the source once-punctured curve.

Unlike the former interface, this structure contains no arbitrary target curve:
`result` below is definitionally the canonical Weierstrass base change.
-/
structure PuncturedEllipticCurveScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : PuncturedEllipticCurve F) where
  source_puncture_eq_origin : X.puncture = 0

namespace PuncturedEllipticCurveScalarExtension

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {X : PuncturedEllipticCurve F}

/-- The scalar-extended curve, constructed rather than supplied. -/
noncomputable def result
    (_extension : PuncturedEllipticCurveScalarExtension F K X) :
    PuncturedEllipticCurve K :=
  X.baseChangeOrigin F K

@[simp]
theorem curve_eq_baseChange
    (extension : PuncturedEllipticCurveScalarExtension F K X) :
    extension.result.curve = X.curve.baseChange K :=
  rfl

@[simp]
theorem result_puncture_eq_origin
    (extension : PuncturedEllipticCurveScalarExtension F K X) :
    extension.result.puncture = 0 :=
  rfl

end PuncturedEllipticCurveScalarExtension

/--
The `K`-core `X_K -> C_K` obtained by scalar extension from `X_F -> C_F`.
-/
structure SourceThetaKCoreData
    (F K : Type u) [Field F] [Field K] [CharZero K] [Algebra F K]
    (curve : PuncturedEllipticCurve F)
    (fOrbicurves : SignQuotientOrbicurveData F curve) where
  curveExtension :
    PuncturedEllipticCurveScalarExtension F K curve
  xStackExtension :
    OrbicurveScalarExtension F K fOrbicurves.xF
  cStackExtension :
    OrbicurveScalarExtension F K fOrbicurves.cF
  orbicurves :
    SignQuotientOrbicurveData K curveExtension.result
  xK_eq_scalarExtension :
    orbicurves.xF = xStackExtension.result
  cK_eq_scalarExtension :
    orbicurves.cF = cStackExtension.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension F K
      xStackExtension cStackExtension
      fOrbicurves.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        xK_eq_scalarExtension cK_eq_scalarExtension
        orbicurves.quotientMap =
      quotientMapExtension.result
  absoluteGalois_eq :
    orbicurves.absoluteGalois =
      AbsoluteGaloisProfinite K

/-- The completed local field attached to a finite place of a number field. -/
abbrev ThetaFinitePlace.Completion
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :=
  (ThetaFinitePlace.underlyingPrime v).adicCompletion K

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance ThetaFinitePlace.completionCharZero
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    CharZero (ThetaFinitePlace.Completion v) :=
  Algebra.charZero_of_charZero K (ThetaFinitePlace.Completion v)

/--
A Tate parameter at a selected bad finite place.

The parameter is an actual nonzero element of the completed local field, and
its valuation is strictly below one. Its positive local height is derived
below from the discrete valuation exponent.
-/
noncomputable def ThetaFinitePlace.tateParameterUnit
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (q : ThetaFinitePlace.Completion v)
    (q_ne_zero : q ≠ 0) :
    (AlgebraicClosure
      (ThetaFinitePlace.Completion v))ˣ :=
  Units.map
    (algebraMap
      (ThetaFinitePlace.Completion v)
      (AlgebraicClosure
        (ThetaFinitePlace.Completion v))).toMonoidHom
    (Units.mk0 q q_ne_zero)

structure ThetaTateParameterData
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (localCurve :
      PuncturedEllipticCurve
        (ThetaFinitePlace.Completion v)) where
  q : ThetaFinitePlace.Completion v
  q_ne_zero : q ≠ 0
  valuation_lt_one :
    (Valued.v q : WithZero (Multiplicative ℤ)) < 1
  uniformization :
    letI : localCurve.curve.IsElliptic :=
      localCurve.isElliptic
    ((AlgebraicClosure
        (ThetaFinitePlace.Completion v))ˣ ⧸
      Subgroup.zpowers
        (ThetaFinitePlace.tateParameterUnit
          v q q_ne_zero)) ≃*
      Multiplicative
        localCurve.AlgebraicClosurePoint
  galoisEquivariant :
    letI : localCurve.curve.IsElliptic :=
      localCurve.isElliptic
    ∀ (sigma :
        AlgebraicClosure
            (ThetaFinitePlace.Completion v) ≃ₐ[
          ThetaFinitePlace.Completion v]
        AlgebraicClosure
          (ThetaFinitePlace.Completion v))
      (x :
        (AlgebraicClosure
          (ThetaFinitePlace.Completion v))ˣ),
      uniformization
          (QuotientGroup.mk
            (Units.map
              sigma.toRingEquiv.toMonoidHom x)) =
        Multiplicative.ofAdd
          (localCurve.galoisActionOnPoint sigma
            (uniformization
              (QuotientGroup.mk x)).toAdd)

namespace ThetaTateParameterData

variable
    {K : Type u} [Field K] [NumberField K]
    {v : NumberField.FinitePlace K}
    {localCurve :
      PuncturedEllipticCurve
        (ThetaFinitePlace.Completion v)}

/-- The nonzero valuation of a Tate parameter. -/
theorem valuation_ne_zero
    (parameter : ThetaTateParameterData v localCurve) :
    (Valued.v parameter.q :
      WithZero (Multiplicative ℤ)) ≠ 0 := by
  intro h
  exact parameter.q_ne_zero
    (((Valued.v :
      Valuation (ThetaFinitePlace.Completion v)
        (WithZero (Multiplicative ℤ))).map_eq_zero_iff).mp h)

/--
The positive local height: minus the additive exponent of the multiplicative
discrete valuation.
-/
noncomputable def order
    (parameter : ThetaTateParameterData v localCurve) : ℕ :=
  Int.toNat
    (-Multiplicative.toAdd
      (WithZero.unzero parameter.valuation_ne_zero))

theorem order_pos
    (parameter : ThetaTateParameterData v localCurve) :
    0 < parameter.order := by
  have exponent_neg :
      Multiplicative.toAdd
          (WithZero.unzero parameter.valuation_ne_zero) < 0 := by
    exact
      WithZero.toAdd_unzero_lt_of_lt_ofAdd
        parameter.valuation_ne_zero
        parameter.valuation_lt_one
  rw [order]
  apply Nat.pos_of_ne_zero
  intro h
  have nonpositive :
      -Multiplicative.toAdd
          (WithZero.unzero parameter.valuation_ne_zero) ≤ 0 :=
    Int.toNat_eq_zero.mp h
  omega

end ThetaTateParameterData

/--
The literal stabilizer of a prolongation of a place to an algebraic closure.

The global profinite group is identified with mathlib's Krull-topological
absolute Galois group, and the closed subgroup is characterized elementwise as
the stabilizer of the chosen prolongation.
-/
structure AbsoluteGaloisPlaceStabilizerData
    (K : Type u) [Field K] [CharZero K]
    (basePlace : AbsoluteValue K ℝ)
    (globalGroup : ProfiniteGrp.{u}) where
  globalIdentification :
    globalGroup ≅ AbsoluteGaloisProfinite K
  prolongation :
    AbsoluteValue (AlgebraicClosure K) ℝ
  prolongation_restricts :
    prolongation.comp
        (algebraMap K (AlgebraicClosure K)).injective =
      basePlace
  stabilizer :
    ClosedSubgroup globalGroup
  mem_stabilizer_iff :
    ∀ g : globalGroup,
      g ∈ stabilizer ↔
        prolongation.comp
            ((globalIdentification.hom g :
                AlgebraicClosure K ≃ₐ[K]
                  AlgebraicClosure K).toRingEquiv.toRingHom.injective) =
          prolongation

/--
A completed local absolute Galois group identified with a closed decomposition
subgroup of the global absolute Galois group.
-/
structure ProfiniteDecompositionGroupData
    (localGroup globalGroup : ProfiniteGrp.{u}) where
  subgroup : ClosedSubgroup globalGroup
  localEquiv :
    localGroup ≅ closedSubgroupProfiniteGrp subgroup
  embedding :
    ProfiniteEmbedding localGroup globalGroup
  embedding_eq :
    embedding.hom =
      localEquiv.hom ≫
        (closedSubgroupProfiniteInclusion subgroup).hom

/-- Scalar extension of the `K`-core orbicurves to a selected finite completion. -/
structure SourceThetaFiniteLocalCoreData
    (K : Type u) [Field K] [NumberField K]
    (curve : PuncturedEllipticCurve K)
    (kOrbicurves : SignQuotientOrbicurveData K curve)
    (v : NumberField.FinitePlace K) where
  curveLocal :
    PuncturedEllipticCurveScalarExtension K
      (ThetaFinitePlace.Completion v) curve
  xLocal :
    OrbicurveScalarExtension K
      (ThetaFinitePlace.Completion v) kOrbicurves.xF
  cLocal :
    OrbicurveScalarExtension K
      (ThetaFinitePlace.Completion v) kOrbicurves.cF
  orbicurves :
    SignQuotientOrbicurveData
      (ThetaFinitePlace.Completion v) curveLocal.result
  x_eq_scalarExtension :
    orbicurves.xF = xLocal.result
  c_eq_scalarExtension :
    orbicurves.cF = cLocal.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension K
      (ThetaFinitePlace.Completion v)
      xLocal cLocal kOrbicurves.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        x_eq_scalarExtension c_eq_scalarExtension
        orbicurves.quotientMap =
      quotientMapExtension.result
  absoluteGalois_eq :
    orbicurves.absoluteGalois =
      AbsoluteGaloisProfinite
        (ThetaFinitePlace.Completion v)
  decompositionGroup :
    ProfiniteDecompositionGroupData
      orbicurves.absoluteGalois
      kOrbicurves.absoluteGalois
  placeStabilizer :
    AbsoluteGaloisPlaceStabilizerData K v.1
      kOrbicurves.absoluteGalois
  decompositionGroup_subgroup_eq :
    decompositionGroup.subgroup =
      placeStabilizer.stabilizer
  xFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      orbicurves.xFundamentalGroups.geometric.group
      orbicurves.xFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      kOrbicurves.xFundamentalGroups.geometric.group
      kOrbicurves.xFundamentalGroups.arithmetic.group
      kOrbicurves.absoluteGalois
      orbicurves.xFundamentalGroups.exactSequence
      kOrbicurves.xFundamentalGroups.exactSequence
  cFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      orbicurves.cFundamentalGroups.geometric.group
      orbicurves.cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      kOrbicurves.cFundamentalGroups.geometric.group
      kOrbicurves.cFundamentalGroups.arithmetic.group
      kOrbicurves.absoluteGalois
      orbicurves.cFundamentalGroups.exactSequence
      kOrbicurves.cFundamentalGroups.exactSequence
  xDiagram_galois_eq :
    xFundamentalGroupDiagram.galois =
      decompositionGroup.embedding
  cDiagram_galois_eq :
    cFundamentalGroupDiagram.galois =
      decompositionGroup.embedding

/-- The completed archimedean field attached to an infinite place. -/
abbrev ThetaInfinitePlace.Completion
    {K : Type u} [Field K]
    (v : NumberField.InfinitePlace K) :=
  v.Completion

/-- An archimedean completion of a number field has characteristic zero. -/
noncomputable instance ThetaInfinitePlace.completionCharZero
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    CharZero (ThetaInfinitePlace.Completion v) :=
  Algebra.charZero_of_charZero K
    (ThetaInfinitePlace.Completion v)

/--
Scalar extension of the `K`-core orbicurves to a selected archimedean
completion, with the local-to-global fundamental-group diagrams from
Definition 3.1(e).
-/
structure SourceThetaInfiniteLocalCoreData
    (K : Type u) [Field K] [NumberField K]
    (curve : PuncturedEllipticCurve K)
    (kOrbicurves : SignQuotientOrbicurveData K curve)
    (v : NumberField.InfinitePlace K) where
  curveLocal :
    PuncturedEllipticCurveScalarExtension K
      (ThetaInfinitePlace.Completion v) curve
  xLocal :
    OrbicurveScalarExtension K
      (ThetaInfinitePlace.Completion v) kOrbicurves.xF
  cLocal :
    OrbicurveScalarExtension K
      (ThetaInfinitePlace.Completion v) kOrbicurves.cF
  orbicurves :
    SignQuotientOrbicurveData
      (ThetaInfinitePlace.Completion v) curveLocal.result
  x_eq_scalarExtension :
    orbicurves.xF = xLocal.result
  c_eq_scalarExtension :
    orbicurves.cF = cLocal.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension K
      (ThetaInfinitePlace.Completion v)
      xLocal cLocal kOrbicurves.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        x_eq_scalarExtension c_eq_scalarExtension
        orbicurves.quotientMap =
      quotientMapExtension.result
  absoluteGalois_eq :
    orbicurves.absoluteGalois =
      AbsoluteGaloisProfinite
        (ThetaInfinitePlace.Completion v)
  decompositionGroup :
    ProfiniteDecompositionGroupData
      orbicurves.absoluteGalois
      kOrbicurves.absoluteGalois
  placeStabilizer :
    AbsoluteGaloisPlaceStabilizerData K v.1
      kOrbicurves.absoluteGalois
  decompositionGroup_subgroup_eq :
    decompositionGroup.subgroup =
      placeStabilizer.stabilizer
  xFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      orbicurves.xFundamentalGroups.geometric.group
      orbicurves.xFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      kOrbicurves.xFundamentalGroups.geometric.group
      kOrbicurves.xFundamentalGroups.arithmetic.group
      kOrbicurves.absoluteGalois
      orbicurves.xFundamentalGroups.exactSequence
      kOrbicurves.xFundamentalGroups.exactSequence
  cFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      orbicurves.cFundamentalGroups.geometric.group
      orbicurves.cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      kOrbicurves.cFundamentalGroups.geometric.group
      kOrbicurves.cFundamentalGroups.arithmetic.group
      kOrbicurves.absoluteGalois
      orbicurves.cFundamentalGroups.exactSequence
      kOrbicurves.cFundamentalGroups.exactSequence
  xDiagram_galois_eq :
    xFundamentalGroupDiagram.galois =
      decompositionGroup.embedding
  cDiagram_galois_eq :
    cFundamentalGroupDiagram.galois =
      decompositionGroup.embedding

/--
The common scalar-extension diagram for a sign-quotient pair `X -> C`.

This isolates the part shared by finite and archimedean localizations and is
also the base-change datum used for the type-`(1,l-tors)` covers below.
-/
structure SignQuotientOrbicurveBaseChange
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    (globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve)
    (localOrbicurves :
      SignQuotientOrbicurveData L localCurve) where
  xExtension :
    OrbicurveScalarExtension K L globalOrbicurves.xF
  cExtension :
    OrbicurveScalarExtension K L globalOrbicurves.cF
  x_eq_scalarExtension :
    localOrbicurves.xF = xExtension.result
  c_eq_scalarExtension :
    localOrbicurves.cF = cExtension.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension K L
      xExtension cExtension globalOrbicurves.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        x_eq_scalarExtension c_eq_scalarExtension
        localOrbicurves.quotientMap =
      quotientMapExtension.result

namespace SourceThetaFiniteLocalCoreData

variable
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}

/-- The sign-quotient scalar-extension part of a finite local core. -/
def baseChange
    (localData :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v) :
    SignQuotientOrbicurveBaseChange K
      (ThetaFinitePlace.Completion v)
      kOrbicurves localData.orbicurves where
  xExtension := localData.xLocal
  cExtension := localData.cLocal
  x_eq_scalarExtension := localData.x_eq_scalarExtension
  c_eq_scalarExtension := localData.c_eq_scalarExtension
  quotientMapExtension := localData.quotientMapExtension
  quotientMap_eq_scalarExtension :=
    localData.quotientMap_eq_scalarExtension

end SourceThetaFiniteLocalCoreData

namespace SourceThetaInfiniteLocalCoreData

variable
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.InfinitePlace K}

/-- The sign-quotient scalar-extension part of an archimedean local core. -/
def baseChange
    (localData :
      SourceThetaInfiniteLocalCoreData
        K curve kOrbicurves v) :
    SignQuotientOrbicurveBaseChange K
      (ThetaInfinitePlace.Completion v)
      kOrbicurves localData.orbicurves where
  xExtension := localData.xLocal
  cExtension := localData.cLocal
  x_eq_scalarExtension := localData.x_eq_scalarExtension
  c_eq_scalarExtension := localData.c_eq_scalarExtension
  quotientMapExtension := localData.quotientMapExtension
  quotientMap_eq_scalarExtension :=
    localData.quotientMap_eq_scalarExtension

end SourceThetaInfiniteLocalCoreData

/--
The global group-theoretic construction imported by IUT I, Definition 3.1(d),
from Etale Theta, Definitions 2.1 and 2.3 and Proposition 2.2.

In particular, the class-two theta quotient `piTheta` and its rank-two
elliptic quotient `piEll` are distinct. The Lagrangian quotient and
Proposition 2.2 inversion splitting live on `piEll`, not on the original
arithmetic fundamental group or the class-two theta quotient.
-/
structure GlobalLTorsionCoverInput
    (l : PrimeGeFive)
    {F : Type u} [Field F]
    {curve : PuncturedEllipticCurve F}
    (orbicurves : SignQuotientOrbicurveData F curve) where
  piTheta : ProfiniteGrp.{u}
  piEll : ProfiniteGrp.{u}
  cuspTheta : ProfiniteGrp.{u}
  geometricRank :
    EtaleTheta.OncePuncturedEllipticThetaRealization
      l.value orbicurves.xFundamentalGroups.geometric.group
  arithmeticTheta :
    EtaleTheta.ArithmeticThetaQuotientData
      l.value
      orbicurves.xFundamentalGroups.geometric.group
      orbicurves.xFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      piTheta
  originalExact_eq :
    arithmeticTheta.originalExact =
      { inclusion :=
          orbicurves.xFundamentalGroups.exactSequence.inclusion.hom.toMonoidHom
        projection :=
          orbicurves.xFundamentalGroups.exactSequence.projection.hom.toMonoidHom
        inclusion_injective :=
          orbicurves.xFundamentalGroups.exactSequence.inclusion_injective
        projection_surjective :=
          orbicurves.xFundamentalGroups.exactSequence.projection_surjective
        exact :=
          orbicurves.xFundamentalGroups.exactSequence.exact }
  arithmeticThetaQuotientContinuous :
    Continuous arithmeticTheta.arithmeticQuotient
  arithmeticThetaInclusionContinuous :
    Continuous arithmeticTheta.quotientExact.inclusion
  arithmeticThetaProjectionContinuous :
    Continuous arithmeticTheta.quotientExact.projection
  arithmeticElliptic :
    EtaleTheta.ArithmeticEllipticQuotientData
      arithmeticTheta piEll
  arithmeticEllipticQuotientContinuous :
    Continuous arithmeticElliptic.quotient
  arithmeticEllipticInclusionContinuous :
    Continuous arithmeticElliptic.exact.inclusion
  arithmeticEllipticProjectionContinuous :
    Continuous arithmeticElliptic.exact.projection
  cuspSequence :
    EtaleTheta.CuspidalThetaSequence
      arithmeticTheta cuspTheta
  cuspInclusionContinuous :
    Continuous cuspSequence.exact.inclusion
  cuspProjectionContinuous :
    Continuous cuspSequence.exact.projection
  cuspIntoArithmeticContinuous :
    Continuous cuspSequence.intoArithmetic
  lagrangian :
    EtaleTheta.TypeOneLTorsionQuotient
      arithmeticTheta arithmeticElliptic cuspSequence
  profiniteLagrangian :
    EtaleTheta.ProfiniteLagrangianQuotient
      l.value piEll
  profiniteLagrangian_eq :
    profiniteLagrangian.toLagrangianQuotient =
      lagrangian.quotient
  inversion :
    EtaleTheta.InversionEigenspaceSplitting
      arithmeticTheta arithmeticElliptic cuspSequence lagrangian
  inversionContinuous :
    Continuous inversion.inversion
  inversionConjugationContinuous :
    ∀ p, Continuous (inversion.conjugation.action p)
  thetaRoot :
    EtaleTheta.ThetaRootSplittingData
      arithmeticTheta arithmeticElliptic cuspSequence
        lagrangian inversion
  thetaRootCuspQuotientContinuous :
    Continuous thetaRoot.cuspQuotient
  thetaRootGaloisSectionContinuous :
    Continuous thetaRoot.galoisSection
  thetaRootSubgroup_isOpen :
    IsOpen
      ((thetaRoot.thetaRootSubgroup :
          Subgroup piEll) :
        Set piEll)

namespace GlobalLTorsionCoverInput

variable {l : PrimeGeFive}
variable {F : Type u} [Field F]
variable {curve : PuncturedEllipticCurve F}
variable {orbicurves : SignQuotientOrbicurveData F curve}
variable (data : GlobalLTorsionCoverInput l orbicurves)

theorem cuspDecompositionGroup_in_cover :
    (data.arithmeticElliptic.quotient.comp
        data.cuspSequence.intoArithmetic).range ≤
      data.lagrangian.coverSubgroup :=
  data.lagrangian.cusp_decompositionGroup_le_coverSubgroup

theorem globalCoverSubgroup_isOpen :
    IsOpen
      ((data.lagrangian.coverSubgroup :
          Subgroup data.piEll) :
        Set data.piEll) := by
  have hsubgroup :
      data.profiniteLagrangian.coverSubgroup =
        data.lagrangian.coverSubgroup := by
    change
      data.profiniteLagrangian.toLagrangianQuotient.coverSubgroup =
        data.lagrangian.quotient.coverSubgroup
    rw [data.profiniteLagrangian_eq]
  rw [← hsubgroup]
  exact data.profiniteLagrangian.coverSubgroup_isOpen

theorem thetaRoot_contains_negativeEigenspaceImage :
    data.thetaRoot.negativeEigenspaceImage ≤
      data.thetaRoot.thetaRootSubgroup :=
  data.thetaRoot.negativeEigenspaceImage_le_thetaRootSubgroup

theorem thetaRoot_quotient_is_cusp :
    Nonempty
      (data.piEll ⧸
          data.thetaRoot.negativeEigenspaceImage ≃*
        data.cuspTheta) :=
  ⟨data.thetaRoot.quotientByNegativeEigenspaceEquivCusp⟩

/-- The negative eigenspace as a closed subgroup of the arithmetic elliptic group. -/
noncomputable def negativeEigenspaceClosedSubgroup :
    ClosedSubgroup data.piEll where
  toSubgroup := data.thetaRoot.negativeEigenspaceImage
  isClosed' := by
    change
      IsClosed
        {x : data.piEll |
          data.thetaRoot.cuspQuotient x = 1}
    exact
      isClosed_singleton.preimage
        data.thetaRootCuspQuotientContinuous

/-- The profinite geometric group of the theta-root cover. -/
noncomputable def negativeEigenspaceProfiniteGroup :
    ProfiniteGrp.{u} :=
  closedSubgroupProfiniteGrp
    data.negativeEigenspaceClosedSubgroup

/-- The theta-root subgroup as a closed subgroup of the arithmetic elliptic group. -/
noncomputable def thetaRootClosedSubgroup :
    ClosedSubgroup data.piEll where
  toSubgroup := data.thetaRoot.thetaRootSubgroup
  isClosed' :=
    Subgroup.isClosed_of_isOpen
      data.thetaRoot.thetaRootSubgroup
      data.thetaRootSubgroup_isOpen

/-- The profinite arithmetic group of the theta-root cover. -/
noncomputable def thetaRootProfiniteGroup :
    ProfiniteGrp.{u} :=
  closedSubgroupProfiniteGrp data.thetaRootClosedSubgroup

/-- The canonical open inclusion of the theta-root arithmetic group. -/
noncomputable def thetaRootInclusion :
    ProfiniteOpenEmbedding
      data.thetaRootProfiniteGroup data.piEll := by
  letI : IsTopologicalGroup data.thetaRootClosedSubgroup :=
    inferInstanceAs
      (IsTopologicalGroup
        data.thetaRootClosedSubgroup.toSubgroup)
  refine
    { hom :=
        (closedSubgroupProfiniteInclusion
          data.thetaRootClosedSubgroup).hom
      isOpenEmbedding := ?_ }
  exact
    data.thetaRootSubgroup_isOpen.isOpenEmbedding_subtypeVal

/-- The open cover subgroup inside the profinite arithmetic elliptic group. -/
def globalCoverClosedSubgroup :
    ClosedSubgroup data.piEll where
  toSubgroup := data.lagrangian.coverSubgroup
  isClosed' :=
    Subgroup.isClosed_of_isOpen
      data.lagrangian.coverSubgroup
      data.globalCoverSubgroup_isOpen

/-- The profinite arithmetic group of the finite Lagrangian cover. -/
def globalCoverProfiniteGroup :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.ofClosedSubgroup data.globalCoverClosedSubgroup

/-- The canonical open inclusion of the Lagrangian cover group. -/
def globalCoverInclusion :
    ProfiniteOpenEmbedding
      data.globalCoverProfiniteGroup data.piEll := by
  letI : IsTopologicalGroup data.globalCoverClosedSubgroup :=
    inferInstanceAs
      (IsTopologicalGroup
        data.globalCoverClosedSubgroup.toSubgroup)
  refine
    { hom :=
        (closedSubgroupProfiniteInclusion
          data.globalCoverClosedSubgroup).hom
      isOpenEmbedding := ?_ }
  exact
    data.globalCoverSubgroup_isOpen.isOpenEmbedding_subtypeVal

end GlobalLTorsionCoverInput

/-- An element normalizes the range of a profinite-group embedding. -/
def NormalizesProfiniteEmbeddingImage
    {source target : ProfiniteGrp.{u}}
    (embedding : ProfiniteOpenEmbedding source target)
    (element : target) : Prop :=
  ∀ x, ∃ y,
    element * embedding.hom x * element⁻¹ =
      embedding.hom y

/--
Stack realization of the type-`(1,l-tors)` and sign-quotient covers from
Etale Theta, Definition 2.1, including the full bicategorical pullback
universal property of the defining cover square.
-/
structure TypeOneLTorsionStackRealization
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    (groupData : GlobalLTorsionCoverInput l orbicurves) where
  xCover : HyperbolicOrbicurve K
  cCover : HyperbolicOrbicurve K
  xToBase : xCover.Hom orbicurves.xF
  cToBase : cCover.Hom orbicurves.cF
  signAction : OrbicurveSignAction xCover
  quotientMap : xCover.Hom cCover
  quotientInvariant :
    OrbicurveSignInvariantMorphism signAction cCover
  quotientInvariant_map :
    quotientInvariant.map = quotientMap
  quotientUniversal :
    OrbicurveSignQuotientWitness signAction quotientInvariant
  coverSquare :
    OrbicurveSquare xCover orbicurves.xF cCover orbicurves.cF
  coverSquare_toX :
    coverSquare.toX = xToBase
  coverSquare_toY :
    coverSquare.toY = quotientMap
  coverSquare_xToBase :
    coverSquare.xToBase = orbicurves.quotientMap
  coverSquare_yToBase :
    coverSquare.yToBase = cToBase
  cartesian :
    coverSquare.TwoPullbackWitness
  xFundamentalGroups :
    OrbicurveFundamentalGroupData
      xCover orbicurves.absoluteGalois
  cFundamentalGroups :
    OrbicurveFundamentalGroupData
      cCover orbicurves.absoluteGalois
  arithmeticGroup_identification :
    xFundamentalGroups.arithmetic.group ≅
      groupData.globalCoverProfiniteGroup
  xToCFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      xFundamentalGroups.geometric.group
      xFundamentalGroups.arithmetic.group
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      xFundamentalGroups.exactSequence
      cFundamentalGroups.exactSequence
  cToBaseFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      orbicurves.cFundamentalGroups.geometric.group
      orbicurves.cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      cFundamentalGroups.exactSequence
      orbicurves.cFundamentalGroups.exactSequence
  signFundamentalGroupAction :
    ProfiniteFundamentalExactSequenceAutomorphism
      xFundamentalGroups.exactSequence
  signGeometricAction_involutive :
    signFundamentalGroupAction.geometric.hom ≫
        signFundamentalGroupAction.geometric.hom =
      𝟙 xFundamentalGroups.geometric.group
  signArithmeticAction_involutive :
    signFundamentalGroupAction.arithmetic.hom ≫
        signFundamentalGroupAction.arithmetic.hom =
      𝟙 xFundamentalGroups.arithmetic.group
  signInvolution :
    cFundamentalGroups.geometric.group
  signInvolution_orderTwo :
    signInvolution ^ 2 = 1
  signInvolution_outside_xCover :
    signInvolution ∉
      Set.range
        xToCFundamentalGroupInclusion.geometric.hom
  signInvolution_normalizes_xCover :
    NormalizesProfiniteEmbeddingImage
      xToCFundamentalGroupInclusion.geometric
      signInvolution
  signGeometricAction_is_conjugation :
    ∀ g,
      xToCFundamentalGroupInclusion.geometric.hom
          (signFundamentalGroupAction.geometric.hom g) =
        signInvolution *
          xToCFundamentalGroupInclusion.geometric.hom g *
          signInvolution⁻¹
  signArithmeticAction_is_conjugation :
    ∀ g,
      xToCFundamentalGroupInclusion.arithmetic.hom
          (signFundamentalGroupAction.arithmetic.hom g) =
        cFundamentalGroups.exactSequence.inclusion
            signInvolution *
          xToCFundamentalGroupInclusion.arithmetic.hom g *
          (cFundamentalGroups.exactSequence.inclusion
            signInvolution)⁻¹
  cArithmetic_generated :
    Subgroup.closure
        (Set.range
            xToCFundamentalGroupInclusion.arithmetic.hom ∪
          {cFundamentalGroups.exactSequence.inclusion
            signInvolution}) =
      ⊤

/--
Scalar extension of a realized type-`(1,l-tors)` cover.

Besides the stack maps, this contains the local-to-global decomposition
embeddings of both cover fundamental groups and the induced embedding of the
rank-two elliptic quotient.  The final equation pins the latter to the actual
arithmetic fundamental-group map of the `X`-cover.
-/
structure TypeOneLTorsionStackScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    (baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves)
    (globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves)
    (globalStack :
      TypeOneLTorsionStackRealization
        l globalGroupData) where
  localGroupData :
    GlobalLTorsionCoverInput l localOrbicurves
  localStack :
    TypeOneLTorsionStackRealization l localGroupData
  xCoverExtension :
    OrbicurveScalarExtension K L globalStack.xCover
  cCoverExtension :
    OrbicurveScalarExtension K L globalStack.cCover
  xCover_eq_scalarExtension :
    localStack.xCover = xCoverExtension.result
  cCover_eq_scalarExtension :
    localStack.cCover = cCoverExtension.result
  xToBaseExtension :
    OrbicurveMorphismScalarExtension K L
      xCoverExtension baseChange.xExtension
      globalStack.xToBase
  xToBase_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        xCover_eq_scalarExtension
        baseChange.x_eq_scalarExtension
        localStack.xToBase =
      xToBaseExtension.result
  cToBaseExtension :
    OrbicurveMorphismScalarExtension K L
      cCoverExtension baseChange.cExtension
      globalStack.cToBase
  cToBase_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        cCover_eq_scalarExtension
        baseChange.c_eq_scalarExtension
        localStack.cToBase =
      cToBaseExtension.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension K L
      xCoverExtension cCoverExtension
      globalStack.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        xCover_eq_scalarExtension
        cCover_eq_scalarExtension
        localStack.quotientMap =
      quotientMapExtension.result
  galoisEmbedding :
    ProfiniteEmbedding
      localOrbicurves.absoluteGalois
      globalOrbicurves.absoluteGalois
  xFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localStack.xFundamentalGroups.geometric.group
      localStack.xFundamentalGroups.arithmetic.group
      localOrbicurves.absoluteGalois
      globalStack.xFundamentalGroups.geometric.group
      globalStack.xFundamentalGroups.arithmetic.group
      globalOrbicurves.absoluteGalois
      localStack.xFundamentalGroups.exactSequence
      globalStack.xFundamentalGroups.exactSequence
  cFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localStack.cFundamentalGroups.geometric.group
      localStack.cFundamentalGroups.arithmetic.group
      localOrbicurves.absoluteGalois
      globalStack.cFundamentalGroups.geometric.group
      globalStack.cFundamentalGroups.arithmetic.group
      globalOrbicurves.absoluteGalois
      localStack.cFundamentalGroups.exactSequence
      globalStack.cFundamentalGroups.exactSequence
  xDiagram_galois_eq :
    xFundamentalGroupDiagram.galois = galoisEmbedding
  cDiagram_galois_eq :
    cFundamentalGroupDiagram.galois = galoisEmbedding
  signGeometricAction_compatible :
    localStack.signFundamentalGroupAction.geometric.hom ≫
        xFundamentalGroupDiagram.geometric.hom =
      xFundamentalGroupDiagram.geometric.hom ≫
        globalStack.signFundamentalGroupAction.geometric.hom
  signArithmeticAction_compatible :
    localStack.signFundamentalGroupAction.arithmetic.hom ≫
        xFundamentalGroupDiagram.arithmetic.hom =
      xFundamentalGroupDiagram.arithmetic.hom ≫
        globalStack.signFundamentalGroupAction.arithmetic.hom
  signInvolution_compatible :
    cFundamentalGroupDiagram.geometric.hom
        localStack.signInvolution =
      globalStack.signInvolution
  ellipticEmbedding :
    ProfiniteEmbedding
      localGroupData.piEll globalGroupData.piEll
  lagrangianQuotient_compatible :
    ∀ p,
      globalGroupData.lagrangian.quotient.quotient
          (ellipticEmbedding.hom p) =
        localGroupData.lagrangian.quotient.quotient p
  xArithmeticGroup_compatible :
    ∀ p,
      globalGroupData.globalCoverInclusion.hom
          (globalStack.arithmeticGroup_identification.hom
            (xFundamentalGroupDiagram.arithmetic.hom p)) =
        ellipticEmbedding.hom
          (localGroupData.globalCoverInclusion.hom
            (localStack.arithmeticGroup_identification.hom p))

/--
The cuspidal atlas of a type-`(1,l-tors)` cover and its sign quotient.

Nonzero cusps of the `X`-cover are indexed by actual nonidentity elements of
the Lagrangian quotient; cusps of the `C`-cover are indexed by their inversion
orbits.  Each `X`-cusp is pinned to the corresponding conjugate of the base
cuspidal decomposition group, and the sign action carries the `q`-cusp to the
`q^-1`-cusp.  This is the group-theoretic boundary data needed by IUT I,
Definition 1.1, without pretending that a cusp is a point of the open stack.
-/
structure TypeOneCuspidalAtlas
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    (groupData : GlobalLTorsionCoverInput l orbicurves)
    (stack :
      TypeOneLTorsionStackRealization l groupData) where
  zeroXCusp :
    OrbicurveCuspidalDecompositionData
      stack.xFundamentalGroups
  zeroCCusp :
    OrbicurveCuspidalDecompositionData
      stack.cFundamentalGroups
  xCusps :
    EtaleTheta.NonzeroLabel
        (EtaleTheta.LTorsionLabel l.value) →
      OrbicurveCuspidalDecompositionData
        stack.xFundamentalGroups
  cCusps :
    EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel l.value) →
      OrbicurveCuspidalDecompositionData
        stack.cFundamentalGroups
  sheetRepresentative :
    EtaleTheta.NonzeroLabel
        (EtaleTheta.LTorsionLabel l.value) →
      groupData.piEll
  sheetRepresentative_label :
    ∀ q,
    groupData.lagrangian.quotient.quotient
        (sheetRepresentative q) = q
  xToCCusp :
    ∀ q,
      ProfiniteFundamentalExactSequenceEmbedding
        (xCusps q).inertia
        (xCusps q).decomposition
        orbicurves.absoluteGalois
        (cCusps (EtaleTheta.toSignLabel q)).inertia
        (cCusps
          (EtaleTheta.toSignLabel q)).decomposition
        orbicurves.absoluteGalois
        (xCusps q).exactSequence
        (cCusps
          (EtaleTheta.toSignLabel q)).exactSequence
  xToCCusp_galois_eq_id :
    ∀ q, (xToCCusp q).galois.hom =
      𝟙 orbicurves.absoluteGalois
  xToC_inertia_square :
    ∀ q,
      (xToCCusp q).geometric.hom ≫
          (cCusps
            (EtaleTheta.toSignLabel q)).ambientEmbedding.geometric.hom =
        (xCusps q).ambientEmbedding.geometric.hom ≫
          stack.xToCFundamentalGroupInclusion.geometric.hom
  xToC_decomposition_square :
    ∀ q,
      (xToCCusp q).arithmetic.hom ≫
          (cCusps
            (EtaleTheta.toSignLabel q)).ambientEmbedding.arithmetic.hom =
        (xCusps q).ambientEmbedding.arithmetic.hom ≫
          stack.xToCFundamentalGroupInclusion.arithmetic.hom
  baseCuspIdentification :
    ∀ q, (xCusps q).decomposition ≅ groupData.cuspTheta
  xCusp_is_sheetConjugate :
    ∀ q d,
      groupData.globalCoverInclusion.hom
          (stack.arithmeticGroup_identification.hom
            ((xCusps q).ambientEmbedding.arithmetic.hom d)) =
        sheetRepresentative q *
          groupData.arithmeticElliptic.quotient
            (groupData.cuspSequence.intoArithmetic
              ((baseCuspIdentification q).hom d)) *
          (sheetRepresentative q)⁻¹
  signCuspIsomorphism :
    ∀ q,
      ProfiniteFundamentalExactSequenceIsomorphism
        (xCusps q).exactSequence
        (xCusps q⁻¹).exactSequence
  signCusp_inertia_square :
    ∀ q,
      (signCuspIsomorphism q).geometric.hom ≫
          (xCusps q⁻¹).ambientEmbedding.geometric.hom =
        (xCusps q).ambientEmbedding.geometric.hom ≫
          stack.signFundamentalGroupAction.geometric.hom
  signCusp_decomposition_square :
    ∀ q,
      (signCuspIsomorphism q).arithmetic.hom ≫
          (xCusps q⁻¹).ambientEmbedding.arithmetic.hom =
        (xCusps q).ambientEmbedding.arithmetic.hom ≫
          stack.signFundamentalGroupAction.arithmetic.hom
  signModLAction :
    EtaleTheta.ModLEllipticAbelianization
        stack.xFundamentalGroups.geometric.group l.value ≃*
      EtaleTheta.ModLEllipticAbelianization
        stack.xFundamentalGroups.geometric.group l.value
  signModLAction_involutive :
    signModLAction.trans signModLAction =
      MulEquiv.refl
        (EtaleTheta.ModLEllipticAbelianization
          stack.xFundamentalGroups.geometric.group l.value)
  signModLAction_projection :
    ∀ g,
      signModLAction
          (EtaleTheta.modLEllipticProjection
            stack.xFundamentalGroups.geometric.group
            l.value g) =
        EtaleTheta.modLEllipticProjection
          stack.xFundamentalGroups.geometric.group
          l.value
          (stack.signFundamentalGroupAction.geometric.hom g)

/-- A selected nonzero cusp from the complete cuspidal atlas. -/
structure TypeOneNonzeroCusp
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    (groupData : GlobalLTorsionCoverInput l orbicurves)
    (stack :
      TypeOneLTorsionStackRealization l groupData) where
  atlas : TypeOneCuspidalAtlas l groupData stack
  origin :
    EtaleTheta.NonzeroLabel
      (EtaleTheta.LTorsionLabel l.value)

namespace TypeOneNonzeroCusp

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack)

/-- The chosen lift of the cusp label to the arithmetic elliptic quotient. -/
def sheetRepresentative : groupData.piEll :=
  cusp.atlas.sheetRepresentative cusp.origin

/-- The cuspidal decomposition sequence of the selected `X`-cusp. -/
def xDecomposition :
    OrbicurveCuspidalDecompositionData
      stack.xFundamentalGroups :=
  cusp.atlas.xCusps cusp.origin

/-- The cuspidal decomposition sequence of the selected sign-orbit cusp. -/
def cDecomposition :
    OrbicurveCuspidalDecompositionData
      stack.cFundamentalGroups :=
  cusp.atlas.cCusps
    (EtaleTheta.toSignLabel cusp.origin)

/-- The cusp label after identifying a sheet with its inverse. -/
def signLabel :
    EtaleTheta.SignLabel
      (EtaleTheta.LTorsionLabel l.value) :=
  EtaleTheta.toSignLabel cusp.origin

theorem origin_ne_one :
    (cusp.origin :
      EtaleTheta.LTorsionLabel l.value) ≠ 1 :=
  cusp.origin.property

/--
The cusp label `2 epsilon` from the construction preceding IUT I,
Definition 1.1.  Multiplication in `LTorsionLabel` is addition in `ZMod l`,
so squaring is multiplication of the original elliptic-torsion point by two.
-/
def doubledOrigin :
    EtaleTheta.NonzeroLabel
      (EtaleTheta.LTorsionLabel l.value) := by
  letI : Fact (Nat.Prime l.value) := ⟨l.prime⟩
  refine ⟨(cusp.origin :
    EtaleTheta.LTorsionLabel l.value) ^ 2, ?_⟩
  intro h
  have htwo :
      (2 : ZMod l.value) ≠ 0 := by
    intro hz
    have hdiv : l.value ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 l.value).mp hz
    have hle : l.value ≤ 2 :=
      Nat.le_of_dvd (by omega) hdiv
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have horigin :
      Multiplicative.toAdd
          (cusp.origin :
            EtaleTheta.LTorsionLabel l.value) ≠ 0 := by
    simpa using cusp.origin.property
  have hproduct :
      (2 : ZMod l.value) *
          Multiplicative.toAdd
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) = 0 := by
    simpa [nsmul_eq_mul] using
      congrArg Multiplicative.toAdd h
  exact horigin ((mul_eq_zero.mp hproduct).resolve_left htwo)

@[simp]
theorem doubledOrigin_value :
    (cusp.doubledOrigin :
      EtaleTheta.LTorsionLabel l.value) =
      (cusp.origin :
        EtaleTheta.LTorsionLabel l.value) ^ 2 :=
  rfl

theorem doubledOrigin_ne_origin :
    cusp.doubledOrigin ≠ cusp.origin := by
  intro h
  have hmul :
      (cusp.origin :
          EtaleTheta.LTorsionLabel l.value) *
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) =
        (cusp.origin :
          EtaleTheta.LTorsionLabel l.value) * 1 := by
    simpa [pow_two] using congrArg Subtype.val h
  exact cusp.origin.property (mul_left_cancel hmul)

theorem doubledOrigin_ne_inverse :
    cusp.doubledOrigin ≠ cusp.origin⁻¹ := by
  letI : Fact (Nat.Prime l.value) := ⟨l.prime⟩
  intro h
  have hthree :
      (3 : ZMod l.value) ≠ 0 := by
    intro hz
    have hdiv : l.value ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 l.value).mp hz
    have hle : l.value ≤ 3 :=
      Nat.le_of_dvd (by omega) hdiv
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have horigin :
      Multiplicative.toAdd
          (cusp.origin :
            EtaleTheta.LTorsionLabel l.value) ≠ 0 := by
    simpa using cusp.origin.property
  have hdouble :
      (2 : ZMod l.value) *
          Multiplicative.toAdd
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) =
        -Multiplicative.toAdd
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) := by
    have hval :
        (cusp.origin :
            EtaleTheta.LTorsionLabel l.value) ^ 2 =
          (cusp.origin :
            EtaleTheta.LTorsionLabel l.value)⁻¹ :=
      congrArg Subtype.val h
    simpa [nsmul_eq_mul] using
      congrArg Multiplicative.toAdd hval
  have hproduct :
      (3 : ZMod l.value) *
          Multiplicative.toAdd
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) = 0 := by
    calc
      (3 : ZMod l.value) *
          Multiplicative.toAdd
            (cusp.origin :
              EtaleTheta.LTorsionLabel l.value) =
          (2 : ZMod l.value) *
              Multiplicative.toAdd
                (cusp.origin :
                  EtaleTheta.LTorsionLabel l.value) +
            Multiplicative.toAdd
              (cusp.origin :
                EtaleTheta.LTorsionLabel l.value) := by ring
      _ = 0 := by rw [hdouble]; exact neg_add_cancel _
  exact horigin ((mul_eq_zero.mp hproduct).resolve_left hthree)

theorem sheetRepresentative_label :
    groupData.lagrangian.quotient.quotient
        cusp.sheetRepresentative =
      cusp.origin :=
  cusp.atlas.sheetRepresentative_label cusp.origin

end TypeOneNonzeroCusp

/-- Mod-`l` inertia classes of all nonselected nonzero cusps of the `X`-cover. -/
def TypeOneNonzeroCusp.nonselectedInertiaGenerators
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack) :
    Set
      (EtaleTheta.ModLEllipticAbelianization
        stack.xFundamentalGroups.geometric.group
        l.value) :=
  {x | ∃ q,
    q ≠ cusp.origin ∧ q ≠ cusp.origin⁻¹ ∧
      ∃ inertiaElement : (cusp.atlas.xCusps q).inertia,
        x =
          EtaleTheta.modLEllipticProjection
            stack.xFundamentalGroups.geometric.group
            l.value
            ((cusp.atlas.xCusps q).ambientEmbedding.geometric.hom
              inertiaElement)}

/--
The subgroup generated by the inertia groups of every nonzero cusp except the
two cusps over the selected sign orbit.
-/
def TypeOneNonzeroCusp.discardedInertiaSubgroup
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack) :
    Subgroup
      (EtaleTheta.ModLEllipticAbelianization
        stack.xFundamentalGroups.geometric.group
        l.value) :=
  Subgroup.normalClosure cusp.nonselectedInertiaGenerators

instance TypeOneNonzeroCusp.discardedInertiaSubgroup_normal
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack) :
    cusp.discardedInertiaSubgroup.Normal := by
  exact Subgroup.normalClosure_normal

/-- The quotient `Delta dagger` in the construction preceding IUT I, Definition 1.1. -/
abbrev TypeOneNonzeroCusp.ArrowedDelta
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack) :=
  EtaleTheta.ModLEllipticAbelianization
      stack.xFundamentalGroups.geometric.group l.value ⧸
    cusp.discardedInertiaSubgroup

namespace TypeOneNonzeroCusp

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack)

/-- The first selected inertia group mapped into `Delta dagger`. -/
def firstSelectedInertia :
    (cusp.atlas.xCusps cusp.origin).inertia →*
      cusp.ArrowedDelta :=
  (QuotientGroup.mk' cusp.discardedInertiaSubgroup).comp
    ((EtaleTheta.modLEllipticProjection
      stack.xFundamentalGroups.geometric.group
      l.value).comp
      (cusp.atlas.xCusps
        cusp.origin).ambientEmbedding.geometric.hom.hom.toMonoidHom)

/-- The sign-conjugate selected inertia group mapped into `Delta dagger`. -/
def secondSelectedInertia :
    (cusp.atlas.xCusps cusp.origin⁻¹).inertia →*
      cusp.ArrowedDelta :=
  (QuotientGroup.mk' cusp.discardedInertiaSubgroup).comp
    ((EtaleTheta.modLEllipticProjection
      stack.xFundamentalGroups.geometric.group
      l.value).comp
      (cusp.atlas.xCusps
        cusp.origin⁻¹).ambientEmbedding.geometric.hom.hom.toMonoidHom)

/-- Image of the first selected inertia group in `Delta dagger`. -/
def firstSelectedInertiaImage :
    Subgroup cusp.ArrowedDelta :=
  cusp.firstSelectedInertia.range

/-- Image of the sign-conjugate selected inertia group in `Delta dagger`. -/
def secondSelectedInertiaImage :
    Subgroup cusp.ArrowedDelta :=
  cusp.secondSelectedInertia.range

end TypeOneNonzeroCusp

/--
The mod-`l` eigenspace quotient in the construction of the arrowed covers from
IUT I, Definition 1.1.

The quotient itself and the two selected inertia maps are derived above.  This
record supplies the paper's remaining geometric input: descent of inversion,
the direct-product eigenspace decomposition, and the two inertia
identifications with the positive eigenspace.
-/
structure ArrowedCuspidalEigenspaceData
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack) where
  inversion :
    cusp.ArrowedDelta ≃* cusp.ArrowedDelta
  inversion_involutive :
    inversion.trans inversion =
      MulEquiv.refl cusp.ArrowedDelta
  inversion_from_signAction :
    ∀ g,
      inversion
          (QuotientGroup.mk
            (EtaleTheta.modLEllipticProjection
              stack.xFundamentalGroups.geometric.group
              l.value g)) =
        QuotientGroup.mk
          (EtaleTheta.modLEllipticProjection
            stack.xFundamentalGroups.geometric.group
            l.value
            (stack.signFundamentalGroupAction.geometric.hom g))
  positiveEigenspace : Subgroup cusp.ArrowedDelta
  positiveEigenspace_eq :
    positiveEigenspace =
      {x | inversion x = x}
  negativeEigenspace : Subgroup cusp.ArrowedDelta
  negativeEigenspace_eq :
    negativeEigenspace =
      {x | inversion x = x⁻¹}
  productDecomposition :
    cusp.ArrowedDelta ≃*
      positiveEigenspace × negativeEigenspace
  productDecomposition_coordinates :
    ∀ x,
      ((productDecomposition (inversion x)).1,
        (productDecomposition (inversion x)).2) =
      ((productDecomposition x).1,
        (productDecomposition x).2⁻¹)
  positiveRankOne :
    positiveEigenspace ≃*
      EtaleTheta.LTorsionLabel l.value
  firstInertiaEquiv :
    cusp.firstSelectedInertiaImage ≃*
      positiveEigenspace
  firstInertiaEquiv_inclusion :
    positiveEigenspace.subtype.comp
        firstInertiaEquiv.toMonoidHom =
      cusp.firstSelectedInertiaImage.subtype
  secondInertiaEquiv :
    cusp.secondSelectedInertiaImage ≃*
      positiveEigenspace
  secondInertiaEquiv_inclusion :
      positiveEigenspace.subtype.comp
        secondInertiaEquiv.toMonoidHom =
      cusp.secondSelectedInertiaImage.subtype

namespace ArrowedCuspidalEigenspaceData

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    (data : ArrowedCuspidalEigenspaceData l cusp)

/-- Projection of `Delta dagger` to its positive eigenspace. -/
def positiveProjection :
    cusp.ArrowedDelta →* data.positiveEigenspace where
  toFun x := (data.productDecomposition x).1
  map_one' := by simp
  map_mul' x y := by
    exact
      congrArg Prod.fst
        (data.productDecomposition.map_mul x y)

/-- The derived quotient of the geometric `X`-cover group onto `Delta dagger plus`. -/
def geometricPositiveQuotient :
    stack.xFundamentalGroups.geometric.group →*
      data.positiveEigenspace :=
  data.positiveProjection.comp
    ((QuotientGroup.mk'
      cusp.discardedInertiaSubgroup).comp
      (EtaleTheta.modLEllipticProjection
        stack.xFundamentalGroups.geometric.group
        l.value))

theorem geometricPositiveQuotient_surjective :
    Function.Surjective data.geometricPositiveQuotient := by
  intro x
  obtain ⟨delta, hdelta⟩ :=
    (QuotientGroup.mk'_surjective
      cusp.discardedInertiaSubgroup)
      (data.productDecomposition.symm (x, 1))
  obtain ⟨g, hg⟩ :=
    EtaleTheta.modLEllipticProjection_surjective
      stack.xFundamentalGroups.geometric.group
      l.value delta
  refine ⟨g, ?_⟩
  change
    (data.productDecomposition
      (QuotientGroup.mk
        (EtaleTheta.modLEllipticProjection
          stack.xFundamentalGroups.geometric.group
          l.value g))).1 = x
  rw [hg]
  change
    (data.productDecomposition
      ((QuotientGroup.mk'
        cusp.discardedInertiaSubgroup) delta)).1 = x
  rw [hdelta]
  simp

end ArrowedCuspidalEigenspaceData

/-- The finite profinite group underlying `Delta dagger plus`. -/
abbrev ArrowedPositiveProfiniteGroup
    (l : PrimeGeFive) : ProfiniteGrp.{u} :=
  EtaleTheta.lTorsionProfiniteGroup.{u} l.value

/-- The order-two profinite group generated by the sign involution. -/
abbrev ArrowedSignProfiniteGroup : ProfiniteGrp.{u} :=
  EtaleTheta.lTorsionProfiniteGroup.{u} 2

/-- Universe-lifted product underlying the geometric kernel of `J_C`. -/
abbrev ArrowedCGeometricLabel
    (l : PrimeGeFive) :=
  ULift.{u}
    (EtaleTheta.LTorsionLabel l.value ×
      EtaleTheta.LTorsionLabel 2)

/--
The geometric kernel `Delta dagger plus x Gal(X/C)` of `J_C -> G_K`.
-/
abbrev ArrowedCGeometricProfiniteGroup
    (l : PrimeGeFive) : ProfiniteGrp.{u} :=
  ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (ArrowedCGeometricLabel.{u} l))

/-- Inclusion of `Delta dagger plus` as the first geometric factor of `J_C`. -/
def arrowedPositiveFactorInclusion
    (l : PrimeGeFive) :
    ArrowedPositiveProfiniteGroup.{u} l ⟶
      ArrowedCGeometricProfiniteGroup.{u} l :=
  ProfiniteGrp.ofFiniteGrpHom
    (FiniteGrp.ofHom
      { toFun := fun q => ULift.up (q.down, 1)
        map_one' := rfl
        map_mul' := by intro x y; rfl })

/-- Inclusion of `Gal(X/C)` as the second geometric factor of `J_C`. -/
def arrowedSignFactorInclusion
    (l : PrimeGeFive) :
    ArrowedSignProfiniteGroup.{u} ⟶
      ArrowedCGeometricProfiniteGroup.{u} l :=
  ProfiniteGrp.ofFiniteGrpHom
    (FiniteGrp.ofHom
      { toFun := fun sign => ULift.up (1, sign.down)
        map_one' := rfl
        map_mul' := by
          intro x y
          apply ULift.ext
          simp })

/-- The nontrivial element of the profinite sign factor. -/
def arrowedSignGenerator :
    ArrowedSignProfiniteGroup.{u} :=
  ULift.up (Multiplicative.ofAdd (1 : ZMod 2))

@[simp]
theorem arrowedSignGenerator_orderTwo :
    (arrowedSignGenerator :
      ArrowedSignProfiniteGroup.{u}) ^ 2 = 1 := by
  apply ULift.ext
  change (1 + 1 : ZMod 2) = 0
  decide

theorem arrowedSignGenerator_ne_one :
    (arrowedSignGenerator :
      ArrowedSignProfiniteGroup.{u}) ≠ 1 := by
  intro h
  have hdown := congrArg ULift.down h
  have hadd := congrArg Multiplicative.toAdd hdown
  change (1 : ZMod 2) = 0 at hadd
  exact one_ne_zero hadd

/-- The nontrivial sign element in the product geometric kernel of `J_C`. -/
def arrowedCSignGenerator
    (l : PrimeGeFive) :
    ArrowedCGeometricProfiniteGroup.{u} l :=
  ULift.up (1, Multiplicative.ofAdd (1 : ZMod 2))

namespace ArrowedCuspidalEigenspaceData

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    (data : ArrowedCuspidalEigenspaceData l cusp)

/-- Identification of the finite profinite model with the positive eigenspace. -/
def positiveProfiniteIdentification :
    ArrowedPositiveProfiniteGroup.{u} l ≃*
      data.positiveEigenspace :=
  (EtaleTheta.liftedLTorsionEquiv l.value).trans
    data.positiveRankOne.symm

end ArrowedCuspidalEigenspaceData

/--
Topological realization of the positive-eigenspace quotient.

The algebraic quotient was derived from the actual geometric fundamental
group.  This record adds precisely the missing assertion that it is induced
by a continuous morphism to the finite profinite rank-one group.
-/
structure ArrowedPositiveProfiniteRealization
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    (eigenspaces :
      ArrowedCuspidalEigenspaceData l cusp) where
  geometricProjection :
    stack.xFundamentalGroups.geometric.group ⟶
      ArrowedPositiveProfiniteGroup.{u} l
  geometricProjection_identification :
    eigenspaces.positiveProfiniteIdentification.toMonoidHom.comp
        geometricProjection.hom.toMonoidHom =
      eigenspaces.geometricPositiveQuotient

namespace ArrowedPositiveProfiniteRealization

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    {eigenspaces : ArrowedCuspidalEigenspaceData l cusp}
    (topology :
      ArrowedPositiveProfiniteRealization l eigenspaces)

theorem geometricProjection_surjective :
    Function.Surjective topology.geometricProjection := by
  intro q
  obtain ⟨g, hg⟩ :=
    eigenspaces.geometricPositiveQuotient_surjective
      (eigenspaces.positiveProfiniteIdentification q)
  refine ⟨g, ?_⟩
  apply eigenspaces.positiveProfiniteIdentification.injective
  have hcompat :=
    DFunLike.congr_fun
      topology.geometricProjection_identification g
  exact hcompat.trans hg

end ArrowedPositiveProfiniteRealization

namespace TypeOneNonzeroCusp

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    (cusp : TypeOneNonzeroCusp l groupData stack)

/-- The cuspidal decomposition sequence attached to the doubled cusp `2 epsilon`. -/
def doubledCDecomposition :
    OrbicurveCuspidalDecompositionData
      stack.cFundamentalGroups :=
  cusp.atlas.cCusps
    (EtaleTheta.toSignLabel cusp.doubledOrigin)

end TypeOneNonzeroCusp

/--
The intermediate quotients `J_X -> J_C` and the doubled-cusp section in the
construction preceding IUT I, Definition 1.1.

Both quotient maps are continuous surjections and commute with the original
fundamental exact sequences.  The section is tied to the decomposition group
of `2 epsilon`; its lift to `J_X` records the paper's assertion that its image
lies in `J_X`.  Centrality of the geometric kernel against this section is the
trivial Galois-action hypothesis used to prove normality of the image.
-/
structure ArrowedJQuotientData
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    {eigenspaces :
      ArrowedCuspidalEigenspaceData l cusp}
    (positiveTopology :
      ArrowedPositiveProfiniteRealization l eigenspaces) where
  jX : ProfiniteGrp.{u}
  jC : ProfiniteGrp.{u}
  xExact :
    ProfiniteFundamentalExactSequence
      (ArrowedPositiveProfiniteGroup.{u} l)
      jX orbicurves.absoluteGalois
  cExact :
    ProfiniteFundamentalExactSequence
      (ArrowedCGeometricProfiniteGroup.{u} l)
      jC orbicurves.absoluteGalois
  xQuotient :
    stack.xFundamentalGroups.arithmetic.group ⟶ jX
  xQuotient_surjective :
    Function.Surjective xQuotient
  xGeometricSquare :
    stack.xFundamentalGroups.exactSequence.inclusion ≫
        xQuotient =
      positiveTopology.geometricProjection ≫
        xExact.inclusion
  xGaloisSquare :
    xQuotient ≫ xExact.projection =
      stack.xFundamentalGroups.exactSequence.projection
  cGeometricQuotient :
    stack.cFundamentalGroups.geometric.group ⟶
      ArrowedCGeometricProfiniteGroup.{u} l
  cGeometricQuotient_surjective :
    Function.Surjective cGeometricQuotient
  cGeometricQuotient_restricts :
    stack.xToCFundamentalGroupInclusion.geometric.hom ≫
        cGeometricQuotient =
      positiveTopology.geometricProjection ≫
        arrowedPositiveFactorInclusion l
  cSignInvolution_maps_to_generator :
    cGeometricQuotient stack.signInvolution =
      arrowedCSignGenerator l
  cQuotient :
    stack.cFundamentalGroups.arithmetic.group ⟶ jC
  cQuotient_surjective :
    Function.Surjective cQuotient
  cGeometricSquare :
    stack.cFundamentalGroups.exactSequence.inclusion ≫
        cQuotient =
      cGeometricQuotient ≫ cExact.inclusion
  cGaloisSquare :
    cQuotient ≫ cExact.projection =
      stack.cFundamentalGroups.exactSequence.projection
  jInclusion :
    ProfiniteFundamentalGroupInclusion
      (ArrowedPositiveProfiniteGroup.{u} l) jX
      (ArrowedCGeometricProfiniteGroup.{u} l) jC
      orbicurves.absoluteGalois xExact cExact
  jInclusion_geometric_eq :
    jInclusion.geometric.hom =
      arrowedPositiveFactorInclusion l
  quotientInclusionSquare :
    stack.xToCFundamentalGroupInclusion.arithmetic.hom ≫
        cQuotient =
      xQuotient ≫ jInclusion.arithmetic.hom
  doubledCuspSection :
    orbicurves.absoluteGalois ⟶ jC
  doubledCuspSection_rightInverse :
    doubledCuspSection ≫ cExact.projection =
      𝟙 orbicurves.absoluteGalois
  doubledCusp_factorization :
    cusp.doubledCDecomposition.ambientEmbedding.arithmetic.hom ≫
        cQuotient =
      cusp.doubledCDecomposition.exactSequence.projection ≫
        doubledCuspSection
  doubledCuspSectionLift :
    orbicurves.absoluteGalois ⟶ jX
  doubledCuspSectionLift_rightInverse :
    doubledCuspSectionLift ≫ xExact.projection =
      𝟙 orbicurves.absoluteGalois
  doubledCuspSectionLift_to_jC :
    doubledCuspSectionLift ≫
        jInclusion.arithmetic.hom =
      doubledCuspSection
  kernel_centralizes_doubledCuspSection :
    ∀ kernelElement g,
      cExact.inclusion kernelElement *
          doubledCuspSection g =
        doubledCuspSection g *
          cExact.inclusion kernelElement

namespace ArrowedJQuotientData

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    {eigenspaces :
      ArrowedCuspidalEigenspaceData l cusp}
    {positiveTopology :
      ArrowedPositiveProfiniteRealization l eigenspaces}
    (data : ArrowedJQuotientData l positiveTopology)

/-- The image of the section determined by the doubled cusp. -/
def doubledCuspSectionImage : Subgroup data.jC :=
  data.doubledCuspSection.hom.range

/-- The same doubled-cusp section, regarded inside `J_X`. -/
def doubledCuspSectionLiftImage : Subgroup data.jX :=
  data.doubledCuspSectionLift.hom.range

/-- The doubled-cusp section image is normal, as asserted before Definition 1.1. -/
theorem doubledCuspSectionImage_normal :
    data.doubledCuspSectionImage.Normal := by
  constructor
  intro n hn x
  obtain ⟨g, rfl⟩ := hn
  let q := data.cExact.projection x
  have hkernel :
      x * (data.doubledCuspSection q)⁻¹ ∈
        data.cExact.projection.hom.ker := by
    change
      data.cExact.projection
          (x * (data.doubledCuspSection q)⁻¹) = 1
    rw [map_mul, map_inv]
    have hsection :
        data.cExact.projection
            (data.doubledCuspSection q) = q := by
      simpa using
        ConcreteCategory.congr_hom
          data.doubledCuspSection_rightInverse q
    change data.cExact.projection x *
        (data.cExact.projection
          (data.doubledCuspSection q))⁻¹ = 1
    rw [hsection]
    exact mul_inv_cancel _
  rw [← data.cExact.exact] at hkernel
  obtain ⟨kernelElement, hkernelElement⟩ := hkernel
  change
    data.cExact.inclusion kernelElement =
      x * (data.doubledCuspSection q)⁻¹ at hkernelElement
  have hx :
      x =
        data.cExact.inclusion kernelElement *
          data.doubledCuspSection q := by
    calc
      x =
          (x * (data.doubledCuspSection q)⁻¹) *
            data.doubledCuspSection q := by group
      _ =
          data.cExact.inclusion kernelElement *
            data.doubledCuspSection q := by
              rw [← hkernelElement]
  refine ⟨q * g * q⁻¹, ?_⟩
  symm
  have hsectionConjugation :
      data.doubledCuspSection q *
          data.doubledCuspSection g *
          (data.doubledCuspSection q)⁻¹ =
        data.doubledCuspSection (q * g * q⁻¹) := by
    simp
  calc
    x * data.doubledCuspSection g * x⁻¹ =
      (data.cExact.inclusion kernelElement *
          data.doubledCuspSection q) *
        data.doubledCuspSection g *
        (data.cExact.inclusion kernelElement *
          data.doubledCuspSection q)⁻¹ := by rw [hx]
    _ =
      data.cExact.inclusion kernelElement *
        (data.doubledCuspSection q *
          data.doubledCuspSection g *
          (data.doubledCuspSection q)⁻¹) *
        (data.cExact.inclusion kernelElement)⁻¹ := by group
    _ =
      data.cExact.inclusion kernelElement *
        data.doubledCuspSection (q * g * q⁻¹) *
        (data.cExact.inclusion kernelElement)⁻¹ := by
          rw [hsectionConjugation]
    _ =
      data.doubledCuspSection (q * g * q⁻¹) *
        data.cExact.inclusion kernelElement *
        (data.cExact.inclusion kernelElement)⁻¹ := by
          rw [data.kernel_centralizes_doubledCuspSection]
    _ = data.doubledCuspSection (q * g * q⁻¹) := by simp

/-- The sign factor inside `J_C`. -/
def signFactor :
    ArrowedSignProfiniteGroup.{u} ⟶ data.jC :=
  arrowedSignFactorInclusion l ≫ data.cExact.inclusion

/-- The subgroup `Im(sigma) x Gal(X/C)` used to define the arrowed `C`-cover. -/
def doubledCuspSectionSignSubgroup : Subgroup data.jC :=
  data.doubledCuspSectionImage ⊔ data.signFactor.hom.range

end ArrowedJQuotientData

/--
Stack and profinite-group realization of the arrowed covers from IUT I,
Definition 1.1.

The geometric `X`-cover subgroup is not supplied independently: its image is
required to be the kernel of the positive-eigenspace quotient constructed
above.  The corresponding `C` quotient extends it across the sign involution.
-/
structure ArrowedTypeOneStackRealization
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    (eigenspaces :
      ArrowedCuspidalEigenspaceData l cusp)
    (positiveTopology :
      ArrowedPositiveProfiniteRealization l eigenspaces)
    (jQuotients :
      ArrowedJQuotientData l positiveTopology) where
  arrowX : HyperbolicOrbicurve K
  arrowC : HyperbolicOrbicurve K
  xToBase : arrowX.Hom stack.xCover
  cToBase : arrowC.Hom stack.cCover
  signAction : OrbicurveSignAction arrowX
  quotientMap : arrowX.Hom arrowC
  quotientInvariant :
    OrbicurveSignInvariantMorphism signAction arrowC
  quotientInvariant_map :
    quotientInvariant.map = quotientMap
  quotientUniversal :
    OrbicurveSignQuotientWitness
      signAction quotientInvariant
  coverSquare :
    OrbicurveSquare arrowX stack.xCover
      arrowC stack.cCover
  coverSquare_toX :
    coverSquare.toX = xToBase
  coverSquare_toY :
    coverSquare.toY = quotientMap
  coverSquare_xToBase :
    coverSquare.xToBase = stack.quotientMap
  coverSquare_yToBase :
    coverSquare.yToBase = cToBase
  cartesian :
    coverSquare.TwoPullbackWitness
  xFundamentalGroups :
    OrbicurveFundamentalGroupData
      arrowX orbicurves.absoluteGalois
  cFundamentalGroups :
    OrbicurveFundamentalGroupData
      arrowC orbicurves.absoluteGalois
  xToCFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      xFundamentalGroups.geometric.group
      xFundamentalGroups.arithmetic.group
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      xFundamentalGroups.exactSequence
      cFundamentalGroups.exactSequence
  xToBaseFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      xFundamentalGroups.geometric.group
      xFundamentalGroups.arithmetic.group
      stack.xFundamentalGroups.geometric.group
      stack.xFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      xFundamentalGroups.exactSequence
      stack.xFundamentalGroups.exactSequence
  cToBaseFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      stack.cFundamentalGroups.geometric.group
      stack.cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      cFundamentalGroups.exactSequence
      stack.cFundamentalGroups.exactSequence
  xArithmeticImage_eq_sectionPreimage :
    xToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range =
      jQuotients.doubledCuspSectionLiftImage.comap
        jQuotients.xQuotient.hom.toMonoidHom
  cArithmeticImage_eq_sectionSignPreimage :
    cToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range =
      jQuotients.doubledCuspSectionSignSubgroup.comap
        jQuotients.cQuotient.hom.toMonoidHom
  xGeometricImage_eq_kernel :
    xToBaseFundamentalGroupInclusion.geometric.hom.hom.range =
      eigenspaces.geometricPositiveQuotient.ker
  xArithmeticPositiveQuotient :
    stack.xFundamentalGroups.arithmetic.group →*
      eigenspaces.positiveEigenspace
  xArithmeticPositiveQuotient_surjective :
    Function.Surjective xArithmeticPositiveQuotient
  xArithmeticPositiveQuotient_geometric :
    xArithmeticPositiveQuotient.comp
        stack.xFundamentalGroups.exactSequence.inclusion.hom.toMonoidHom =
      eigenspaces.geometricPositiveQuotient
  xArithmeticImage_eq_kernel :
    xToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range =
      xArithmeticPositiveQuotient.ker
  cGeometricPositiveQuotient :
    stack.cFundamentalGroups.geometric.group →*
      eigenspaces.positiveEigenspace
  cGeometricPositiveQuotient_surjective :
    Function.Surjective cGeometricPositiveQuotient
  cGeometricPositiveQuotient_restricts :
    cGeometricPositiveQuotient.comp
        stack.xToCFundamentalGroupInclusion.geometric.hom.hom.toMonoidHom =
      eigenspaces.geometricPositiveQuotient
  cGeometricImage_eq_kernel :
    cToBaseFundamentalGroupInclusion.geometric.hom.hom.range =
      cGeometricPositiveQuotient.ker
  cArithmeticPositiveQuotient :
    stack.cFundamentalGroups.arithmetic.group →*
      eigenspaces.positiveEigenspace
  cArithmeticPositiveQuotient_surjective :
    Function.Surjective cArithmeticPositiveQuotient
  cArithmeticPositiveQuotient_geometric :
    cArithmeticPositiveQuotient.comp
        stack.cFundamentalGroups.exactSequence.inclusion.hom.toMonoidHom =
      cGeometricPositiveQuotient
  cArithmeticPositiveQuotient_restricts :
    cArithmeticPositiveQuotient.comp
        stack.xToCFundamentalGroupInclusion.arithmetic.hom.hom.toMonoidHom =
      xArithmeticPositiveQuotient
  cArithmeticImage_eq_kernel :
    cToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range =
      cArithmeticPositiveQuotient.ker
  combinedArithmeticImage_normal :
    (xToCFundamentalGroupInclusion.arithmetic.hom.hom.range.map
      cToBaseFundamentalGroupInclusion.arithmetic.hom.hom.toMonoidHom).Normal
  combinedDeckQuotient :
    stack.cFundamentalGroups.arithmetic.group →*
      Multiplicative (ZMod (2 * l.value))
  combinedDeckQuotient_surjective :
    Function.Surjective combinedDeckQuotient
  combinedDeckQuotient_kernel :
    combinedDeckQuotient.ker =
      xToCFundamentalGroupInclusion.arithmetic.hom.hom.range.map
        cToBaseFundamentalGroupInclusion.arithmetic.hom.hom.toMonoidHom

namespace ArrowedTypeOneStackRealization

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    {groupData : GlobalLTorsionCoverInput l orbicurves}
    {stack : TypeOneLTorsionStackRealization l groupData}
    {cusp : TypeOneNonzeroCusp l groupData stack}
    {eigenspaces : ArrowedCuspidalEigenspaceData l cusp}
    {positiveTopology :
      ArrowedPositiveProfiniteRealization l eigenspaces}
    {jQuotients :
      ArrowedJQuotientData l positiveTopology}
    (realization :
      ArrowedTypeOneStackRealization l eigenspaces
        positiveTopology jQuotients)

theorem xGeometricImage_normal :
    realization.xToBaseFundamentalGroupInclusion.geometric.hom.hom.range.Normal := by
  rw [realization.xGeometricImage_eq_kernel]
  infer_instance

theorem xArithmeticImage_normal :
    realization.xToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range.Normal := by
  rw [realization.xArithmeticImage_eq_kernel]
  infer_instance

theorem cGeometricImage_normal :
    realization.cToBaseFundamentalGroupInclusion.geometric.hom.hom.range.Normal := by
  rw [realization.cGeometricImage_eq_kernel]
  infer_instance

theorem cArithmeticImage_normal :
    realization.cToBaseFundamentalGroupInclusion.arithmetic.hom.hom.range.Normal := by
  rw [realization.cArithmeticImage_eq_kernel]
  infer_instance

/-- The degree-`l` deck group of the arrowed `X`-cover. -/
noncomputable def xDeckEquiv :
    stack.xFundamentalGroups.arithmetic.group ⧸
        realization.xArithmeticPositiveQuotient.ker ≃*
      eigenspaces.positiveEigenspace := by
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      realization.xArithmeticPositiveQuotient
      realization.xArithmeticPositiveQuotient_surjective

/-- The degree-`l` deck group of the arrowed `C`-cover. -/
noncomputable def cDeckEquiv :
    stack.cFundamentalGroups.arithmetic.group ⧸
        realization.cArithmeticPositiveQuotient.ker ≃*
      eigenspaces.positiveEigenspace := by
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      realization.cArithmeticPositiveQuotient
      realization.cArithmeticPositiveQuotient_surjective

/-- The cyclic order-`2l` deck group of the composite arrowed cover. -/
noncomputable def combinedDeckEquiv :
    stack.cFundamentalGroups.arithmetic.group ⧸
        realization.combinedDeckQuotient.ker ≃*
      Multiplicative (ZMod (2 * l.value)) := by
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      realization.combinedDeckQuotient
      realization.combinedDeckQuotient_surjective

end ArrowedTypeOneStackRealization

/--
Localization of a nonzero cusp along a scalar extension of type-`(1,l-tors)`
covers.

The local sheet representative is the image of the global representative in
the local-to-global elliptic quotient, and both cuspidal decomposition exact
sequences commute with the corresponding cover diagrams.  Consequently the
local sign label is derived below to equal the global sign label.
-/
structure TypeOneNonzeroCuspScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    (coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack)
    (globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack) where
  localCusp :
    TypeOneNonzeroCusp l
      coverExtension.localGroupData
      coverExtension.localStack
  sheetRepresentative_compatible :
    coverExtension.ellipticEmbedding.hom
        localCusp.sheetRepresentative =
      globalCusp.sheetRepresentative
  xDecompositionDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localCusp.xDecomposition.inertia
      localCusp.xDecomposition.decomposition
      localOrbicurves.absoluteGalois
      globalCusp.xDecomposition.inertia
      globalCusp.xDecomposition.decomposition
      globalOrbicurves.absoluteGalois
      localCusp.xDecomposition.exactSequence
      globalCusp.xDecomposition.exactSequence
  cDecompositionDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localCusp.cDecomposition.inertia
      localCusp.cDecomposition.decomposition
      localOrbicurves.absoluteGalois
      globalCusp.cDecomposition.inertia
      globalCusp.cDecomposition.decomposition
      globalOrbicurves.absoluteGalois
      localCusp.cDecomposition.exactSequence
      globalCusp.cDecomposition.exactSequence
  xDecomposition_galois_eq :
    xDecompositionDiagram.galois =
      coverExtension.galoisEmbedding
  cDecomposition_galois_eq :
    cDecompositionDiagram.galois =
      coverExtension.galoisEmbedding
  xDecomposition_ambient_square :
    xDecompositionDiagram.arithmetic.hom ≫
        globalCusp.xDecomposition.ambientEmbedding.arithmetic.hom =
      localCusp.xDecomposition.ambientEmbedding.arithmetic.hom ≫
        coverExtension.xFundamentalGroupDiagram.arithmetic.hom
  cDecomposition_ambient_square :
    cDecompositionDiagram.arithmetic.hom ≫
        globalCusp.cDecomposition.ambientEmbedding.arithmetic.hom =
      localCusp.cDecomposition.ambientEmbedding.arithmetic.hom ≫
        coverExtension.cFundamentalGroupDiagram.arithmetic.hom

namespace TypeOneNonzeroCuspScalarExtension

variable
    {l : PrimeGeFive}
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    (extension :
      TypeOneNonzeroCuspScalarExtension l K L
        coverExtension globalCusp)

theorem origin_eq :
    extension.localCusp.origin =
      globalCusp.origin := by
  apply Subtype.ext
  calc
    (extension.localCusp.origin :
        EtaleTheta.LTorsionLabel l.value) =
        coverExtension.localGroupData.lagrangian.quotient.quotient
          extension.localCusp.sheetRepresentative :=
      extension.localCusp.sheetRepresentative_label.symm
    _ =
        globalGroupData.lagrangian.quotient.quotient
          (coverExtension.ellipticEmbedding.hom
            extension.localCusp.sheetRepresentative) :=
      (coverExtension.lagrangianQuotient_compatible
        extension.localCusp.sheetRepresentative).symm
    _ =
        globalGroupData.lagrangian.quotient.quotient
          globalCusp.sheetRepresentative := by
      rw [extension.sheetRepresentative_compatible]
    _ = (globalCusp.origin :
        EtaleTheta.LTorsionLabel l.value) :=
      globalCusp.sheetRepresentative_label

theorem signLabel_eq :
    extension.localCusp.signLabel =
      globalCusp.signLabel := by
  exact congrArg EtaleTheta.toSignLabel extension.origin_eq

end TypeOneNonzeroCuspScalarExtension

/--
Scalar extension of one cuspidal decomposition exact sequence inside a
scalar extension of ambient orbicurve fundamental groups.
-/
structure CuspidalDecompositionScalarExtension
    (K L : Type u) [Field K] [Field L]
    {localGalois globalGalois : ProfiniteGrp.{u}}
    {localX : HyperbolicOrbicurve L}
    {globalX : HyperbolicOrbicurve K}
    (localGroups :
      OrbicurveFundamentalGroupData localX localGalois)
    (globalGroups :
      OrbicurveFundamentalGroupData globalX globalGalois)
    (ambientDiagram :
      ProfiniteFundamentalExactSequenceEmbedding
        localGroups.geometric.group
        localGroups.arithmetic.group localGalois
        globalGroups.geometric.group
        globalGroups.arithmetic.group globalGalois
        localGroups.exactSequence
        globalGroups.exactSequence)
    (localCusp :
      OrbicurveCuspidalDecompositionData localGroups)
    (globalCusp :
      OrbicurveCuspidalDecompositionData globalGroups) where
  diagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localCusp.inertia localCusp.decomposition localGalois
      globalCusp.inertia globalCusp.decomposition globalGalois
      localCusp.exactSequence globalCusp.exactSequence
  galois_eq :
    diagram.galois = ambientDiagram.galois
  geometric_ambient_square :
    diagram.geometric.hom ≫
        globalCusp.ambientEmbedding.geometric.hom =
      localCusp.ambientEmbedding.geometric.hom ≫
        ambientDiagram.geometric.hom
  arithmetic_ambient_square :
    diagram.arithmetic.hom ≫
        globalCusp.ambientEmbedding.arithmetic.hom =
      localCusp.ambientEmbedding.arithmetic.hom ≫
        ambientDiagram.arithmetic.hom

/--
Scalar extension of the complete cusp atlas of a type-`(1,l-tors)` cover.

Unlike the selected-cusp localization, this quantifies over every nonzero
`Q`-label and every sign orbit.  The final squares assert that localization
commutes with the two structural operations used in Definition 1.1:
passage from `X`-cusps to `C`-cusps and inversion of sheets.
-/
structure TypeOneCuspidalAtlasScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    (coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack)
    (globalAtlas :
      TypeOneCuspidalAtlas l globalGroupData globalStack) where
  localAtlas :
    TypeOneCuspidalAtlas l
      coverExtension.localGroupData
      coverExtension.localStack
  sheetRepresentative_compatible :
    ∀ q,
      coverExtension.ellipticEmbedding.hom
          (localAtlas.sheetRepresentative q) =
        globalAtlas.sheetRepresentative q
  zeroX :
    CuspidalDecompositionScalarExtension K L
      coverExtension.localStack.xFundamentalGroups
      globalStack.xFundamentalGroups
      coverExtension.xFundamentalGroupDiagram
      localAtlas.zeroXCusp globalAtlas.zeroXCusp
  zeroC :
    CuspidalDecompositionScalarExtension K L
      coverExtension.localStack.cFundamentalGroups
      globalStack.cFundamentalGroups
      coverExtension.cFundamentalGroupDiagram
      localAtlas.zeroCCusp globalAtlas.zeroCCusp
  xCusps :
    ∀ q,
      CuspidalDecompositionScalarExtension K L
        coverExtension.localStack.xFundamentalGroups
        globalStack.xFundamentalGroups
        coverExtension.xFundamentalGroupDiagram
        (localAtlas.xCusps q) (globalAtlas.xCusps q)
  cCusps :
    ∀ q,
      CuspidalDecompositionScalarExtension K L
        coverExtension.localStack.cFundamentalGroups
        globalStack.cFundamentalGroups
        coverExtension.cFundamentalGroupDiagram
        (localAtlas.cCusps q) (globalAtlas.cCusps q)
  xToC_geometric_compatible :
    ∀ q,
      (xCusps q).diagram.geometric.hom ≫
          (globalAtlas.xToCCusp q).geometric.hom =
        (localAtlas.xToCCusp q).geometric.hom ≫
          (cCusps (EtaleTheta.toSignLabel q)).diagram.geometric.hom
  xToC_arithmetic_compatible :
    ∀ q,
      (xCusps q).diagram.arithmetic.hom ≫
          (globalAtlas.xToCCusp q).arithmetic.hom =
        (localAtlas.xToCCusp q).arithmetic.hom ≫
          (cCusps (EtaleTheta.toSignLabel q)).diagram.arithmetic.hom
  sign_geometric_compatible :
    ∀ q,
      (localAtlas.signCuspIsomorphism q).geometric.hom ≫
          (xCusps q⁻¹).diagram.geometric.hom =
        (xCusps q).diagram.geometric.hom ≫
          (globalAtlas.signCuspIsomorphism q).geometric.hom
  sign_arithmetic_compatible :
    ∀ q,
      (localAtlas.signCuspIsomorphism q).arithmetic.hom ≫
          (xCusps q⁻¹).diagram.arithmetic.hom =
        (xCusps q).diagram.arithmetic.hom ≫
          (globalAtlas.signCuspIsomorphism q).arithmetic.hom

/--
Scalar extension of the `Delta dagger` eigenspace construction.

The equivalence of dagger quotients is pinned to the actual local-to-global
geometric fundamental-group map.  Its restrictions to both eigenspaces and
the continuous positive quotient are therefore compatibility data, not
independent finite-group identifications.
-/
structure ArrowedCuspidalEigenspaceScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    (cuspExtension :
      TypeOneNonzeroCuspScalarExtension l K L
        coverExtension globalCusp)
    (globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp)
    (globalTopology :
      ArrowedPositiveProfiniteRealization l
        globalEigenspaces) where
  localEigenspaces :
    ArrowedCuspidalEigenspaceData l
      cuspExtension.localCusp
  localTopology :
    ArrowedPositiveProfiniteRealization l
      localEigenspaces
  daggerEquiv :
    cuspExtension.localCusp.ArrowedDelta ≃*
      globalCusp.ArrowedDelta
  daggerEquiv_projection :
    ∀ g,
      daggerEquiv
          (QuotientGroup.mk
            (EtaleTheta.modLEllipticProjection
              coverExtension.localStack.xFundamentalGroups.geometric.group
              l.value g)) =
        QuotientGroup.mk
          (EtaleTheta.modLEllipticProjection
            globalStack.xFundamentalGroups.geometric.group
            l.value
            (coverExtension.xFundamentalGroupDiagram.geometric.hom g))
  inversion_compatible :
    ∀ d,
      daggerEquiv (localEigenspaces.inversion d) =
        globalEigenspaces.inversion (daggerEquiv d)
  positiveEquiv :
    localEigenspaces.positiveEigenspace ≃*
      globalEigenspaces.positiveEigenspace
  positiveEquiv_inclusion :
    globalEigenspaces.positiveEigenspace.subtype.comp
        positiveEquiv.toMonoidHom =
      daggerEquiv.toMonoidHom.comp
        localEigenspaces.positiveEigenspace.subtype
  positiveCoordinates_compatible :
    ∀ q,
      globalEigenspaces.positiveRankOne
          (positiveEquiv q) =
        localEigenspaces.positiveRankOne q
  negativeEquiv :
    localEigenspaces.negativeEigenspace ≃*
      globalEigenspaces.negativeEigenspace
  negativeEquiv_inclusion :
    globalEigenspaces.negativeEigenspace.subtype.comp
        negativeEquiv.toMonoidHom =
      daggerEquiv.toMonoidHom.comp
        localEigenspaces.negativeEigenspace.subtype
  geometricPositiveQuotient_compatible :
    ∀ g,
      positiveEquiv
          (localEigenspaces.geometricPositiveQuotient g) =
        globalEigenspaces.geometricPositiveQuotient
          (coverExtension.xFundamentalGroupDiagram.geometric.hom g)
  profinitePositiveQuotient_compatible :
    ∀ g,
      globalTopology.geometricProjection
          (coverExtension.xFundamentalGroupDiagram.geometric.hom g) =
        localTopology.geometricProjection g

/--
Scalar extension of the intermediate `J_X -> J_C` quotients and the section
determined by `2 epsilon`.
-/
structure ArrowedJQuotientScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {cuspExtension :
      TypeOneNonzeroCuspScalarExtension l K L
        coverExtension globalCusp}
    {globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp}
    {globalTopology :
      ArrowedPositiveProfiniteRealization l
        globalEigenspaces}
    (eigenspaceExtension :
      ArrowedCuspidalEigenspaceScalarExtension l K L
        cuspExtension globalEigenspaces globalTopology)
    (globalJ :
      ArrowedJQuotientData l globalTopology) where
  localJ :
    ArrowedJQuotientData l
      eigenspaceExtension.localTopology
  jXDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      (ArrowedPositiveProfiniteGroup.{u} l)
      localJ.jX localOrbicurves.absoluteGalois
      (ArrowedPositiveProfiniteGroup.{u} l)
      globalJ.jX globalOrbicurves.absoluteGalois
      localJ.xExact globalJ.xExact
  jCDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      (ArrowedCGeometricProfiniteGroup.{u} l)
      localJ.jC localOrbicurves.absoluteGalois
      (ArrowedCGeometricProfiniteGroup.{u} l)
      globalJ.jC globalOrbicurves.absoluteGalois
      localJ.cExact globalJ.cExact
  jX_geometric_eq_id :
    jXDiagram.geometric.hom =
      𝟙 (ArrowedPositiveProfiniteGroup.{u} l)
  jC_geometric_eq_id :
    jCDiagram.geometric.hom =
      𝟙 (ArrowedCGeometricProfiniteGroup.{u} l)
  jX_galois_eq :
    jXDiagram.galois = coverExtension.galoisEmbedding
  jC_galois_eq :
    jCDiagram.galois = coverExtension.galoisEmbedding
  xQuotient_square :
    localJ.xQuotient ≫ jXDiagram.arithmetic.hom =
      coverExtension.xFundamentalGroupDiagram.arithmetic.hom ≫
        globalJ.xQuotient
  cGeometricQuotient_square :
    localJ.cGeometricQuotient ≫ jCDiagram.geometric.hom =
      coverExtension.cFundamentalGroupDiagram.geometric.hom ≫
        globalJ.cGeometricQuotient
  cQuotient_square :
    localJ.cQuotient ≫ jCDiagram.arithmetic.hom =
      coverExtension.cFundamentalGroupDiagram.arithmetic.hom ≫
        globalJ.cQuotient
  doubledCuspSection_square :
    localJ.doubledCuspSection ≫ jCDiagram.arithmetic.hom =
      coverExtension.galoisEmbedding.hom ≫
        globalJ.doubledCuspSection
  doubledCuspSectionLift_square :
    localJ.doubledCuspSectionLift ≫ jXDiagram.arithmetic.hom =
      coverExtension.galoisEmbedding.hom ≫
        globalJ.doubledCuspSectionLift

/--
Scalar extension of the arrowed finite-etale stacks at a good finite place.
-/
structure ArrowedTypeOneStackScalarExtension
    (l : PrimeGeFive)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {globalCurve : PuncturedEllipticCurve K}
    {localCurve : PuncturedEllipticCurve L}
    {globalOrbicurves :
      SignQuotientOrbicurveData K globalCurve}
    {localOrbicurves :
      SignQuotientOrbicurveData L localCurve}
    {baseChange :
      SignQuotientOrbicurveBaseChange K L
        globalOrbicurves localOrbicurves}
    {globalGroupData :
      GlobalLTorsionCoverInput l globalOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {coverExtension :
      TypeOneLTorsionStackScalarExtension l K L
        baseChange globalGroupData globalStack}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {cuspExtension :
      TypeOneNonzeroCuspScalarExtension l K L
        coverExtension globalCusp}
    {globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp}
    {globalTopology :
      ArrowedPositiveProfiniteRealization l
        globalEigenspaces}
    {eigenspaceExtension :
      ArrowedCuspidalEigenspaceScalarExtension l K L
        cuspExtension globalEigenspaces globalTopology}
    {globalJ :
      ArrowedJQuotientData l globalTopology}
    (jExtension :
      ArrowedJQuotientScalarExtension l K L
        eigenspaceExtension globalJ)
    (globalArrowed :
      ArrowedTypeOneStackRealization l
        globalEigenspaces globalTopology globalJ) where
  localArrowed :
    ArrowedTypeOneStackRealization l
      eigenspaceExtension.localEigenspaces
      eigenspaceExtension.localTopology
      jExtension.localJ
  arrowXExtension :
    OrbicurveScalarExtension K L globalArrowed.arrowX
  arrowCExtension :
    OrbicurveScalarExtension K L globalArrowed.arrowC
  arrowX_eq_scalarExtension :
    localArrowed.arrowX = arrowXExtension.result
  arrowC_eq_scalarExtension :
    localArrowed.arrowC = arrowCExtension.result
  xToBaseExtension :
    OrbicurveMorphismScalarExtension K L
      arrowXExtension coverExtension.xCoverExtension
      globalArrowed.xToBase
  xToBase_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        arrowX_eq_scalarExtension
        coverExtension.xCover_eq_scalarExtension
        localArrowed.xToBase =
      xToBaseExtension.result
  cToBaseExtension :
    OrbicurveMorphismScalarExtension K L
      arrowCExtension coverExtension.cCoverExtension
      globalArrowed.cToBase
  cToBase_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        arrowC_eq_scalarExtension
        coverExtension.cCover_eq_scalarExtension
        localArrowed.cToBase =
      cToBaseExtension.result
  quotientMapExtension :
    OrbicurveMorphismScalarExtension K L
      arrowXExtension arrowCExtension
      globalArrowed.quotientMap
  quotientMap_eq_scalarExtension :
    HyperbolicOrbicurve.Hom.cast
        arrowX_eq_scalarExtension arrowC_eq_scalarExtension
        localArrowed.quotientMap =
      quotientMapExtension.result
  xFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localArrowed.xFundamentalGroups.geometric.group
      localArrowed.xFundamentalGroups.arithmetic.group
      localOrbicurves.absoluteGalois
      globalArrowed.xFundamentalGroups.geometric.group
      globalArrowed.xFundamentalGroups.arithmetic.group
      globalOrbicurves.absoluteGalois
      localArrowed.xFundamentalGroups.exactSequence
      globalArrowed.xFundamentalGroups.exactSequence
  cFundamentalGroupDiagram :
    ProfiniteFundamentalExactSequenceEmbedding
      localArrowed.cFundamentalGroups.geometric.group
      localArrowed.cFundamentalGroups.arithmetic.group
      localOrbicurves.absoluteGalois
      globalArrowed.cFundamentalGroups.geometric.group
      globalArrowed.cFundamentalGroups.arithmetic.group
      globalOrbicurves.absoluteGalois
      localArrowed.cFundamentalGroups.exactSequence
      globalArrowed.cFundamentalGroups.exactSequence
  xDiagram_galois_eq :
    xFundamentalGroupDiagram.galois =
      coverExtension.galoisEmbedding
  cDiagram_galois_eq :
    cFundamentalGroupDiagram.galois =
      coverExtension.galoisEmbedding
  xToBase_arithmetic_square :
    localArrowed.xToBaseFundamentalGroupInclusion.arithmetic.hom ≫
        coverExtension.xFundamentalGroupDiagram.arithmetic.hom =
      xFundamentalGroupDiagram.arithmetic.hom ≫
        globalArrowed.xToBaseFundamentalGroupInclusion.arithmetic.hom
  cToBase_arithmetic_square :
    localArrowed.cToBaseFundamentalGroupInclusion.arithmetic.hom ≫
        coverExtension.cFundamentalGroupDiagram.arithmetic.hom =
      cFundamentalGroupDiagram.arithmetic.hom ≫
        globalArrowed.cToBaseFundamentalGroupInclusion.arithmetic.hom
  xToC_arithmetic_square :
    localArrowed.xToCFundamentalGroupInclusion.arithmetic.hom ≫
        cFundamentalGroupDiagram.arithmetic.hom =
      xFundamentalGroupDiagram.arithmetic.hom ≫
        globalArrowed.xToCFundamentalGroupInclusion.arithmetic.hom

/-- Finite-place specialization of a realized type-`(1,l-tors)` cover. -/
abbrev SourceThetaFiniteLTorsionCoverScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    (localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v)
    (globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves)
    (globalStack :
      TypeOneLTorsionStackRealization
        l globalGroupData) :=
  TypeOneLTorsionStackScalarExtension l K
    (ThetaFinitePlace.Completion v)
    localCore.baseChange globalGroupData globalStack

/-- Archimedean specialization of a realized type-`(1,l-tors)` cover. -/
abbrev SourceThetaInfiniteLTorsionCoverScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.InfinitePlace K}
    (localCore :
      SourceThetaInfiniteLocalCoreData
        K curve kOrbicurves v)
    (globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves)
    (globalStack :
      TypeOneLTorsionStackRealization
        l globalGroupData) :=
  TypeOneLTorsionStackScalarExtension l K
    (ThetaInfinitePlace.Completion v)
    localCore.baseChange globalGroupData globalStack

/-- Finite-place transport of the complete cusp atlas. -/
abbrev SourceThetaFiniteCuspidalAtlasScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    (coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack)
    (globalAtlas :
      TypeOneCuspidalAtlas l globalGroupData globalStack) :=
  TypeOneCuspidalAtlasScalarExtension l K
    (ThetaFinitePlace.Completion v)
    coverExtension globalAtlas

/-- Archimedean transport of the complete cusp atlas. -/
abbrev SourceThetaInfiniteCuspidalAtlasScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.InfinitePlace K}
    {localCore :
      SourceThetaInfiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    (coverExtension :
      SourceThetaInfiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack)
    (globalAtlas :
      TypeOneCuspidalAtlas l globalGroupData globalStack) :=
  TypeOneCuspidalAtlasScalarExtension l K
    (ThetaInfinitePlace.Completion v)
    coverExtension globalAtlas

/-- Finite-place transport of a chosen nonzero cusp. -/
abbrev SourceThetaFiniteNonzeroCuspScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization
        l globalGroupData}
    (coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack)
    (globalCusp :
      TypeOneNonzeroCusp
        l globalGroupData globalStack) :=
  TypeOneNonzeroCuspScalarExtension l K
    (ThetaFinitePlace.Completion v)
    coverExtension globalCusp

/-- Archimedean transport of a chosen nonzero cusp. -/
abbrev SourceThetaInfiniteNonzeroCuspScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.InfinitePlace K}
    {localCore :
      SourceThetaInfiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization
        l globalGroupData}
    (coverExtension :
      SourceThetaInfiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack)
    (globalCusp :
      TypeOneNonzeroCusp
        l globalGroupData globalStack) :=
  TypeOneNonzeroCuspScalarExtension l K
    (ThetaInfinitePlace.Completion v)
    coverExtension globalCusp

/-- Good finite-place transport of the dagger eigenspaces and positive quotient. -/
abbrev SourceThetaGoodFiniteArrowedEigenspaceScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack}
    (cuspExtension :
      SourceThetaFiniteNonzeroCuspScalarExtension
        l coverExtension globalCusp)
    (globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp)
    (globalTopology :
      ArrowedPositiveProfiniteRealization l globalEigenspaces) :=
  ArrowedCuspidalEigenspaceScalarExtension l K
    (ThetaFinitePlace.Completion v)
    cuspExtension globalEigenspaces globalTopology

/-- Good finite-place transport of `J_X`, `J_C`, and the doubled-cusp section. -/
abbrev SourceThetaGoodFiniteArrowedJScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack}
    {cuspExtension :
      SourceThetaFiniteNonzeroCuspScalarExtension
        l coverExtension globalCusp}
    {globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp}
    {globalTopology :
      ArrowedPositiveProfiniteRealization l globalEigenspaces}
    (eigenspaceExtension :
      SourceThetaGoodFiniteArrowedEigenspaceScalarExtension
        l cuspExtension globalEigenspaces globalTopology)
    (globalJ :
      ArrowedJQuotientData l globalTopology) :=
  ArrowedJQuotientScalarExtension l K
    (ThetaFinitePlace.Completion v)
    eigenspaceExtension globalJ

/-- Good finite-place scalar extension of the two arrowed orbicurve stacks. -/
abbrev SourceThetaGoodFiniteArrowedStackScalarExtension
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData
        K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack}
    {cuspExtension :
      SourceThetaFiniteNonzeroCuspScalarExtension
        l coverExtension globalCusp}
    {globalEigenspaces :
      ArrowedCuspidalEigenspaceData l globalCusp}
    {globalTopology :
      ArrowedPositiveProfiniteRealization l globalEigenspaces}
    {eigenspaceExtension :
      SourceThetaGoodFiniteArrowedEigenspaceScalarExtension
        l cuspExtension globalEigenspaces globalTopology}
    {globalJ :
      ArrowedJQuotientData l globalTopology}
    (jExtension :
      SourceThetaGoodFiniteArrowedJScalarExtension
        l eigenspaceExtension globalJ)
    (globalArrowed :
      ArrowedTypeOneStackRealization l
        globalEigenspaces globalTopology globalJ) :=
  ArrowedTypeOneStackScalarExtension l K
    (ThetaFinitePlace.Completion v)
    jExtension globalArrowed

/--
Stack realization of the type-`(1,l-torsTheta)` cover and its sign quotient
from Etale Theta, Proposition 2.2 and Definition 2.3.

The arithmetic group is fixed to the derived open theta-root subgroup. The
sign quotient, cartesian square, and both open fundamental-group inclusions
are part of the realization rather than inferred from unrelated identifiers.
-/
structure ThetaRootStackRealization
    (l : PrimeGeFive)
    {K : Type u} [Field K]
    {curve : PuncturedEllipticCurve K}
    {orbicurves : SignQuotientOrbicurveData K curve}
    (groupData : GlobalLTorsionCoverInput l orbicurves) where
  xTheta : HyperbolicOrbicurve K
  cTheta : HyperbolicOrbicurve K
  xToBase : xTheta.Hom orbicurves.xF
  cToBase : cTheta.Hom orbicurves.cF
  signAction : OrbicurveSignAction xTheta
  quotientMap : xTheta.Hom cTheta
  quotientInvariant :
    OrbicurveSignInvariantMorphism signAction cTheta
  quotientInvariant_map :
    quotientInvariant.map = quotientMap
  quotientUniversal :
    OrbicurveSignQuotientWitness
      signAction quotientInvariant
  coverSquare :
    OrbicurveSquare xTheta orbicurves.xF
      cTheta orbicurves.cF
  coverSquare_toX :
    coverSquare.toX = xToBase
  coverSquare_toY :
    coverSquare.toY = quotientMap
  coverSquare_xToBase :
    coverSquare.xToBase = orbicurves.quotientMap
  coverSquare_yToBase :
    coverSquare.yToBase = cToBase
  cartesian :
    coverSquare.TwoPullbackWitness
  xFundamentalGroups :
    OrbicurveFundamentalGroupData xTheta
      orbicurves.absoluteGalois
  cFundamentalGroups :
    OrbicurveFundamentalGroupData cTheta
      orbicurves.absoluteGalois
  xThetaArithmeticGroup_identification :
    xFundamentalGroups.arithmetic.group ≅
      groupData.thetaRootProfiniteGroup
  xThetaGeometricGroup_identification :
    xFundamentalGroups.geometric.group ≅
      groupData.negativeEigenspaceProfiniteGroup
  xToCThetaFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      xFundamentalGroups.geometric.group
      xFundamentalGroups.arithmetic.group
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      xFundamentalGroups.exactSequence
      cFundamentalGroups.exactSequence
  cThetaToBaseFundamentalGroupInclusion :
    ProfiniteFundamentalGroupInclusion
      cFundamentalGroups.geometric.group
      cFundamentalGroups.arithmetic.group
      orbicurves.cFundamentalGroups.geometric.group
      orbicurves.cFundamentalGroups.arithmetic.group
      orbicurves.absoluteGalois
      cFundamentalGroups.exactSequence
      orbicurves.cFundamentalGroups.exactSequence
  signInvolution :
    cFundamentalGroups.geometric.group
  signInvolution_orderTwo :
    signInvolution ^ 2 = 1
  signInvolution_outside_xTheta :
    signInvolution ∉
      Set.range
        xToCThetaFundamentalGroupInclusion.geometric.hom
  signInvolution_normalizes_xTheta :
    NormalizesProfiniteEmbeddingImage
      xToCThetaFundamentalGroupInclusion.geometric
      signInvolution
  signArithmeticAction :
    xFundamentalGroups.arithmetic.group ≃*
      xFundamentalGroups.arithmetic.group
  signArithmeticAction_involutive :
    signArithmeticAction.trans signArithmeticAction =
      MulEquiv.refl xFundamentalGroups.arithmetic.group
  signArithmeticAction_is_conjugation :
    ∀ g,
      xToCThetaFundamentalGroupInclusion.arithmetic.hom
          (signArithmeticAction g) =
        cFundamentalGroups.exactSequence.inclusion signInvolution *
          xToCThetaFundamentalGroupInclusion.arithmetic.hom g *
          (cFundamentalGroups.exactSequence.inclusion
            signInvolution)⁻¹
  orderTwo_admissible_iff_signCoset :
    ∀ element,
      element ∉
          Set.range
            xToCThetaFundamentalGroupInclusion.geometric.hom →
      NormalizesProfiniteEmbeddingImage
          xToCThetaFundamentalGroupInclusion.geometric
          element →
      (element ^ 2 = 1 ↔
        ∃ x,
          element =
            signInvolution *
              xToCThetaFundamentalGroupInclusion.geometric.hom x)
  cThetaArithmetic_generated :
    Subgroup.closure
        (Set.range
            xToCThetaFundamentalGroupInclusion.arithmetic.hom ∪
          {cFundamentalGroups.exactSequence.inclusion
            signInvolution}) =
      ⊤

/--
Bad-place standard type `(1,Z/lZ)^plusminus`: the local Lagrangian quotient
factors through the profinite Tate direction.

The selected cuspidal splitting is compatible with the cuspidal sign
structure, as required by Etale Theta, Definition 2.5(i).
-/
structure SourceThetaBadLocalStandardData
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    (localCore :
      SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    (coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack)
    (cuspExtension :
      SourceThetaFiniteNonzeroCuspScalarExtension
        l coverExtension globalCusp) where
  tateFactorization :
    EtaleTheta.TateFactorizedLagrangian
      l.value coverExtension.localGroupData.piEll
      coverExtension.localGroupData.profiniteLagrangian
  cuspidalSign :
    EtaleTheta.CuspidalSignStructure
      coverExtension.localGroupData.cuspSequence
  splittingSignCompatible :
    EtaleTheta.SignCompatibleThetaRootSplitting
      coverExtension.localGroupData.thetaRoot cuspidalSign
  epsilonCanonical :
    cuspExtension.localCusp.signLabel =
      EtaleTheta.canonicalTateSignLabel l.value
        (lt_of_lt_of_le (by decide : 1 < 5) l.ge_five)

namespace SourceThetaBadLocalStandardData

variable
    {l : PrimeGeFive}
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    {localCore :
      SourceThetaFiniteLocalCoreData K curve kOrbicurves v}
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    {globalCusp :
      TypeOneNonzeroCusp l globalGroupData globalStack}
    {coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack}
    {cuspExtension :
      SourceThetaFiniteNonzeroCuspScalarExtension
        l coverExtension globalCusp}
    (standard :
      SourceThetaBadLocalStandardData l localCore
        coverExtension cuspExtension)

/-- The theta-root subgroup as a closed subgroup of the local theta group. -/
noncomputable def thetaRootClosedSubgroup :
    ClosedSubgroup
      coverExtension.localGroupData.piEll :=
  coverExtension.localGroupData.thetaRootClosedSubgroup

/-- The profinite arithmetic group of the local theta-root cover. -/
noncomputable def thetaRootProfiniteGroup :
    ProfiniteGrp.{u} :=
  coverExtension.localGroupData.thetaRootProfiniteGroup

/-- The canonical continuous inclusion of the local theta-root group. -/
noncomputable def thetaRootInclusion :
    ProfiniteOpenEmbedding
      coverExtension.localGroupData.thetaRootProfiniteGroup
      coverExtension.localGroupData.piEll :=
  coverExtension.localGroupData.thetaRootInclusion

end SourceThetaBadLocalStandardData

/--
The bad-place orbicurves of type `(1,(Z/lZ)_Theta)` and
`(1,(Z/lZ)_Theta)^plusminus` from IUT I, Definition 3.1(e) and Etale Theta,
Definitions 2.3 and 2.5(i).

The arithmetic fundamental group of `xTheta` is identified with the profinite
group of the derived theta-root subgroup. The sign quotient and cartesian
square have their full bicategorical universal properties, and the group maps
form the required open-subgroup chain into the local base orbicurves.
-/
abbrev SourceThetaBadLocalThetaRootStackRealization
    (l : PrimeGeFive)
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    (localCore :
      SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    {globalGroupData :
      GlobalLTorsionCoverInput l kOrbicurves}
    {globalStack :
      TypeOneLTorsionStackRealization l globalGroupData}
    (coverExtension :
      SourceThetaFiniteLTorsionCoverScalarExtension
        l localCore globalGroupData globalStack) :=
  ThetaRootStackRealization l
    coverExtension.localGroupData

/--
The source-native arithmetic and global-cover core of initial theta data.

The `K`-core is an actual scalar extension of the curve and both orbicurve
stacks. The type-`(1,l-torsion)` and global/bad-local theta-root stack
realization interfaces include their quotient and pullback universal
properties; deriving these realizations as finite-etale covers remains an
explicit source obligation.
-/
structure SourceInitialThetaCore
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K] where
  l : PrimeGeFive
  fieldTower : ThetaFieldTower l Fmod F K
  curveModuli : SourceThetaCurveModuliData Fmod F
  kCore :
    SourceThetaKCoreData F K
      curveModuli.xF curveModuli.signQuotient
  globalLTorsionCover :
    GlobalLTorsionCoverInput l kCore.orbicurves
  globalLTorsionStack :
    TypeOneLTorsionStackRealization l globalLTorsionCover
  epsilon :
    TypeOneNonzeroCusp l
      globalLTorsionCover globalLTorsionStack
  arrowedEigenspaces :
    ArrowedCuspidalEigenspaceData l epsilon
  arrowedPositiveTopology :
    ArrowedPositiveProfiniteRealization l
      arrowedEigenspaces
  arrowedJQuotients :
    ArrowedJQuotientData l
      arrowedPositiveTopology
  globalArrowedStack :
    ArrowedTypeOneStackRealization l
      arrowedEigenspaces arrowedPositiveTopology
      arrowedJQuotients
  globalThetaRootStack :
    ThetaRootStackRealization l globalLTorsionCover
  lTorsionRepresentation :
    ThetaLTorsionRepresentationData l F K curveModuli.xF
  lTorsionImageContainsSL2 :
    lTorsionRepresentation.ImageContainsSL2
  valuations : ThetaValuationData l Fmod K
  finiteLocalCores :
    ∀ v,
      SourceThetaFiniteLocalCoreData K
        kCore.curveExtension.result kCore.orbicurves v
  infiniteLocalCores :
    ∀ v,
      SourceThetaInfiniteLocalCoreData K
        kCore.curveExtension.result kCore.orbicurves v
  finiteLocalLTorsionCovers :
    ∀ v (_hv : v ∈ valuations.selected),
      SourceThetaFiniteLTorsionCoverScalarExtension l
        (finiteLocalCores v)
        globalLTorsionCover globalLTorsionStack
  infiniteLocalLTorsionCovers :
    ∀ v (_hv : v ∈ valuations.selectedInfinite),
      SourceThetaInfiniteLTorsionCoverScalarExtension l
        (infiniteLocalCores v)
        globalLTorsionCover globalLTorsionStack
  finiteLocalCuspidalAtlases :
    ∀ v (hv : v ∈ valuations.selected),
      SourceThetaFiniteCuspidalAtlasScalarExtension l
        (finiteLocalLTorsionCovers v hv) epsilon.atlas
  infiniteLocalCuspidalAtlases :
    ∀ v (hv : v ∈ valuations.selectedInfinite),
      SourceThetaInfiniteCuspidalAtlasScalarExtension l
        (infiniteLocalLTorsionCovers v hv) epsilon.atlas
  finiteLocalEpsilon :
    ∀ v (hv : v ∈ valuations.selected),
      SourceThetaFiniteNonzeroCuspScalarExtension l
        (finiteLocalLTorsionCovers v hv) epsilon
  infiniteLocalEpsilon :
    ∀ v (hv : v ∈ valuations.selectedInfinite),
      SourceThetaInfiniteNonzeroCuspScalarExtension l
        (infiniteLocalLTorsionCovers v hv) epsilon
  finiteLocalEpsilon_atlas_eq :
    ∀ v (hv : v ∈ valuations.selected),
      (finiteLocalEpsilon v hv).localCusp.atlas =
        (finiteLocalCuspidalAtlases v hv).localAtlas
  infiniteLocalEpsilon_atlas_eq :
    ∀ v (hv : v ∈ valuations.selectedInfinite),
      (infiniteLocalEpsilon v hv).localCusp.atlas =
        (infiniteLocalCuspidalAtlases v hv).localAtlas
  goodLocalArrowedEigenspaces :
    ∀ v (hv : v ∈ valuations.good),
      SourceThetaGoodFiniteArrowedEigenspaceScalarExtension l
        (finiteLocalEpsilon v hv.1)
        arrowedEigenspaces arrowedPositiveTopology
  goodLocalArrowedJQuotients :
    ∀ v (hv : v ∈ valuations.good),
      SourceThetaGoodFiniteArrowedJScalarExtension l
        (goodLocalArrowedEigenspaces v hv)
        arrowedJQuotients
  goodLocalArrowedStacks :
    ∀ v (hv : v ∈ valuations.good),
      SourceThetaGoodFiniteArrowedStackScalarExtension l
        (goodLocalArrowedJQuotients v hv)
        globalArrowedStack
  badLocalStandard :
    ∀ v (hv : v ∈ valuations.bad),
      SourceThetaBadLocalStandardData l
        (finiteLocalCores v)
        (finiteLocalLTorsionCovers v hv.1)
        (finiteLocalEpsilon v hv.1)
  badLocalThetaRootStacks :
    ∀ v (hv : v ∈ valuations.bad),
      SourceThetaBadLocalThetaRootStackRealization l
        (finiteLocalCores v)
        (finiteLocalLTorsionCovers v hv.1)
  fPlacesOverBadHaveMultiplicativeReduction :
    ∀ v : NumberField.FinitePlace F,
      ThetaFinitePlace.comap v ∈ valuations.badMod →
        curveModuli.xF.HasMultiplicativeReductionAt v
  fBadLocalCurves :
    ∀ v : NumberField.FinitePlace F,
      ThetaFinitePlace.comap v ∈ valuations.badMod →
        PuncturedEllipticCurveScalarExtension F
          (ThetaFinitePlace.Completion v) curveModuli.xF
  fBadQParameters :
    ∀ v (hv : ThetaFinitePlace.comap v ∈ valuations.badMod),
      ThetaTateParameterData
        v (fBadLocalCurves v hv).result
  fBadQParameterOrdersPrimeToL :
    ∀ v hv,
      Nat.Coprime (fBadQParameters v hv).order l.value
  badLiftsHaveMultiplicativeReduction :
    ∀ v, v ∈ valuations.bad →
      curveModuli.xF.HasMultiplicativeReductionAtBaseChange v
  qParameters :
    ∀ v (_hv : v ∈ valuations.bad),
      ThetaTateParameterData
        v (finiteLocalCores v).curveLocal.result
  qParameterOrdersPrimeToL :
    ∀ v hv,
      Nat.Coprime (qParameters v hv).order l.value

namespace SourceInitialThetaCore

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable (theta : SourceInitialThetaCore Fmod F K)

theorem xF_stableReductionEverywhere :
    theta.curveModuli.xF.HasStableReductionEverywhere :=
  theta.curveModuli.stableReduction

theorem xF_torsion23Rational :
    theta.curveModuli.xF.Torsion23Rational :=
  theta.curveModuli.torsion23Rational

theorem k_is_kernel_field :
    theta.lTorsionRepresentation.IsKernelField :=
  theta.lTorsionRepresentation.isKernelField

theorem image_contains_SL2 :
    theta.lTorsionRepresentation.ImageContainsSL2 :=
  theta.lTorsionImageContainsSL2

theorem finiteLocalEpsilon_signLabel
    (v : NumberField.FinitePlace K)
    (hv : v ∈ theta.valuations.selected) :
    (theta.finiteLocalEpsilon v hv).localCusp.signLabel =
      theta.epsilon.signLabel :=
  (theta.finiteLocalEpsilon v hv).signLabel_eq

theorem infiniteLocalEpsilon_signLabel
    (v : NumberField.InfinitePlace K)
    (hv : v ∈ theta.valuations.selectedInfinite) :
    (theta.infiniteLocalEpsilon v hv).localCusp.signLabel =
      theta.epsilon.signLabel :=
  (theta.infiniteLocalEpsilon v hv).signLabel_eq

theorem badLocalEpsilon_canonical
    (v : NumberField.FinitePlace K)
    (hv : v ∈ theta.valuations.bad) :
    (theta.finiteLocalEpsilon v hv.1).localCusp.signLabel =
      EtaleTheta.canonicalTateSignLabel theta.l.value
        (lt_of_lt_of_le (by decide : 1 < 5)
          theta.l.ge_five) :=
  (theta.badLocalStandard v hv).epsilonCanonical

theorem globalEpsilon_canonicalAtBad
    (v : NumberField.FinitePlace K)
    (hv : v ∈ theta.valuations.bad) :
    theta.epsilon.signLabel =
      EtaleTheta.canonicalTateSignLabel theta.l.value
        (lt_of_lt_of_le (by decide : 1 < 5)
          theta.l.ge_five) :=
  (theta.finiteLocalEpsilon_signLabel v hv.1).symm.trans
    (theta.badLocalEpsilon_canonical v hv)

theorem q_orders_prime_to_l :
    ∀ v hv,
      Nat.Coprime (theta.qParameters v hv).order
        theta.l.value :=
  theta.qParameterOrdersPrimeToL

end SourceInitialThetaCore

end Iut
