/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
Initial theta data from IUT I, Definition 3.1.

This is the first math-facing layer of the project.  It deliberately uses
mathlib objects when they are available: number fields, algebraic closures,
finite Galois extensions, natural-number primality, and Weierstrass elliptic
curves.  Objects not yet available in the needed IUT form, such as hyperbolic
orbicurves and the full local reduction theory, are represented by typed
records with named proof obligations.
-/

namespace Iut

universe u

/-- A prime number `l` satisfying the IUT lower bound `5 <= l`. -/
structure PrimeGeFive where
  value : ℕ
  prime : Nat.Prime value
  ge_five : 5 ≤ value

namespace PrimeGeFive

theorem ne_zero (l : PrimeGeFive) : l.value ≠ 0 :=
  l.prime.ne_zero

theorem ne_one (l : PrimeGeFive) : l.value ≠ 1 :=
  l.prime.ne_one

theorem ne_two (l : PrimeGeFive) : l.value ≠ 2 := by
  intro h
  have hlt : l.value < 5 := by
    omega
  exact (not_lt_of_ge l.ge_five) hlt

end PrimeGeFive

/-- The condition `sqrt(-1) in F` from IUT I, Definition 3.1(a). -/
structure SqrtMinusOneData (F : Type u) [Field F] where
  element : F
  square_eq_neg_one : element ^ 2 = -1

/--
The field tower `Fmod ⊆ F ⊆ K` appearing in IUT I, Definition 3.1(b),(c).

The source requires `F/Fmod` to be Galois of degree prime to `l`, and `K/F` to
be a finite Galois extension.  The finite-dimensional and Galois parts are
typeclass hypotheses; the prime-to-`l` degree condition is a field of the
record because it depends on the chosen prime.
-/
structure ThetaFieldTower
    (l : PrimeGeFive) (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K] where
  sqrtMinusOne : SqrtMinusOneData F
  degreePrimeToL_holds :
    Nat.Coprime (Module.finrank Fmod F) l.value

namespace ThetaFieldTower

variable {l : PrimeGeFive}
variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable (tower : ThetaFieldTower l Fmod F K)

theorem sqrtMinusOne_square :
    tower.sqrtMinusOne.element ^ 2 = (-1 : F) :=
  tower.sqrtMinusOne.square_eq_neg_one

theorem degreePrimeToL (tower : ThetaFieldTower l Fmod F K) :
    Nat.Coprime (Module.finrank Fmod F) l.value :=
  ThetaFieldTower.degreePrimeToL_holds tower

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [IsGalois Fmod F] [FiniteDimensional F K] [IsGalois F K] in
theorem f_over_fmod_is_finiteDimensional : FiniteDimensional Fmod F :=
  inferInstance

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [FiniteDimensional Fmod F] [FiniteDimensional F K]
    [IsGalois F K] in
theorem f_over_fmod_is_galois : IsGalois Fmod F :=
  inferInstance

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra Fmod F] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [IsGalois F K] in
theorem k_over_f_is_finiteDimensional : FiniteDimensional F K :=
  inferInstance

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra Fmod F] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] in
theorem k_over_f_is_galois : IsGalois F K :=
  inferInstance

end ThetaFieldTower

/--
A once-punctured elliptic curve represented by its ambient Weierstrass elliptic
curve and a label for the removed point.

The label is not intended to carry geometry.  It keeps the formal record close
to Definition 3.1 while the later curve/open-subscheme layer is developed.
-/
structure PuncturedEllipticCurve (F : Type u) [Field F] where
  curve : WeierstrassCurve F
  isElliptic : curve.IsElliptic
  punctureLabel : String

namespace PuncturedEllipticCurve

instance {F : Type u} [Field F] (X : PuncturedEllipticCurve F) :
    X.curve.IsElliptic :=
  X.isElliptic

/-- The `j`-invariant of the ambient elliptic curve. -/
noncomputable def jInvariant {F : Type u} [Field F] (X : PuncturedEllipticCurve F) :
    F := by
  letI := X.isElliptic
  exact X.curve.j

/-- A concrete source of punctured elliptic curves from mathlib's `ofJ` model. -/
noncomputable def ofJ (F : Type u) [Field F] [DecidableEq F] (j : F) :
    PuncturedEllipticCurve F where
  curve := WeierstrassCurve.ofJ j
  isElliptic := inferInstance
  punctureLabel := "origin"

theorem jInvariant_ofJ (F : Type u) [Field F] [DecidableEq F] (j : F) :
    (ofJ F j).jInvariant = j := by
  dsimp [jInvariant, ofJ]
  exact WeierstrassCurve.ofJ_j j

end PuncturedEllipticCurve

/--
The valuation data `V`, `Vbad_mod`, and the section `V -> Vmod` from
Definition 3.1(b),(e).

The moduli-level and extension-level valuation types are now mathlib finite
places of the corresponding number fields.  The map from places of `K` to
places of `Fmod`, together with a chosen section, remains explicit data.
-/
structure ThetaValuationData
    (l : PrimeGeFive) (Fmod K : Type u)
    [Field Fmod] [NumberField Fmod] [Field K] [NumberField K]
    [Algebra Fmod K] where
  toModuli : NumberField.FinitePlace K -> NumberField.FinitePlace Fmod
  chosenLift : NumberField.FinitePlace Fmod -> NumberField.FinitePlace K
  toModuli_chosenLift : ∀ w, toModuli (chosenLift w) = w
  residueCharacteristic : NumberField.FinitePlace Fmod -> ℕ
  badMod : Set (NumberField.FinitePlace Fmod)
  badMod_nonempty : ∃ w, w ∈ badMod
  badMod_oddResidueCharacteristic :
    ∀ w, w ∈ badMod -> Odd (residueCharacteristic w)
  badMod_residueCharacteristic_prime :
    ∀ w, w ∈ badMod -> Nat.Prime (residueCharacteristic w)
  badMod_residueCharacteristic_coprime_l :
    ∀ w, w ∈ badMod -> Nat.Coprime (residueCharacteristic w) l.value
  multiplicativeBadReductionAtLift : NumberField.FinitePlace K -> Prop
  bad_lifts_have_multiplicative_reduction :
    ∀ v, v ∈ Set.range chosenLift -> toModuli v ∈ badMod ->
      multiplicativeBadReductionAtLift v

namespace ThetaValuationData

variable {l : PrimeGeFive} {Fmod K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field K] [NumberField K]
variable [Algebra Fmod K]

/-- The selected subset `V ⊆ V(K)` supplied by the section. -/
def selected (data : ThetaValuationData l Fmod K) :
    Set (NumberField.FinitePlace K) :=
  Set.range data.chosenLift

/-- The good valuations at the moduli level, i.e. the complement of `Vbad_mod`. -/
def goodMod (data : ThetaValuationData l Fmod K) :
    Set (NumberField.FinitePlace Fmod) :=
  data.badModᶜ

/-- The bad valuations in the chosen section `V`. -/
def bad (data : ThetaValuationData l Fmod K) :
    Set (NumberField.FinitePlace K) :=
  {v | v ∈ data.selected ∧ data.toModuli v ∈ data.badMod}

/-- The good valuations in the chosen section `V`. -/
def good (data : ThetaValuationData l Fmod K) :
    Set (NumberField.FinitePlace K) :=
  {v | v ∈ data.selected ∧ data.toModuli v ∈ data.goodMod}

theorem mem_selected_iff (data : ThetaValuationData l Fmod K)
    (v : NumberField.FinitePlace K) :
    v ∈ data.selected ↔ ∃ w, data.chosenLift w = v :=
  Iff.rfl

theorem chosenLift_mem_selected (data : ThetaValuationData l Fmod K)
    (w : NumberField.FinitePlace Fmod) :
    data.chosenLift w ∈ data.selected :=
  ⟨w, rfl⟩

theorem toModuli_chosenLift_eq (data : ThetaValuationData l Fmod K)
    (w : NumberField.FinitePlace Fmod) :
    data.toModuli (data.chosenLift w) = w :=
  data.toModuli_chosenLift w

theorem mem_bad_iff (data : ThetaValuationData l Fmod K)
    (v : NumberField.FinitePlace K) :
    v ∈ data.bad ↔ v ∈ data.selected ∧ data.toModuli v ∈ data.badMod :=
  Iff.rfl

theorem mem_good_iff (data : ThetaValuationData l Fmod K)
    (v : NumberField.FinitePlace K) :
    v ∈ data.good ↔ v ∈ data.selected ∧ data.toModuli v ∉ data.badMod :=
  Iff.rfl

theorem chosenLift_mem_bad_iff (data : ThetaValuationData l Fmod K)
    (w : NumberField.FinitePlace Fmod) :
    data.chosenLift w ∈ data.bad ↔ w ∈ data.badMod := by
  simp [bad, selected, data.toModuli_chosenLift_eq]

theorem bad_nonempty (data : ThetaValuationData l Fmod K) :
    ∃ v, v ∈ data.bad := by
  rcases data.badMod_nonempty with ⟨w, hw⟩
  exact ⟨data.chosenLift w, (data.chosenLift_mem_bad_iff w).mpr hw⟩

theorem badLift_has_multiplicative_reduction
    (data : ThetaValuationData l Fmod K)
    {v : NumberField.FinitePlace K} (hv : v ∈ data.bad) :
    data.multiplicativeBadReductionAtLift v :=
  data.bad_lifts_have_multiplicative_reduction v hv.1 hv.2

end ThetaValuationData

/-- A typed placeholder for the hyperbolic orbicurves `C_F`, `C_K`, etc. -/
structure HyperbolicOrbicurveModel (F : Type u) [Field F] where
  label : String
  typeLabel : String

/--
The curve/moduli portion of IUT I, Definition 3.1(b).

This records the once-punctured elliptic curve `X_F`, the quotient orbicurve
`C_F`, the assertion that `C_F` is obtained by quotienting by the unique
order-two involution `-1`, the field-of-moduli assertion for `Fmod`, stable
reduction over nonarchimedean valuations, and rationality of the `2 * 3`
torsion points of the ambient elliptic curve.
-/
structure ThetaCurveModuliData
    (Fmod F : Type u) [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Algebra Fmod F] where
  xF : PuncturedEllipticCurve F
  cF : HyperbolicOrbicurveModel F
  cF_is_quotient_by_neg_one : Prop
  cF_is_quotient_by_neg_one_holds : cF_is_quotient_by_neg_one
  fmod_is_fieldOfModuli : Prop
  fmod_is_fieldOfModuli_holds : fmod_is_fieldOfModuli
  stableReductionOverNonarchimedean : Prop
  stableReductionOverNonarchimedean_holds : stableReductionOverNonarchimedean
  torsion23RationalOverF : Prop
  torsion23RationalOverF_holds : torsion23RationalOverF

namespace ThetaCurveModuliData

variable {Fmod F : Type u} [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Algebra Fmod F]
variable (curveData : ThetaCurveModuliData Fmod F)

theorem quotientByNegOne :
    curveData.cF_is_quotient_by_neg_one :=
  curveData.cF_is_quotient_by_neg_one_holds

theorem fmodFieldOfModuli :
    curveData.fmod_is_fieldOfModuli :=
  curveData.fmod_is_fieldOfModuli_holds

theorem stableReduction :
    curveData.stableReductionOverNonarchimedean :=
  curveData.stableReductionOverNonarchimedean_holds

theorem torsion23Rational :
    curveData.torsion23RationalOverF :=
  curveData.torsion23RationalOverF_holds

end ThetaCurveModuliData

/--
The `C_K`/`X_K` covering data from IUT I, Definition 3.1(d).

This bundle ties `C_K` to the previously defined `C_F`: its `K`-core is the
base-change `C_F x_F K`, and it determines the corresponding `X_K` cover and
the finite etale/profinite group diagrams mentioned in the source.
-/
structure ThetaOrbicurveCoverData
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra Fmod F] [Algebra F K]
    (curveModuli : ThetaCurveModuliData Fmod F) where
  cK : HyperbolicOrbicurveModel K
  xK : HyperbolicOrbicurveModel K
  cK_has_type_l_tors_pm : Prop
  cK_has_type_l_tors_pm_holds : cK_has_type_l_tors_pm
  cK_core_is_baseChange_cF : Prop
  cK_core_is_baseChange_cF_holds : cK_core_is_baseChange_cF
  cK_determined_by_cF : Prop
  cK_determined_by_cF_holds : cK_determined_by_cF
  xK_has_type_l_tors : Prop
  xK_has_type_l_tors_holds : xK_has_type_l_tors
  finiteEtaleCoveringDiagrams : Prop
  finiteEtaleCoveringDiagrams_holds : finiteEtaleCoveringDiagrams
  profiniteGroupOpenImmersions : Prop
  profiniteGroupOpenImmersions_holds : profiniteGroupOpenImmersions

namespace ThetaOrbicurveCoverData

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K] [Algebra Fmod F] [Algebra F K]
variable {curveModuli : ThetaCurveModuliData Fmod F}
variable (coverData : ThetaOrbicurveCoverData Fmod F K curveModuli)

theorem cKType :
    coverData.cK_has_type_l_tors_pm :=
  coverData.cK_has_type_l_tors_pm_holds

theorem cKCoreBaseChange :
    coverData.cK_core_is_baseChange_cF :=
  coverData.cK_core_is_baseChange_cF_holds

theorem cKDeterminedByCF :
    coverData.cK_determined_by_cF :=
  coverData.cK_determined_by_cF_holds

theorem xKType :
    coverData.xK_has_type_l_tors :=
  coverData.xK_has_type_l_tors_holds

theorem finiteEtaleDiagrams :
    coverData.finiteEtaleCoveringDiagrams :=
  coverData.finiteEtaleCoveringDiagrams_holds

theorem openImmersions :
    coverData.profiniteGroupOpenImmersions :=
  coverData.profiniteGroupOpenImmersions_holds

end ThetaOrbicurveCoverData

/-- The cusp `epsilon` of `C_K` from IUT I, Definition 3.1(f). -/
structure CuspData {F : Type u} [Field F] (C : HyperbolicOrbicurveModel F) where
  label : String
  arisesFromNonzeroQuotientElement : Prop
  arisesFromNonzeroQuotientElement_holds : arisesFromNonzeroQuotientElement

/--
Initial theta data in the sense of IUT I, Definition 3.1.

This record captures the currently formalized core:
* `F` is a number field with a chosen square root of `-1`;
* `Fbar` is mathlib's algebraic closure `AlgebraicClosure F`;
* `X_F` is represented by a punctured Weierstrass elliptic curve over `F`;
* `l` is a prime at least five;
* `Fmod/F/K` is a number-field tower with the source Galois and degree
  prime-to-`l` conditions;
* `V -> Vmod` is a bijective valuation section with a nonempty bad moduli set;
* `C_K` and `epsilon` are explicit typed objects;
* not-yet-expanded source hypotheses remain named proof obligations.
-/
structure InitialThetaData
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K] where
  l : PrimeGeFive
  fieldTower : ThetaFieldTower l Fmod F K
  curveModuli : ThetaCurveModuliData Fmod F
  coverData : ThetaOrbicurveCoverData Fmod F K curveModuli
  k_is_lTorsionKernelField : Prop
  k_is_lTorsionKernelField_holds : k_is_lTorsionKernelField
  valuations : ThetaValuationData l Fmod K
  epsilon : CuspData coverData.cK
  lTorsionImageContainsSL2 : Prop
  lTorsionImageContainsSL2_holds : lTorsionImageContainsSL2
  qParameterOrdersPrimeToL : Prop
  qParameterOrdersPrimeToL_holds : qParameterOrdersPrimeToL

namespace InitialThetaData

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable (theta : InitialThetaData Fmod F K)

/-- The algebraic closure `Fbar` from Definition 3.1(a), using mathlib's construction. -/
abbrev algebraicClosure : Type u :=
  AlgebraicClosure F

omit [NumberField F] in
theorem algebraicClosure_isAlgClosure :
    IsAlgClosure F (AlgebraicClosure F) :=
  inferInstance

theorem base_is_numberField : NumberField F :=
  inferInstance

theorem extension_is_numberField : NumberField K :=
  inferInstance

omit [NumberField F] [NumberField K] [IsGalois F K] in
theorem extension_is_finiteDimensional : FiniteDimensional F K :=
  inferInstance

omit [NumberField F] [NumberField K] [FiniteDimensional F K] in
theorem extension_is_galois : IsGalois F K :=
  inferInstance

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [IsGalois Fmod F] [FiniteDimensional F K] [IsGalois F K] in
theorem moduli_extension_is_finiteDimensional : FiniteDimensional Fmod F :=
  inferInstance

omit [NumberField Fmod] [NumberField F] [NumberField K] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K] [FiniteDimensional Fmod F] [FiniteDimensional F K]
    [IsGalois F K] in
theorem moduli_extension_is_galois : IsGalois Fmod F :=
  inferInstance

theorem degree_F_over_Fmod_prime_to_l :
    Nat.Coprime (Module.finrank Fmod F) theta.l.value :=
  ThetaFieldTower.degreePrimeToL theta.fieldTower

theorem prime_is_prime : Nat.Prime theta.l.value :=
  theta.l.prime

theorem prime_ge_five : 5 ≤ theta.l.value :=
  theta.l.ge_five

theorem badValuations_nonempty :
    ∃ v, v ∈ theta.valuations.bad :=
  theta.valuations.bad_nonempty

theorem badValuation_has_multiplicative_reduction
    {v : NumberField.FinitePlace K} (hv : v ∈ theta.valuations.bad) :
    theta.valuations.multiplicativeBadReductionAtLift v :=
  theta.valuations.badLift_has_multiplicative_reduction hv

theorem sqrtMinusOne_square :
    theta.fieldTower.sqrtMinusOne.element ^ 2 = (-1 : F) :=
  theta.fieldTower.sqrtMinusOne_square

theorem fmodFieldOfModuli :
    theta.curveModuli.fmod_is_fieldOfModuli :=
  theta.curveModuli.fmodFieldOfModuli

theorem quotientByNegOne :
    theta.curveModuli.cF_is_quotient_by_neg_one :=
  theta.curveModuli.quotientByNegOne

theorem stableReductionOverNonarchimedean :
    theta.curveModuli.stableReductionOverNonarchimedean :=
  theta.curveModuli.stableReduction

theorem torsion23RationalOverF :
    theta.curveModuli.torsion23RationalOverF :=
  theta.curveModuli.torsion23Rational

theorem cKType :
    theta.coverData.cK_has_type_l_tors_pm :=
  theta.coverData.cKType

theorem cKCoreBaseChange :
    theta.coverData.cK_core_is_baseChange_cF :=
  theta.coverData.cKCoreBaseChange

theorem cKDeterminedByCF :
    theta.coverData.cK_determined_by_cF :=
  theta.coverData.cKDeterminedByCF

theorem xKType :
    theta.coverData.xK_has_type_l_tors :=
  theta.coverData.xKType

theorem finiteEtaleCoveringDiagrams :
    theta.coverData.finiteEtaleCoveringDiagrams :=
  theta.coverData.finiteEtaleDiagrams

theorem profiniteGroupOpenImmersions :
    theta.coverData.profiniteGroupOpenImmersions :=
  theta.coverData.openImmersions

theorem kIsLTorsionKernelField :
    theta.k_is_lTorsionKernelField :=
  theta.k_is_lTorsionKernelField_holds

theorem cusp_arisesFromNonzeroQuotientElement :
    theta.epsilon.arisesFromNonzeroQuotientElement :=
  theta.epsilon.arisesFromNonzeroQuotientElement_holds

end InitialThetaData

end Iut
