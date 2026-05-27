/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.InitialThetaData

/-!
Examples for the first formal slice of initial theta data.

These examples are intentionally small.  They verify the constructor and the
basic projections without pretending that a complete arithmetic example of IUT
initial data has already been supplied.
-/

namespace Iut

namespace InitialThetaDataExample

/-- The first admissible prime allowed by IUT I, Definition 3.1(c). -/
def primeFive : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

example : Nat.Prime primeFive.value :=
  primeFive.prime

example : 5 ≤ primeFive.value :=
  primeFive.ge_five

/--
A two-point valuation toy model.  This is only an example of the formal shape
`V -> Vmod`; it is not asserted to arise from a number field.
-/
def boolThetaValuationData : ThetaValuationData primeFive Bool Bool where
  toModuli := id
  toModuli_bijective := by
    constructor
    · intro a b h
      simpa using h
    · intro b
      exact ⟨b, rfl⟩
  residueCharacteristic := fun _ => 3
  isNonarchimedean := fun _ => True
  badMod := {w | w = true}
  badMod_nonempty := ⟨true, rfl⟩
  badMod_nonarchimedean := by
    intro _ _
    trivial
  badMod_oddResidueCharacteristic := by
    intro _ _
    norm_num [Odd]
  badMod_residueCharacteristic_prime := by
    intro _ _
    norm_num
  badMod_residueCharacteristic_coprime_l := by
    intro _ _
    norm_num [primeFive]
  multiplicativeBadReductionAtLift := fun v => v = true
  bad_lifts_have_multiplicative_reduction := by
    intro v hv
    simpa using hv

example : ∃ v, v ∈ boolThetaValuationData.bad :=
  boolThetaValuationData.bad_nonempty

example {v : Bool} (hv : v ∈ boolThetaValuationData.bad) :
    boolThetaValuationData.multiplicativeBadReductionAtLift v :=
  boolThetaValuationData.badLift_has_multiplicative_reduction hv

section AbstractConstructor

universe u

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable [DecidableEq F]

/-- A constructor smoke test for the field tower part of initial theta data. -/
def abstractThetaFieldTower
    (sqrtMinusOne : SqrtMinusOneData F)
    (hDegree : Nat.Coprime (Module.finrank Fmod F) primeFive.value) :
    ThetaFieldTower primeFive Fmod F K where
  sqrtMinusOne := sqrtMinusOne
  degreePrimeToL_holds := hDegree

/--
A constructor smoke test for full initial theta data under the exact field
hypotheses required by the record.
-/
noncomputable def abstractInitialThetaData
    (fieldTower : ThetaFieldTower primeFive Fmod F K)
    (cK : HyperbolicOrbicurveModel K)
    (epsilon : CuspData cK)
    (fmod_is_fieldOfModuli k_is_lTorsionKernelField
      stableReductionOverNonarchimedean torsion23RationalOverF
      lTorsionImageContainsSL2 qParameterOrdersPrimeToL : Prop)
    (hFmod : fmod_is_fieldOfModuli)
    (hK : k_is_lTorsionKernelField)
    (hStable : stableReductionOverNonarchimedean)
    (hTorsion : torsion23RationalOverF)
    (hImage : lTorsionImageContainsSL2)
    (hQ : qParameterOrdersPrimeToL) :
    InitialThetaData Fmod F K Bool Bool where
  l := primeFive
  fieldTower := fieldTower
  xF := PuncturedEllipticCurve.ofJ F (37 : F)
  fmod_is_fieldOfModuli := fmod_is_fieldOfModuli
  fmod_is_fieldOfModuli_holds := hFmod
  cK := cK
  k_is_lTorsionKernelField := k_is_lTorsionKernelField
  k_is_lTorsionKernelField_holds := hK
  valuations := boolThetaValuationData
  epsilon := epsilon
  stableReductionOverNonarchimedean := stableReductionOverNonarchimedean
  stableReductionOverNonarchimedean_holds := hStable
  torsion23RationalOverF := torsion23RationalOverF
  torsion23RationalOverF_holds := hTorsion
  lTorsionImageContainsSL2 := lTorsionImageContainsSL2
  lTorsionImageContainsSL2_holds := hImage
  qParameterOrdersPrimeToL := qParameterOrdersPrimeToL
  qParameterOrdersPrimeToL_holds := hQ

variable (theta : InitialThetaData Fmod F K Bool Bool)

example : Nat.Prime theta.l.value :=
  theta.prime_is_prime

example : 5 ≤ theta.l.value :=
  theta.prime_ge_five

example : ∃ v, v ∈ theta.valuations.bad :=
  theta.badValuations_nonempty

example : Nat.Coprime (Module.finrank Fmod F) theta.l.value :=
  theta.degree_F_over_Fmod_prime_to_l

example :
    theta.fieldTower.sqrtMinusOne.element ^ 2 = (-1 : F) :=
  theta.sqrtMinusOne_square

example : theta.fmod_is_fieldOfModuli :=
  theta.fmodFieldOfModuli

example : theta.k_is_lTorsionKernelField :=
  theta.kIsLTorsionKernelField

example (j : F) :
    (PuncturedEllipticCurve.ofJ F j).jInvariant = j :=
  PuncturedEllipticCurve.jInvariant_ofJ F j

end AbstractConstructor

end InitialThetaDataExample

end Iut
