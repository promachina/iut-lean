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

section AbstractConstructor

universe u

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable [DecidableEq F]

/-- A constructor smoke test for the finite-place valuation section. -/
def abstractThetaValuationData
    (toModuli : NumberField.FinitePlace K -> NumberField.FinitePlace Fmod)
    (chosenLift : NumberField.FinitePlace Fmod -> NumberField.FinitePlace K)
    (hSection : ∀ w, toModuli (chosenLift w) = w)
    (residueCharacteristic : NumberField.FinitePlace Fmod -> ℕ)
    (badMod : Set (NumberField.FinitePlace Fmod))
    (hBad : ∃ w, w ∈ badMod)
    (hOdd : ∀ w, w ∈ badMod -> Odd (residueCharacteristic w))
    (hPrime : ∀ w, w ∈ badMod -> Nat.Prime (residueCharacteristic w))
    (hCoprime : ∀ w, w ∈ badMod ->
      Nat.Coprime (residueCharacteristic w) primeFive.value)
    (multiplicativeBadReductionAtLift : NumberField.FinitePlace K -> Prop)
    (hMult : ∀ v, v ∈ Set.range chosenLift -> toModuli v ∈ badMod ->
      multiplicativeBadReductionAtLift v) :
    ThetaValuationData primeFive Fmod K where
  toModuli := toModuli
  chosenLift := chosenLift
  toModuli_chosenLift := hSection
  residueCharacteristic := residueCharacteristic
  badMod := badMod
  badMod_nonempty := hBad
  badMod_oddResidueCharacteristic := hOdd
  badMod_residueCharacteristic_prime := hPrime
  badMod_residueCharacteristic_coprime_l := hCoprime
  multiplicativeBadReductionAtLift := multiplicativeBadReductionAtLift
  bad_lifts_have_multiplicative_reduction := hMult

/-- A constructor smoke test for the field tower part of initial theta data. -/
def abstractThetaFieldTower
    (sqrtMinusOne : SqrtMinusOneData F)
    (hDegree : Nat.Coprime (Module.finrank Fmod F) primeFive.value) :
    ThetaFieldTower primeFive Fmod F K where
  sqrtMinusOne := sqrtMinusOne
  degreePrimeToL_holds := hDegree

/-- A constructor smoke test for the curve/moduli part of initial theta data. -/
noncomputable def abstractThetaCurveModuliData
    (cF : HyperbolicOrbicurveModel F)
    (cF_is_quotient_by_neg_one fmod_is_fieldOfModuli
      stableReductionOverNonarchimedean torsion23RationalOverF : Prop)
    (hQuotient : cF_is_quotient_by_neg_one)
    (hFmod : fmod_is_fieldOfModuli)
    (hStable : stableReductionOverNonarchimedean)
    (hTorsion : torsion23RationalOverF) :
    ThetaCurveModuliData Fmod F where
  xF := PuncturedEllipticCurve.ofJ F (37 : F)
  cF := cF
  cF_is_quotient_by_neg_one := cF_is_quotient_by_neg_one
  cF_is_quotient_by_neg_one_holds := hQuotient
  fmod_is_fieldOfModuli := fmod_is_fieldOfModuli
  fmod_is_fieldOfModuli_holds := hFmod
  stableReductionOverNonarchimedean := stableReductionOverNonarchimedean
  stableReductionOverNonarchimedean_holds := hStable
  torsion23RationalOverF := torsion23RationalOverF
  torsion23RationalOverF_holds := hTorsion

/--
A constructor smoke test for full initial theta data under the exact field
hypotheses required by the record.
-/
noncomputable def abstractInitialThetaData
    (fieldTower : ThetaFieldTower primeFive Fmod F K)
    (curveModuli : ThetaCurveModuliData Fmod F)
    (valuations : ThetaValuationData primeFive Fmod K)
    (cK : HyperbolicOrbicurveModel K)
    (epsilon : CuspData cK)
    (k_is_lTorsionKernelField lTorsionImageContainsSL2 qParameterOrdersPrimeToL : Prop)
    (hK : k_is_lTorsionKernelField)
    (hImage : lTorsionImageContainsSL2)
    (hQ : qParameterOrdersPrimeToL) :
    InitialThetaData Fmod F K where
  l := primeFive
  fieldTower := fieldTower
  curveModuli := curveModuli
  cK := cK
  k_is_lTorsionKernelField := k_is_lTorsionKernelField
  k_is_lTorsionKernelField_holds := hK
  valuations := valuations
  epsilon := epsilon
  lTorsionImageContainsSL2 := lTorsionImageContainsSL2
  lTorsionImageContainsSL2_holds := hImage
  qParameterOrdersPrimeToL := qParameterOrdersPrimeToL
  qParameterOrdersPrimeToL_holds := hQ

variable (theta : InitialThetaData Fmod F K)

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

example : theta.curveModuli.cF_is_quotient_by_neg_one :=
  theta.quotientByNegOne

example : theta.curveModuli.fmod_is_fieldOfModuli :=
  theta.fmodFieldOfModuli

example : theta.curveModuli.stableReductionOverNonarchimedean :=
  theta.stableReductionOverNonarchimedean

example : theta.curveModuli.torsion23RationalOverF :=
  theta.torsion23RationalOverF

example : theta.k_is_lTorsionKernelField :=
  theta.kIsLTorsionKernelField

example (j : F) :
    (PuncturedEllipticCurve.ofJ F j).jInvariant = j :=
  PuncturedEllipticCurve.jInvariant_ofJ F j

end AbstractConstructor

end InitialThetaDataExample

end Iut
