import Iut.Foundations.SourceThetaEvaluation

open CategoryTheory

namespace Iut

universe u

namespace SourceSplitKummerMonoid

variable {M : Type u} [CommMonoid M]

/--
Multiplication of the full unit group with a proposed characteristic factor.
-/
def unitCharacteristicMultiplication (S : Submonoid M) :
    Mˣ × S → M :=
  fun pair => (pair.1 : M) * pair.2.1

/--
A characteristic factor has no nontrivial units when unit-characteristic
multiplication is injective.
-/
theorem characteristic_eq_one_of_isUnit
    (S : Submonoid M)
    (hinjective : Function.Injective (unitCharacteristicMultiplication S))
    (value : S) (hvalue : IsUnit (value.1 : M)) :
    value = 1 := by
  let unit : Mˣ := hvalue.unit
  have hunit : (unit : M) = value.1 := hvalue.unit_spec
  have heq :
      unitCharacteristicMultiplication S (unit, 1) =
        unitCharacteristicMultiplication S (1, value) := by
    change (unit : M) * 1 = 1 * value.1
    simp [hunit]
  exact (congrArg Prod.snd (hinjective heq)).symm

/-- A subgroup of ambient units, embedded as units of any submonoid containing it. -/
noncomputable def subgroupUnits
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) : H →* Sˣ where
  toFun unit :=
    { val := ⟨(unit.1 : M),
        hH (H.mem_ofUnits unit.2 rfl)⟩
      inv := ⟨((unit.1⁻¹ : Mˣ) : M),
        hH (H.mem_ofUnits (H.inv_mem unit.2) rfl)⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  map_one' := by ext; rfl
  map_mul' first second := by ext; rfl

/-- The exact congruence identifying multiplication by a selected unit subgroup. -/
noncomputable def unitCongruence
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) : Con S where
  r first second :=
    ∃ unit : H,
      first = (subgroupUnits S H hH unit : S) * second
  iseqv := by
    constructor
    · intro value
      exact ⟨1, by simp⟩
    · intro first second h
      rcases h with ⟨unit, rfl⟩
      refine ⟨unit⁻¹, ?_⟩
      simp
    · intro first second third hfirst hsecond
      rcases hfirst with ⟨firstUnit, rfl⟩
      rcases hsecond with ⟨secondUnit, rfl⟩
      refine ⟨firstUnit * secondUnit, ?_⟩
      simp [mul_assoc]
  mul' := by
    intro first second third fourth hfirst hsecond
    rcases hfirst with ⟨firstUnit, rfl⟩
    rcases hsecond with ⟨secondUnit, rfl⟩
    refine ⟨firstUnit * secondUnit, ?_⟩
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- A commutative monoid modulo a specified subgroup of its ambient units. -/
abbrev UnitQuotient
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) :=
  (unitCongruence S H hH).Quotient

theorem unitQuotient_mk_eq_iff
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) (first second : S) :
    (first : UnitQuotient S H hH) = second ↔
      ∃ unit : H,
        first = (subgroupUnits S H hH unit : S) * second := by
  exact (unitCongruence S H hH).eq

theorem unitQuotient_mk_subgroupUnit_eq_one
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) (unit : H) :
    ((subgroupUnits S H hH unit : S) :
      UnitQuotient S H hH) = 1 := by
  apply (unitCongruence S H hH).eq.mpr
  exact ⟨unit, by simp⟩

variable [IsCancelMul M]

/-- Quotienting `H · S` by `H` leaves no units when `S` is characteristic. -/
theorem unitQuotient_isUnit_eq_one
    (characteristic : Submonoid M)
    (H : Subgroup Mˣ)
    (hinjective :
      Function.Injective
        (unitCharacteristicMultiplication characteristic))
    (value : UnitQuotient
      (H.ofUnits ⊔ characteristic) H le_sup_left)
    (hvalue : IsUnit value) :
    value = 1 := by
  let generated := H.ofUnits ⊔ characteristic
  let inclusion : H.ofUnits ≤ generated := le_sup_left
  induction value using Con.induction_on with
  | _ representative =>
    let inverseValue : UnitQuotient generated H inclusion :=
      (hvalue.unit⁻¹ : (UnitQuotient generated H inclusion)ˣ)
    obtain ⟨inverseRepresentative, hinverseRepresentative⟩ :=
      (unitCongruence generated H inclusion).mk'_surjective inverseValue
    have hproduct :
        ((representative * inverseRepresentative : generated) :
            UnitQuotient generated H inclusion) = 1 := by
      change
        (representative : UnitQuotient generated H inclusion) *
            (inverseRepresentative : UnitQuotient generated H inclusion) = 1
      have hinverse :
          (inverseRepresentative : UnitQuotient generated H inclusion) =
            inverseValue := hinverseRepresentative
      rw [hinverse]
      rw [← hvalue.unit_spec]
      simp [inverseValue]
    have hproductRelation :=
      (unitCongruence generated H inclusion).eq.mp hproduct
    rcases hproductRelation with ⟨productUnit, hproduct⟩
    rcases (Submonoid.mem_sup.mp representative.2) with
      ⟨firstUnitValue, hfirstUnitValue,
        firstCharacteristic, hfirstCharacteristic, hfirst⟩
    rcases (Submonoid.mem_sup.mp inverseRepresentative.2) with
      ⟨secondUnitValue, hsecondUnitValue,
        secondCharacteristic, hsecondCharacteristic, hsecond⟩
    let firstUnit : H :=
      ⟨H.unit_of_mem_ofUnits hfirstUnitValue,
        H.unit_of_mem_ofUnits_spec_mem⟩
    let secondUnit : H :=
      ⟨H.unit_of_mem_ofUnits hsecondUnitValue,
        H.unit_of_mem_ofUnits_spec_mem⟩
    have hcharacteristicProductIsUnit :
        IsUnit (firstCharacteristic * secondCharacteristic : M) := by
      let resultingUnit : Mˣ :=
        (firstUnit.1 * secondUnit.1)⁻¹ * productUnit.1
      refine ⟨resultingUnit, ?_⟩
      change
        (resultingUnit : M) =
          firstCharacteristic * secondCharacteristic
      apply mul_left_cancel
        (a := ((firstUnit.1 * secondUnit.1 : Mˣ) : M))
      change
        ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (resultingUnit : M) =
          ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (firstCharacteristic * secondCharacteristic)
      rw [show
        ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (resultingUnit : M) = (productUnit.1 : M) by
          rw [← Units.val_mul]
          apply congrArg Units.val
          change
            (firstUnit.1 * secondUnit.1) *
                ((firstUnit.1 * secondUnit.1)⁻¹ * productUnit.1) =
              productUnit.1
          simp [mul_assoc]]
      have hproductVal :
          representative.1 * inverseRepresentative.1 =
            (productUnit.1 : M) := by
        simpa using congrArg Subtype.val hproduct
      rw [← hproductVal, ← hfirst, ← hsecond]
      change
        (firstUnit.1 : M) * firstCharacteristic *
              ((secondUnit.1 : M) * secondCharacteristic) =
          ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (firstCharacteristic * secondCharacteristic)
      simp only [Units.val_mul]
      ac_rfl
    have hfirstCharacteristicIsUnit :
        IsUnit (firstCharacteristic : M) :=
      (IsUnit.mul_iff.mp hcharacteristicProductIsUnit).1
    have hfirstCharacteristicEq :
        (⟨firstCharacteristic, hfirstCharacteristic⟩ : characteristic) = 1 :=
      characteristic_eq_one_of_isUnit characteristic hinjective
        ⟨firstCharacteristic, hfirstCharacteristic⟩
        hfirstCharacteristicIsUnit
    apply (unitCongruence generated H inclusion).eq.mpr
    refine ⟨firstUnit, ?_⟩
    apply Subtype.ext
    change representative.1 = (firstUnit.1 : M) * 1
    rw [← hfirst]
    have : firstCharacteristic = 1 := congrArg Subtype.val hfirstCharacteristicEq
    rw [this, mul_one, mul_one]
    exact
      (H.unit_of_mem_ofUnits_spec_val_eq_of_mem
        hfirstUnitValue).symm

/-- If the first factor has only the identity unit, the units of a product are the second group. -/
noncomputable def productUnitsEquivSecond
    (Q U : Type u) [CommMonoid Q] [CommGroup U]
    (hQ : ∀ value : Q, IsUnit value → value = 1) :
    (Q × U)ˣ ≃* U where
  toFun unit := (MulEquiv.prodUnits unit).2
  invFun value := MulEquiv.prodUnits.symm (1, toUnits value)
  left_inv unit := by
    apply MulEquiv.prodUnits.injective
    apply Prod.ext
    · apply Units.ext
      exact (hQ _ (MulEquiv.prodUnits unit).1.isUnit).symm
    · simp
  right_inv value := by
    simp
  map_mul' first second := by
    simp

end SourceSplitKummerMonoid

namespace SourceMLFGaloisTMPair

variable {G : TopologicalGroupCat.{u}}

/-- The positive integer `2 * ell` used at a bad finite place. -/
def twoEll (l : PrimeGeFive) : ℕ+ :=
  ⟨2 * l.value, Nat.mul_pos (by decide) l.prime.pos⟩

/-- The literal group `mu_(2 ell)(A)`. -/
abbrev TwoEllRootsOfUnity
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive) :=
  pair.arithmeticMonoid.RootsOfUnityGroup (twoEll l)

/-- `O^perp(A)`: generated by `mu_(2 ell)(A)` and the splitting image. -/
abbrev badPerpMonoid
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l)).ofUnits ⊔
    characteristic

/-- `O^square(A) = O^perp(A) / mu_(2 ell)(A)` at a bad finite place. -/
abbrev badCharacteristicQuotient
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  SourceSplitKummerMonoid.UnitQuotient
    (badPerpMonoid pair l characteristic)
    (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
    le_sup_left

/-- The direct product monoid `O^(square times-mu)(A)` at a bad finite place. -/
abbrev badTimesMuMonoid
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  badCharacteristicQuotient pair l characteristic ×
    pair.UnitModuloTorsion

/-- The direct product monoid `O^(square times-mu)(A)` at a good finite place. -/
abbrev goodTimesMuMonoid
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  characteristic × pair.UnitModuloTorsion

/-- At a bad place, the complete unit group of `O^(square times-mu)` is `O^(times-mu)`. -/
noncomputable def badTimesMuUnitsEquiv
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic)) :
    (pair.badTimesMuMonoid l characteristic)ˣ ≃*
      pair.UnitModuloTorsion :=
  SourceSplitKummerMonoid.productUnitsEquivSecond _ _ fun value hvalue =>
    SourceSplitKummerMonoid.unitQuotient_isUnit_eq_one characteristic
      (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
      hinjective value hvalue

/-- At a good place, the complete unit group of `O^(square times-mu)` is `O^(times-mu)`. -/
noncomputable def goodTimesMuUnitsEquiv
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic)) :
    (pair.goodTimesMuMonoid characteristic)ˣ ≃*
      pair.UnitModuloTorsion :=
  SourceSplitKummerMonoid.productUnitsEquivSecond _ _ fun value hvalue => by
    exact SourceSplitKummerMonoid.characteristic_eq_one_of_isUnit
      characteristic hinjective value
      (hvalue.map characteristic.subtype)

end SourceMLFGaloisTMPair

end Iut
