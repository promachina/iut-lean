/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTimesMuPrimeStrip

/-!
# Isomorphisms of the `F^times-mu` prime strips

IUT II, Definition 4.9(vii), defines a morphism of prime strips to be a
place-indexed collection of isomorphisms of the complete constituent data.
This file starts with the finite-place constituent.  In particular, the maps
below preserve the Galois action, every open-subgroup invariant Kummer image,
the characteristic factor, and the model-Frobenioid reconstruction.  A bare
equivalence of the carrier categories is not sufficient.
-/

open CategoryTheory

namespace Iut

universe u

/-! ## Equivalences of MLF-Galois `TM` pairs -/

/-- Transport an open subgroup forward through a topological group isomorphism. -/
def sourceTimesMuPushOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup G) :
    OpenSubgroup H :=
  OpenSubgroup.comap equivalence.symm.toMonoidHom
    equivalence.symm.continuous_toFun subgroup

/-- Transport an open subgroup backward through a topological group isomorphism. -/
def sourceTimesMuPullOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup H) :
    OpenSubgroup G :=
  OpenSubgroup.comap equivalence.toMonoidHom
    equivalence.continuous_toFun subgroup

@[simp]
theorem sourceTimesMuPushOpenSubgroup_refl
    {G : TopologicalGroupCat.{u}} (subgroup : OpenSubgroup G) :
    sourceTimesMuPushOpenSubgroup (ContinuousMulEquiv.refl G) subgroup =
      subgroup := by
  apply OpenSubgroup.ext
  intro value
  rfl

theorem sourceTimesMuPushOpenSubgroup_trans
    {G H L : TopologicalGroupCat.{u}}
    (first : G ≃ₜ* H) (second : H ≃ₜ* L)
    (subgroup : OpenSubgroup G) :
    sourceTimesMuPushOpenSubgroup (first.trans second) subgroup =
      sourceTimesMuPushOpenSubgroup second
        (sourceTimesMuPushOpenSubgroup first subgroup) := by
  apply OpenSubgroup.ext
  intro value
  rfl

theorem sourceTimesMuPullOpenSubgroup_trans
    {G H L : TopologicalGroupCat.{u}}
    (first : G ≃ₜ* H) (second : H ≃ₜ* L)
    (subgroup : OpenSubgroup L) :
    sourceTimesMuPullOpenSubgroup (first.trans second) subgroup =
      sourceTimesMuPullOpenSubgroup first
        (sourceTimesMuPullOpenSubgroup second subgroup) := by
  apply OpenSubgroup.ext
  intro value
  rfl

@[simp]
theorem sourceTimesMuPush_pullOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup H) :
    sourceTimesMuPushOpenSubgroup equivalence
        (sourceTimesMuPullOpenSubgroup equivalence subgroup) = subgroup := by
  apply OpenSubgroup.ext
  intro value
  change equivalence (equivalence.symm value) ∈ subgroup ↔ value ∈ subgroup
  rw [equivalence.apply_symm_apply]

@[simp]
theorem sourceTimesMuPull_pushOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup G) :
    sourceTimesMuPullOpenSubgroup equivalence
        (sourceTimesMuPushOpenSubgroup equivalence subgroup) = subgroup := by
  apply OpenSubgroup.ext
  intro value
  change equivalence.symm (equivalence value) ∈ subgroup ↔ value ∈ subgroup
  rw [equivalence.symm_apply_apply]

/--
An equivariant isomorphism of the complete MLF-Galois `TM` pair data.

Both directions of the invariant-image condition are retained.  This is what
allows an internal `times-mu` Kummer comparison to be transported through an
isomorphism without losing any of the open-subgroup data that defines `Ism`.
-/
structure SourceMLFGaloisTMPairEquivalence
    {G H : TopologicalGroupCat.{u}}
    (source : SourceMLFGaloisTMPair G)
    (target : SourceMLFGaloisTMPair H) where
  group : G ≃ₜ* H
  arithmeticMonoid :
    source.arithmeticMonoid.carrier ≃*
      target.arithmeticMonoid.carrier
  arithmeticMonoid_equivariant :
    ∀ g value,
      arithmeticMonoid (source.action g value) =
        target.action (group g) (arithmeticMonoid value)
  unitModuloTorsion :
    source.UnitModuloTorsion ≃* target.UnitModuloTorsion
  unitModuloTorsion_mk :
    ∀ unit : source.arithmeticMonoid.carrierˣ,
      unitModuloTorsion (QuotientGroup.mk unit) =
        QuotientGroup.mk
          (Units.mapEquiv arithmeticMonoid unit)
  unitModuloTorsion_equivariant :
    ∀ g value,
      unitModuloTorsion (source.unitModuloTorsionAction g value) =
        target.unitModuloTorsionAction (group g)
          (unitModuloTorsion value)
  invariantImage_forward :
    ∀ subgroup,
      unitModuloTorsion ''
          (source.invariantUnitImage subgroup :
            Set source.UnitModuloTorsion) =
        (target.invariantUnitImage
          (sourceTimesMuPushOpenSubgroup group subgroup) :
            Set target.UnitModuloTorsion)
  invariantImage_backward :
    ∀ subgroup,
      unitModuloTorsion.symm ''
          (target.invariantUnitImage subgroup :
            Set target.UnitModuloTorsion) =
        (source.invariantUnitImage
          (sourceTimesMuPullOpenSubgroup group subgroup) :
            Set source.UnitModuloTorsion)

namespace SourceMLFGaloisTMPairEquivalence

variable
    {G H L : TopologicalGroupCat.{u}}
    {source : SourceMLFGaloisTMPair G}
    {middle : SourceMLFGaloisTMPair H}
    {target : SourceMLFGaloisTMPair L}

/-- Identity equivalence of a complete MLF-Galois `TM` pair. -/
noncomputable def refl (source : SourceMLFGaloisTMPair G) :
    SourceMLFGaloisTMPairEquivalence source source where
  group := ContinuousMulEquiv.refl G
  arithmeticMonoid := MulEquiv.refl _
  arithmeticMonoid_equivariant _ _ := rfl
  unitModuloTorsion := MulEquiv.refl _
  unitModuloTorsion_mk _ := rfl
  unitModuloTorsion_equivariant _ _ := rfl
  invariantImage_forward subgroup := by
    rw [sourceTimesMuPushOpenSubgroup_refl]
    exact Set.image_id _
  invariantImage_backward subgroup := by
    change id ''
        (source.invariantUnitImage subgroup :
          Set source.UnitModuloTorsion) = _
    rw [Set.image_id]
    rfl

/-- Composition of equivariant MLF-Galois `TM`-pair equivalences. -/
noncomputable def trans
    (first : SourceMLFGaloisTMPairEquivalence source middle)
    (second : SourceMLFGaloisTMPairEquivalence middle target) :
    SourceMLFGaloisTMPairEquivalence source target where
  group := first.group.trans second.group
  arithmeticMonoid :=
    first.arithmeticMonoid.trans second.arithmeticMonoid
  arithmeticMonoid_equivariant g value := by
    change
      second.arithmeticMonoid
          (first.arithmeticMonoid (source.action g value)) =
        target.action (second.group (first.group g))
          (second.arithmeticMonoid
            (first.arithmeticMonoid value))
    rw [first.arithmeticMonoid_equivariant]
    exact second.arithmeticMonoid_equivariant (first.group g)
      (first.arithmeticMonoid value)
  unitModuloTorsion :=
    first.unitModuloTorsion.trans second.unitModuloTorsion
  unitModuloTorsion_mk unit := by
    change
      second.unitModuloTorsion
          (first.unitModuloTorsion (QuotientGroup.mk unit)) =
        QuotientGroup.mk
          (Units.mapEquiv
            (first.arithmeticMonoid.trans second.arithmeticMonoid) unit)
    rw [first.unitModuloTorsion_mk]
    rw [second.unitModuloTorsion_mk]
    rfl
  unitModuloTorsion_equivariant g value := by
    change
      second.unitModuloTorsion
          (first.unitModuloTorsion
            (source.unitModuloTorsionAction g value)) =
        target.unitModuloTorsionAction
          (second.group (first.group g))
          (second.unitModuloTorsion
            (first.unitModuloTorsion value))
    rw [first.unitModuloTorsion_equivariant]
    exact second.unitModuloTorsion_equivariant (first.group g)
      (first.unitModuloTorsion value)
  invariantImage_forward subgroup := by
    change
      (fun value => second.unitModuloTorsion
        (first.unitModuloTorsion value)) ''
          (source.invariantUnitImage subgroup :
            Set source.UnitModuloTorsion) = _
    rw [← Set.image_image]
    rw [first.invariantImage_forward]
    rw [second.invariantImage_forward]
    rw [sourceTimesMuPushOpenSubgroup_trans]
  invariantImage_backward subgroup := by
    change
      (fun value => first.unitModuloTorsion.symm
        (second.unitModuloTorsion.symm value)) ''
          (target.invariantUnitImage subgroup :
            Set target.UnitModuloTorsion) = _
    rw [← Set.image_image]
    rw [second.invariantImage_backward]
    rw [first.invariantImage_backward]
    rw [sourceTimesMuPullOpenSubgroup_trans]

/-- Equivariance of the inverse unit-quotient map. -/
theorem unitModuloTorsion_symm_equivariant
    (equivalence : SourceMLFGaloisTMPairEquivalence source middle)
    (g : H) (value : middle.UnitModuloTorsion) :
    equivalence.unitModuloTorsion.symm
        (middle.unitModuloTorsionAction g value) =
      source.unitModuloTorsionAction (equivalence.group.symm g)
        (equivalence.unitModuloTorsion.symm value) := by
  apply equivalence.unitModuloTorsion.injective
  rw [equivalence.unitModuloTorsion.apply_symm_apply]
  rw [equivalence.unitModuloTorsion_equivariant]
  rw [equivalence.group.apply_symm_apply]
  rw [equivalence.unitModuloTorsion.apply_symm_apply]

end SourceMLFGaloisTMPairEquivalence

namespace SourceMLFGaloisTMPair.TimesMuKummerIsomorphism

variable
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}

/--
Transport a complete `times-mu` Kummer comparison through equivariant
isomorphisms of its group-theoretic and covering pairs.
-/
noncomputable def transport
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (comparison : TimesMuKummerIsomorphism sourceGroup sourceCover) :
    TimesMuKummerIsomorphism targetGroup targetCover where
  equiv :=
    groupEquivalence.unitModuloTorsion.symm.trans
      (comparison.equiv.trans
        coverEquivalence.unitModuloTorsion)
  equivariant g value := by
    change
      coverEquivalence.unitModuloTorsion
          (comparison.equiv
            (groupEquivalence.unitModuloTorsion.symm
              (targetGroup.unitModuloTorsionAction g value))) =
        targetCover.unitModuloTorsionAction g
          (coverEquivalence.unitModuloTorsion
            (comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm value)))
    rw [groupEquivalence.unitModuloTorsion_symm_equivariant]
    rw [comparison.equivariant]
    rw [coverEquivalence.unitModuloTorsion_equivariant]
    rw [← sameGroup]
    rw [groupEquivalence.group.apply_symm_apply]
  invariantImage subgroup := by
    ext value
    constructor
    · rintro ⟨sourceValue, hsourceValue, rfl⟩
      have hgroupImage :
          groupEquivalence.unitModuloTorsion.symm sourceValue ∈
            groupEquivalence.unitModuloTorsion.symm ''
              (targetGroup.invariantUnitImage subgroup :
                Set targetGroup.UnitModuloTorsion) :=
        ⟨sourceValue, hsourceValue, rfl⟩
      rw [groupEquivalence.invariantImage_backward] at hgroupImage
      have hkummerImage :
          comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm sourceValue) ∈
            comparison.equiv ''
              (sourceGroup.invariantUnitImage
                (sourceTimesMuPullOpenSubgroup
                  groupEquivalence.group subgroup) :
                Set sourceGroup.UnitModuloTorsion) :=
        ⟨_, hgroupImage, rfl⟩
      rw [comparison.invariantImage] at hkummerImage
      have hcoverImage :
          coverEquivalence.unitModuloTorsion
              (comparison.equiv
                (groupEquivalence.unitModuloTorsion.symm sourceValue)) ∈
            coverEquivalence.unitModuloTorsion ''
              (sourceCover.invariantUnitImage
                (sourceTimesMuPullOpenSubgroup
                  groupEquivalence.group subgroup) :
                Set sourceCover.UnitModuloTorsion) :=
        ⟨_, hkummerImage, rfl⟩
      rw [coverEquivalence.invariantImage_forward] at hcoverImage
      rw [← sameGroup,
        sourceTimesMuPush_pullOpenSubgroup] at hcoverImage
      exact hcoverImage
    · intro hvalue
      have hcoverImage :
          value ∈ coverEquivalence.unitModuloTorsion ''
            (sourceCover.invariantUnitImage
              (sourceTimesMuPullOpenSubgroup
                groupEquivalence.group subgroup) :
              Set sourceCover.UnitModuloTorsion) := by
        rw [coverEquivalence.invariantImage_forward]
        rwa [← sameGroup,
          sourceTimesMuPush_pullOpenSubgroup]
      rcases hcoverImage with ⟨coverValue, hcoverValue, rfl⟩
      have hkummerImage :
          coverValue ∈ comparison.equiv ''
            (sourceGroup.invariantUnitImage
              (sourceTimesMuPullOpenSubgroup
                groupEquivalence.group subgroup) :
              Set sourceGroup.UnitModuloTorsion) := by
        rw [comparison.invariantImage]
        exact hcoverValue
      rcases hkummerImage with ⟨groupValue, hgroupValue, rfl⟩
      have hgroupImage :
          groupValue ∈ groupEquivalence.unitModuloTorsion.symm ''
            (targetGroup.invariantUnitImage subgroup :
              Set targetGroup.UnitModuloTorsion) := by
        rw [groupEquivalence.invariantImage_backward]
        exact hgroupValue
      rcases hgroupImage with ⟨targetValue, htargetValue, htargetValueEq⟩
      refine ⟨targetValue, htargetValue, ?_⟩
      change
        coverEquivalence.unitModuloTorsion
            (comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm targetValue)) =
          coverEquivalence.unitModuloTorsion
            (comparison.equiv groupValue)
      rw [htargetValueEq]

end SourceMLFGaloisTMPair.TimesMuKummerIsomorphism

/--
The `Ism`-orbit transported through two pair equivalences.  A representative
is selected only to define the quotient map; the theorem below proves that
the result is independent of this selection.
-/
noncomputable def sourceTimesMuTransportKummerOrbit
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (orbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        sourceGroup sourceCover) :
    SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
      targetGroup targetCover :=
  SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.orbitOf
    (SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.transport
      groupEquivalence coverEquivalence sameGroup
      (Classical.choose (Quotient.exists_rep orbit)))

/-- Every transported Kummer orbit is the unique target `Ism`-orbit. -/
theorem sourceTimesMuTransportKummerOrbit_eq
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (sourceOrbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        sourceGroup sourceCover)
    (targetOrbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        targetGroup targetCover) :
    sourceTimesMuTransportKummerOrbit groupEquivalence coverEquivalence
        sameGroup sourceOrbit = targetOrbit := by
  obtain ⟨targetRepresentative, rfl⟩ := Quotient.exists_rep targetOrbit
  exact
    SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.orbitOf_eq
      (SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.transport
        groupEquivalence coverEquivalence sameGroup
        (Classical.choose (Quotient.exists_rep sourceOrbit)))
      targetRepresentative

namespace SourceFiniteTimesMuKummerInput

/-- The characteristic generator embedded in the reconstructed product monoid. -/
noncomputable def characteristicGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.characteristic →* input.timesMuMonoid := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      let intoPerp :
          characteristic →*
            coverPair.badPerpMonoid ell characteristic :=
        characteristic.subtype.codRestrict
          (coverPair.badPerpMonoid ell characteristic)
          (fun value =>
            (show characteristic ≤
                coverPair.badPerpMonoid ell characteristic from
              le_sup_right) value.property)
      let intoQuotient :
          characteristic →*
            coverPair.badCharacteristicQuotient ell characteristic :=
        (SourceSplitKummerMonoid.unitCongruence
          (coverPair.badPerpMonoid ell characteristic)
          (coverPair.arithmeticMonoid.rootsOfUnitySubgroup
            (SourceMLFGaloisTMPair.twoEll ell))
          le_sup_left).mk'.comp intoPerp
      exact
        (MonoidHom.inl
          (coverPair.badCharacteristicQuotient ell characteristic)
          coverPair.UnitModuloTorsion).comp intoQuotient
  | good =>
      exact MonoidHom.inl characteristic coverPair.UnitModuloTorsion

/-- The unit-mod-torsion factor embedded in the reconstructed product monoid. -/
noncomputable def unitGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.coverPair.UnitModuloTorsion →* input.timesMuMonoid := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      exact MonoidHom.inr
        (coverPair.badCharacteristicQuotient ell characteristic)
        coverPair.UnitModuloTorsion
  | good =>
      exact MonoidHom.inr characteristic coverPair.UnitModuloTorsion

/-- Projection from the reconstructed product to its unit-mod-torsion factor. -/
noncomputable def unitProjection
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.timesMuMonoid →* input.coverPair.UnitModuloTorsion := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      exact MonoidHom.snd
        (coverPair.badCharacteristicQuotient ell characteristic)
        coverPair.UnitModuloTorsion
  | good =>
      exact MonoidHom.snd characteristic coverPair.UnitModuloTorsion

@[simp]
theorem unitProjection_unitGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying)
    (value : input.coverPair.UnitModuloTorsion) :
    input.unitProjection (input.unitGenerator value) = value := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind <;> rfl

@[simp]
theorem unitProjection_characteristicGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying)
    (value : input.characteristic) :
    input.unitProjection (input.characteristicGenerator value) = 1 := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind <;> rfl

end SourceFiniteTimesMuKummerInput

/-! ## Finite split-Kummer Frobenioid isomorphisms -/

/--
An isomorphism of the complete finite-place object constructed in IUT II,
Definition 4.9(iii)--(iv).

The two generator equations and the unit-projection equation identify the
map on the literal product `O^square x O^(times-mu)`.  The remaining fields
say that the reconstructed split Frobenioid, its base, reference object, and
rational-function monoid carry exactly that map.
-/
structure SourceFiniteTimesMuKummerFrobenioidEquivalence
    {ell : PrimeGeFive}
    {sourceUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    (source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying)
    (target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying) where
  kind_compatible : source.input.kind = target.input.kind
  groupPair :
    SourceMLFGaloisTMPairEquivalence
      source.input.groupPair target.input.groupPair
  coverPair :
    SourceMLFGaloisTMPairEquivalence
      source.input.coverPair target.input.coverPair
  galoisGroup_compatible : groupPair.group = coverPair.group
  characteristic_compatible :
    ∀ value,
      value ∈ source.input.characteristic ↔
        coverPair.arithmeticMonoid value ∈
          target.input.characteristic
  timesMuMonoid :
    source.input.timesMuMonoid ≃* target.input.timesMuMonoid
  timesMu_characteristicGenerator :
    ∀ value : source.input.characteristic,
      timesMuMonoid (source.input.characteristicGenerator value) =
        target.input.characteristicGenerator
          ⟨coverPair.arithmeticMonoid value.1,
            (characteristic_compatible value.1).mp value.2⟩
  timesMu_unitGenerator :
    ∀ value : source.input.coverPair.UnitModuloTorsion,
      timesMuMonoid (source.input.unitGenerator value) =
        target.input.unitGenerator
          (coverPair.unitModuloTorsion value)
  timesMu_unitProjection :
    ∀ value : source.input.timesMuMonoid,
      target.input.unitProjection (timesMuMonoid value) =
        coverPair.unitModuloTorsion
          (source.input.unitProjection value)
  reconstructed :
    SplitFrobenioidEquivalence
      source.reconstructed target.reconstructed
  base :
    CategoryTheory.Equivalence
      source.reconstructed.frobenioid.baseCategory
      target.reconstructed.frobenioid.baseCategory
  base_compatible :
    source.reconstructed.frobenioid.preFrobenioid.base ⋙ base.functor =
      reconstructed.carrier.functor ⋙
        target.reconstructed.frobenioid.preFrobenioid.base
  referenceIso :
    reconstructed.carrier.functor.obj source.referenceObject ≅
      target.referenceObject
  referenceRationalMonoid :
    source.reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        source.referenceObject ≃*
      target.reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        target.referenceObject
  referenceRationalMonoid_hom :
    ∀ value,
      (referenceRationalMonoid value).hom =
        referenceIso.inv ≫
          reconstructed.carrier.functor.map value.hom ≫
            referenceIso.hom
  rationalTimesMu_compatible :
    ∀ value,
      target.rationalMonoidIso (referenceRationalMonoid value) =
        timesMuMonoid (source.rationalMonoidIso value)

namespace SourceFiniteTimesMuKummerFrobenioidEquivalence

variable
    {ell : PrimeGeFive}
    {sourceUnderlying middleUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    {source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying}
    {middle :
      SourceFiniteTimesMuKummerFrobenioid ell middleUnderlying}
    {target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying}

/-- Identity isomorphism of a finite split-Kummer Frobenioid. -/
noncomputable def refl
    (source : SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying) :
    SourceFiniteTimesMuKummerFrobenioidEquivalence source source where
  kind_compatible := rfl
  groupPair := SourceMLFGaloisTMPairEquivalence.refl _
  coverPair := SourceMLFGaloisTMPairEquivalence.refl _
  galoisGroup_compatible := rfl
  characteristic_compatible _ := Iff.rfl
  timesMuMonoid := MulEquiv.refl _
  timesMu_characteristicGenerator _ := rfl
  timesMu_unitGenerator _ := rfl
  timesMu_unitProjection _ := rfl
  reconstructed := SplitFrobenioidEquivalence.refl _
  base := CategoryTheory.Equivalence.refl
  base_compatible :=
    (Functor.comp_id
      source.reconstructed.frobenioid.preFrobenioid.base).trans
      (Functor.id_comp
        source.reconstructed.frobenioid.preFrobenioid.base).symm
  referenceIso := Iso.refl source.referenceObject
  referenceRationalMonoid := MulEquiv.refl _
  referenceRationalMonoid_hom value := by
    change value.hom =
      𝟙 source.referenceObject ≫ value.hom ≫ 𝟙 source.referenceObject
    rw [Category.id_comp]
    exact (Category.comp_id value.hom).symm
  rationalTimesMu_compatible _ := rfl

/-- Composition of complete finite split-Kummer Frobenioid isomorphisms. -/
noncomputable def trans
    (first :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source middle)
    (second :
      SourceFiniteTimesMuKummerFrobenioidEquivalence middle target) :
    SourceFiniteTimesMuKummerFrobenioidEquivalence source target where
  kind_compatible := first.kind_compatible.trans second.kind_compatible
  groupPair := first.groupPair.trans second.groupPair
  coverPair := first.coverPair.trans second.coverPair
  galoisGroup_compatible := by
    change
      first.groupPair.group.trans second.groupPair.group =
        first.coverPair.group.trans second.coverPair.group
    rw [first.galoisGroup_compatible,
      second.galoisGroup_compatible]
  characteristic_compatible value := by
    rw [first.characteristic_compatible]
    exact second.characteristic_compatible
      (first.coverPair.arithmeticMonoid value)
  timesMuMonoid := first.timesMuMonoid.trans second.timesMuMonoid
  timesMu_characteristicGenerator value := by
    change
      second.timesMuMonoid
          (first.timesMuMonoid
            (source.input.characteristicGenerator value)) = _
    rw [first.timesMu_characteristicGenerator]
    rw [second.timesMu_characteristicGenerator]
    rfl
  timesMu_unitGenerator value := by
    change
      second.timesMuMonoid
          (first.timesMuMonoid
            (source.input.unitGenerator value)) = _
    rw [first.timesMu_unitGenerator]
    rw [second.timesMu_unitGenerator]
    rfl
  timesMu_unitProjection value := by
    change
      target.input.unitProjection
          (second.timesMuMonoid (first.timesMuMonoid value)) = _
    rw [second.timesMu_unitProjection]
    rw [first.timesMu_unitProjection]
    rfl
  reconstructed := first.reconstructed.trans second.reconstructed
  base := first.base.trans second.base
  base_compatible := by
    change
      source.reconstructed.frobenioid.preFrobenioid.base ⋙
          (first.base.functor ⋙ second.base.functor) =
        (first.reconstructed.carrier.functor ⋙
            second.reconstructed.carrier.functor) ⋙
          target.reconstructed.frobenioid.preFrobenioid.base
    rw [← Functor.assoc]
    rw [first.base_compatible]
    rw [Functor.assoc]
    rw [second.base_compatible]
    rw [← Functor.assoc]
  referenceIso :=
    second.reconstructed.carrier.functor.mapIso first.referenceIso ≪≫
      second.referenceIso
  referenceRationalMonoid :=
    first.referenceRationalMonoid.trans
      second.referenceRationalMonoid
  referenceRationalMonoid_hom value := by
    change
      (second.referenceRationalMonoid
        (first.referenceRationalMonoid value)).hom =
        (second.reconstructed.carrier.functor.mapIso
              first.referenceIso ≪≫
            second.referenceIso).inv ≫
          second.reconstructed.carrier.functor.map
              (first.reconstructed.carrier.functor.map value.hom) ≫
            (second.reconstructed.carrier.functor.mapIso
                first.referenceIso ≪≫
              second.referenceIso).hom
    rw [second.referenceRationalMonoid_hom]
    rw [first.referenceRationalMonoid_hom]
    simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  rationalTimesMu_compatible value := by
    change
      target.rationalMonoidIso
          (second.referenceRationalMonoid
            (first.referenceRationalMonoid value)) =
        second.timesMuMonoid
          (first.timesMuMonoid
            (source.rationalMonoidIso value))
    rw [second.rationalTimesMu_compatible]
    rw [first.rationalTimesMu_compatible]

/-- The finite isomorphism carries the literal source Kummer orbit to the target orbit. -/
theorem kummerStructure_compatible
    (equivalence :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) :
    sourceTimesMuTransportKummerOrbit
        equivalence.groupPair equivalence.coverPair
        equivalence.galoisGroup_compatible
        source.input.kummerStructure =
      target.input.kummerStructure :=
  sourceTimesMuTransportKummerOrbit_eq
    equivalence.groupPair equivalence.coverPair
    equivalence.galoisGroup_compatible
    source.input.kummerStructure target.input.kummerStructure

end SourceFiniteTimesMuKummerFrobenioidEquivalence

end Iut
