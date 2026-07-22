/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTheorem311

/-!
# Indexed horizontal compatibility for IUT III, Theorem 3.11(iii)

The four clauses of Theorem 3.11(iii) compare adjacent horizontal columns at
every relevant vertical site, bad place, and absolute label.  This module
records those indices and fixes every corner of the resulting squares to an
actual lattice, prime-strip, projective-system, or labeled-data object.

The structures here are source obligations: they do not construct the
horizontal poly-isomorphisms from the theta link.  In particular, the
prime-strip square below is still formulated for the ordinary `F`-prime-strip
associated to a theater.  The source theorem uses the Definition 4.9
`F^(turnstile times-mu)`-prime-strip, so this square is preparatory scaffolding
until it is retargeted through the actual `times-mu` construction.  The indexed
corners nevertheless prevent one unrelated arrow-category square from
standing in for all of clauses (a)--(d).
-/

open CategoryTheory

namespace Iut

universe u v

local infixr:81 " ≫ₚ " =>
  SourceFPrimeStripFullPolyIsomorphism.comp

/--
A commutative square with fixed corners and isomorphisms on its two vertical
sides.  Its rows are the horizontal arrows that are compared by Kummer.
-/
structure SourceIndexedHorizontalKummerSquare
    (C : Type u) [Category.{v} C]
    (upperLeft upperRight lowerLeft lowerRight : C) where
  upperHorizontal : upperLeft ⟶ upperRight
  lowerHorizontal : lowerLeft ⟶ lowerRight
  leftKummer : upperLeft ≅ lowerLeft
  rightKummer : upperRight ≅ lowerRight
  commutes :
    leftKummer.hom ≫ lowerHorizontal =
      upperHorizontal ≫ rightKummer.hom

namespace SourceIndexedHorizontalKummerSquare

variable
    {C : Type u} [Category.{v} C]
    {upperLeft upperRight lowerLeft lowerRight : C}

/-- The fixed-corner square as an isomorphism in the arrow category. -/
def toArrowCompatibility
    (square :
      SourceIndexedHorizontalKummerSquare C
        upperLeft upperRight lowerLeft lowerRight) :
    SourceHorizontalKummerCompatibility C where
  sourceHorizontal := Arrow.mk square.upperHorizontal
  targetHorizontal := Arrow.mk square.lowerHorizontal
  verticalKummer :=
    Arrow.isoMk square.leftKummer square.rightKummer square.commutes

/-- Arbitrary automorphisms of the upper row transport to the lower row. -/
def automorphismEquiv
    (square :
      SourceIndexedHorizontalKummerSquare C
        upperLeft upperRight lowerLeft lowerRight) :
    Aut square.toArrowCompatibility.sourceHorizontal ≃*
      Aut square.toArrowCompatibility.targetHorizontal :=
  square.toArrowCompatibility.automorphismEquiv

end SourceIndexedHorizontalKummerSquare

/--
A commutative square in the Section 0 coarsification of `F`-prime-strips.
Every side is an equivalence class of componentwise equivalence maps, not a
strict categorical `Iso` of the prime-strip records.  The chosen horizontal
classes witness nonemptiness; `upperToLower` and `lowerToUpper` express
compatibility of the entire full poly-isomorphisms, not just those witnesses.
-/
structure SourceFPrimeStripPolyIsomorphismSquare
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    (upperLeft upperRight lowerLeft lowerRight :
      SourceFPrimeStrip models) where
  upperHorizontal :
    SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight
  lowerHorizontal :
    SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight
  leftKummer :
    SourceFPrimeStripFullPolyIsomorphism upperLeft lowerLeft
  rightKummer :
    SourceFPrimeStripFullPolyIsomorphism upperRight lowerRight
  commutes :
    SourceFPrimeStripFullPolyIsomorphism.comp
        leftKummer lowerHorizontal =
      SourceFPrimeStripFullPolyIsomorphism.comp
        upperHorizontal rightKummer
  upperToLower :
    ∀ upper : SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight,
      ∃ lower : SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
        SourceFPrimeStripFullPolyIsomorphism.comp leftKummer lower =
          SourceFPrimeStripFullPolyIsomorphism.comp upper rightKummer
  lowerToUpper :
    ∀ lower : SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
      ∃ upper : SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight,
        SourceFPrimeStripFullPolyIsomorphism.comp leftKummer lower =
          SourceFPrimeStripFullPolyIsomorphism.comp upper rightKummer

/--
The ordinary-`F` precursor of clause (iii)(a) at `(n,m)`: the upper row
consists of the two site theaters and the lower row of the two vertically
coric theaters.  Its arrows obey the paper's Section 0 coarsification, but the
corners must still be replaced by their Definition 4.9
`F^(turnstile times-mu)` constructions before this is clause (iii)(a) itself.
-/
abbrev SourceTheorem311TrianglePrimeStripSquare
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models)
    (n m : ℤ) :=
  SourceFPrimeStripPolyIsomorphismSquare
    (lattice.theater n m).associatedF
    (lattice.theater (n + 1) m).associatedF
    (lattice.commonBridge n).theater.associatedF
    (lattice.commonBridge (n + 1)).theater.associatedF

/--
The environment prime strips of clause (iii)(b), together with their natural
comparison isomorphisms to the triangle prime strips at every lattice site.
-/
structure SourceTheorem311EnvironmentPrimeStripFamily
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models) where
  site : ℤ → ℤ → SourceFPrimeStrip models
  common : ℤ → SourceFPrimeStrip models
  siteToTriangle :
    ∀ n m, SourceFPrimeStripFullPolyIsomorphism
      (site n m) (lattice.theater n m).associatedF
  siteFromTriangle :
    ∀ n m, SourceFPrimeStripFullPolyIsomorphism
      (lattice.theater n m).associatedF (site n m)
  siteToFrom :
    ∀ n m,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (siteToTriangle n m) (siteFromTriangle n m) =
        SourceFPrimeStripFullPolyIsomorphism.id (site n m)
  siteFromTo :
    ∀ n m,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (siteFromTriangle n m) (siteToTriangle n m) =
        SourceFPrimeStripFullPolyIsomorphism.id
          (lattice.theater n m).associatedF
  commonToTriangle :
    ∀ n, SourceFPrimeStripFullPolyIsomorphism
      (common n) (lattice.commonBridge n).theater.associatedF
  commonFromTriangle :
    ∀ n, SourceFPrimeStripFullPolyIsomorphism
      (lattice.commonBridge n).theater.associatedF (common n)
  commonToFrom :
    ∀ n,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (commonToTriangle n) (commonFromTriangle n) =
        SourceFPrimeStripFullPolyIsomorphism.id (common n)
  commonFromTo :
    ∀ n,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (commonFromTriangle n) (commonToTriangle n) =
        SourceFPrimeStripFullPolyIsomorphism.id
          (lattice.commonBridge n).theater.associatedF

/-- The ordinary-`F` precursor of the fixed-corner square in clause (iii)(b). -/
abbrev SourceTheorem311EnvironmentPrimeStripSquare
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (family : SourceTheorem311EnvironmentPrimeStripFamily lattice)
    (n m : ℤ) :=
  SourceFPrimeStripPolyIsomorphismSquare
    (family.site n m) (family.site (n + 1) m)
    (family.common n) (family.common (n + 1))

namespace SourceTheorem311EnvironmentPrimeStripSquare

variable
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}

/--
Clause (iii)(b) is obtained from clause (iii)(a) by conjugating all four
sides with the natural environment-to-triangle comparison isomorphisms.
-/
def ofTriangle
    (family : SourceTheorem311EnvironmentPrimeStripFamily lattice)
    (n m : ℤ)
    (triangle : SourceTheorem311TrianglePrimeStripSquare lattice n m) :
    SourceTheorem311EnvironmentPrimeStripSquare family n m where
  upperHorizontal :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle n m) triangle.upperHorizontal)
      (family.siteFromTriangle (n + 1) m)
  lowerHorizontal :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.commonToTriangle n) triangle.lowerHorizontal)
      (family.commonFromTriangle (n + 1))
  leftKummer :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle n m) triangle.leftKummer)
      (family.commonFromTriangle n)
  rightKummer :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle (n + 1) m) triangle.rightKummer)
      (family.commonFromTriangle (n + 1))
  commutes := by
    have commonCancellation :
        family.commonFromTriangle n ≫ₚ
            (family.commonToTriangle n ≫ₚ
              (triangle.lowerHorizontal ≫ₚ
                family.commonFromTriangle (n + 1))) =
          triangle.lowerHorizontal ≫ₚ
            family.commonFromTriangle (n + 1) :=
      SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.commonFromTriangle n)
        (family.commonToTriangle n)
        (family.commonFromTo n)
        (triangle.lowerHorizontal ≫ₚ
          family.commonFromTriangle (n + 1))
    have siteCancellation :
        family.siteFromTriangle (n + 1) m ≫ₚ
            (family.siteToTriangle (n + 1) m ≫ₚ
              (triangle.rightKummer ≫ₚ
                family.commonFromTriangle (n + 1))) =
          triangle.rightKummer ≫ₚ
            family.commonFromTriangle (n + 1) :=
      SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.siteFromTriangle (n + 1) m)
        (family.siteToTriangle (n + 1) m)
        (family.siteFromTo (n + 1) m)
        (triangle.rightKummer ≫ₚ
          family.commonFromTriangle (n + 1))
    calc
      ((family.siteToTriangle n m ≫ₚ triangle.leftKummer) ≫ₚ
          family.commonFromTriangle n) ≫ₚ
          ((family.commonToTriangle n ≫ₚ
            triangle.lowerHorizontal) ≫ₚ
            family.commonFromTriangle (n + 1)) =
        family.siteToTriangle n m ≫ₚ
          (triangle.leftKummer ≫ₚ
            (family.commonFromTriangle n ≫ₚ
              (family.commonToTriangle n ≫ₚ
                (triangle.lowerHorizontal ≫ₚ
                  family.commonFromTriangle (n + 1))))) := by
            simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.leftKummer ≫ₚ
            (triangle.lowerHorizontal ≫ₚ
              family.commonFromTriangle (n + 1))) := by
            rw [commonCancellation]
      _ = family.siteToTriangle n m ≫ₚ
          ((triangle.leftKummer ≫ₚ triangle.lowerHorizontal) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            rw [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          ((triangle.upperHorizontal ≫ₚ triangle.rightKummer) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            rw [triangle.commutes]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.upperHorizontal ≫ₚ
            (triangle.rightKummer ≫ₚ
              family.commonFromTriangle (n + 1))) := by
            rw [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.upperHorizontal ≫ₚ
            (family.siteFromTriangle (n + 1) m ≫ₚ
              (family.siteToTriangle (n + 1) m ≫ₚ
                (triangle.rightKummer ≫ₚ
                  family.commonFromTriangle (n + 1))))) := by
            rw [siteCancellation]
      _ = ((family.siteToTriangle n m ≫ₚ
          triangle.upperHorizontal) ≫ₚ
          family.siteFromTriangle (n + 1) m) ≫ₚ
          ((family.siteToTriangle (n + 1) m ≫ₚ
            triangle.rightKummer) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
  upperToLower := by
    intro upper
    let triangleUpper :=
      (family.siteFromTriangle n m ≫ₚ upper) ≫ₚ
        family.siteToTriangle (n + 1) m
    rcases triangle.upperToLower triangleUpper with
      ⟨triangleLower, triangleCommutes⟩
    refine
      ⟨(family.commonToTriangle n ≫ₚ triangleLower) ≫ₚ
          family.commonFromTriangle (n + 1), ?_⟩
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.commonFromTriangle n)
      (family.commonToTriangle n)
      (family.commonFromTo n)]
    rw [← SourceFPrimeStripFullPolyIsomorphism.comp_assoc
      triangle.leftKummer triangleLower
      (family.commonFromTriangle (n + 1))]
    rw [triangleCommutes]
    dsimp [triangleUpper]
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteToTriangle n m)
      (family.siteFromTriangle n m)
      (family.siteToFrom n m)]
  lowerToUpper := by
    intro lower
    let triangleLower :=
      (family.commonFromTriangle n ≫ₚ lower) ≫ₚ
        family.commonToTriangle (n + 1)
    rcases triangle.lowerToUpper triangleLower with
      ⟨triangleUpper, triangleCommutes⟩
    refine
      ⟨(family.siteToTriangle n m ≫ₚ triangleUpper) ≫ₚ
          family.siteFromTriangle (n + 1) m, ?_⟩
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteFromTriangle (n + 1) m)
      (family.siteToTriangle (n + 1) m)
      (family.siteFromTo (n + 1) m)]
    have extended := congrArg
      (fun map => map ≫ₚ family.commonFromTriangle (n + 1))
      triangleCommutes
    dsimp [triangleLower] at extended
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc] at extended
    rw [family.commonToFrom (n + 1)] at extended
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_id] at extended
    rw [extended]

end SourceTheorem311EnvironmentPrimeStripSquare

/--
A fixed-corner square of actual mono-theta projective systems.  Each side is
an isomorphism carrying its levelwise environment realization.
-/
structure SourceIndexedMonoThetaProjectiveSystemSquare
    (upperLeft upperRight lowerLeft lowerRight :
      SourceMonoThetaProjectiveSystem.{u}) where
  upperHorizontal :
    SourceMonoThetaProjectiveSystemIso upperLeft upperRight
  lowerHorizontal :
    SourceMonoThetaProjectiveSystemIso lowerLeft lowerRight
  leftKummer :
    SourceMonoThetaProjectiveSystemIso upperLeft lowerLeft
  rightKummer :
    SourceMonoThetaProjectiveSystemIso upperRight lowerRight
  commutes :
    leftKummer.groupDiagramIso.hom ≫
        lowerHorizontal.groupDiagramIso.hom =
      upperHorizontal.groupDiagramIso.hom ≫
        rightKummer.groupDiagramIso.hom

namespace SourceIndexedMonoThetaProjectiveSystemSquare

variable
    {upperLeft upperRight lowerLeft lowerRight :
      SourceMonoThetaProjectiveSystem.{u}}

/-- The projective-system square as a fixed-corner arrow isomorphism. -/
def toKummerSquare
    (square :
      SourceIndexedMonoThetaProjectiveSystemSquare
        upperLeft upperRight lowerLeft lowerRight) :
    SourceIndexedHorizontalKummerSquare
      (MonoThetaModulus ⥤ TopologicalGroupCat.{u})
      upperLeft.groupDiagram upperRight.groupDiagram
      lowerLeft.groupDiagram lowerRight.groupDiagram where
  upperHorizontal := square.upperHorizontal.groupDiagramIso.hom
  lowerHorizontal := square.lowerHorizontal.groupDiagramIso.hom
  leftKummer := square.leftKummer.groupDiagramIso
  rightKummer := square.rightKummer.groupDiagramIso
  commutes := square.commutes

end SourceIndexedMonoThetaProjectiveSystemSquare

/--
The site and vertically coric projective systems used in clause (iii)(c),
indexed by both lattice coordinates and the actual selected bad place.
-/
structure SourceTheorem311MonoThetaProjectiveSystemFamily
    (badPlace : Type u) where
  site : ℤ → ℤ → badPlace → SourceMonoThetaProjectiveSystem.{u}
  common : ℤ → badPlace → SourceMonoThetaProjectiveSystem.{u}

/-- The indexed clause (iii)(c) square for one site and bad place. -/
abbrev SourceTheorem311MonoThetaProjectiveSystemSquare
    {badPlace : Type u}
    (family : SourceTheorem311MonoThetaProjectiveSystemFamily badPlace)
    (n m : ℤ) (place : badPlace) :=
  SourceIndexedMonoThetaProjectiveSystemSquare
    (family.site n m place) (family.site (n + 1) m place)
    (family.common n place) (family.common (n + 1) place)

/--
The clause (iii)(d) horizontal square for the actual `kappa`-solvable and
`M_infinity^kappa` objects at one absolute label.
-/
structure SourceTheorem311LabeledHorizontalKummerSquare
    {l : PrimeGeFive}
    (source target : SourceTheorem311LabeledData.{u} l)
    (label : IUTIIAbsoluteThetaLabel.{u} l) where
  kappaSolHorizontal : source.kappaSol label ≅ target.kappaSol label
  mInfinityHorizontal :
    source.mInfinityKappa label ≅ target.mInfinityKappa label
  kappaMInfinity_compatible :
    kappaSolHorizontal.hom ≫ target.kappaToMInfinity label =
      source.kappaToMInfinity label ≫ mInfinityHorizontal.hom

namespace SourceTheorem311LabeledHorizontalKummerSquare

variable
    {l : PrimeGeFive}
    {source target : SourceTheorem311LabeledData.{u} l}
    {label : IUTIIAbsoluteThetaLabel.{u} l}

/-- The labeled compatibility as a square with its four exact profinite corners. -/
def toKummerSquare
    (square :
      SourceTheorem311LabeledHorizontalKummerSquare source target label) :
    SourceIndexedHorizontalKummerSquare ProfiniteGrp
      (source.kappaSol label) (source.mInfinityKappa label)
      (target.kappaSol label) (target.mInfinityKappa label) where
  upperHorizontal := source.kappaToMInfinity label
  lowerHorizontal := target.kappaToMInfinity label
  leftKummer := square.kappaSolHorizontal
  rightKummer := square.mInfinityHorizontal
  commutes := square.kappaMInfinity_compatible

end SourceTheorem311LabeledHorizontalKummerSquare

end Iut
