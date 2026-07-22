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
horizontal poly-isomorphisms from the theta link.  They do prevent one
unindexed arrow-category square, unrelated to the lattice, from standing in
for all of clauses (a)--(d).
-/

open CategoryTheory

namespace Iut

universe u v

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

/-- A fixed-corner commutative square all four of whose sides are isomorphisms. -/
structure SourceIndexedHorizontalIsoSquare
    (C : Type u) [Category.{v} C]
    (upperLeft upperRight lowerLeft lowerRight : C) where
  upperHorizontal : upperLeft ≅ upperRight
  lowerHorizontal : lowerLeft ≅ lowerRight
  leftKummer : upperLeft ≅ lowerLeft
  rightKummer : upperRight ≅ lowerRight
  commutes :
    leftKummer.hom ≫ lowerHorizontal.hom =
      upperHorizontal.hom ≫ rightKummer.hom

namespace SourceIndexedHorizontalIsoSquare

variable
    {C : Type u} [Category.{v} C]
    {upperLeft upperRight lowerLeft lowerRight : C}

/-- Forget only that the two horizontal arrows are isomorphisms. -/
def toKummerSquare
    (square :
      SourceIndexedHorizontalIsoSquare C
        upperLeft upperRight lowerLeft lowerRight) :
    SourceIndexedHorizontalKummerSquare C
      upperLeft upperRight lowerLeft lowerRight where
  upperHorizontal := square.upperHorizontal.hom
  lowerHorizontal := square.lowerHorizontal.hom
  leftKummer := square.leftKummer
  rightKummer := square.rightKummer
  commutes := square.commutes

end SourceIndexedHorizontalIsoSquare

/--
The exact clause (iii)(a) square at `(n,m)`: the upper row consists of the
two site theaters and the lower row of the two vertically coric theaters.
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
  SourceIndexedHorizontalIsoSquare
    (SourceFPrimeStrip models)
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
  siteComparison :
    ∀ n m, (lattice.theater n m).associatedF ≅ site n m
  commonComparison :
    ∀ n, (lattice.commonBridge n).theater.associatedF ≅ common n

/-- The fixed-corner environment-prime-strip square of clause (iii)(b). -/
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
  SourceIndexedHorizontalIsoSquare
    (SourceFPrimeStrip models)
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
    (family.siteComparison n m).symm ≪≫
      triangle.upperHorizontal ≪≫
        family.siteComparison (n + 1) m
  lowerHorizontal :=
    (family.commonComparison n).symm ≪≫
      triangle.lowerHorizontal ≪≫
        family.commonComparison (n + 1)
  leftKummer :=
    (family.siteComparison n m).symm ≪≫
      triangle.leftKummer ≪≫ family.commonComparison n
  rightKummer :=
    (family.siteComparison (n + 1) m).symm ≪≫
      triangle.rightKummer ≪≫ family.commonComparison (n + 1)
  commutes := by
    simp [triangle.commutes]

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
