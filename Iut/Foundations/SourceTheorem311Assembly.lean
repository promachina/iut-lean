/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceVerticalLogLink
import Iut.Foundations.SourceTheorem311Horizontal

/-!
# Source assembly for IUT III, Theorem 3.11

This module assembles the source-faithful constructions of
`SourceTheorem311` at one fixed horizontal column.  It deliberately does not
construct the upstream paper objects by choice: the absolute LGP Gaussian
log-theta lattice, the mono-analytic log-shell algorithm, the local integral
and finite-stage data, the full local log-links, the multiradial
functor and the labeled Kummer maps remain explicit inputs.  Horizontal
compatibility is assembled separately from two adjacent column boundaries and
uses the exact Definition 4.9(vii) times-mu prime-strip endpoints.

Once those inputs are supplied, the local packets, procession, Ind1 and Ind2
actions, generated quotient, vertical packet Kummer maps, Ind3 iterates and
upper-semi containments, and normalized log-volume compatibility are computed
projections or proved theorems.  In particular, this boundary does not pass
through the finite `ZMod` Stage 1 model.
-/

open CategoryTheory

namespace Iut

universe u

/--
The coherent source boundary for one horizontal column of Theorem 3.11.

The common local construction used by the multiradial presentation is
definitionally the common member of the vertical family.  This prevents the
horizontal quotient and vertical Kummer comparison from being assembled from
unrelated packets.
-/
structure SourceTheorem311ColumnBoundary
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta)
    [SourceSelectedPlaceFiberFiniteness theta]
    [SourceSelectedBadPlaceFiniteness theta] where
  lattice : SourceAbsoluteLGPGaussianLogThetaLattice models
  logShellAlgorithm : SourceMonoAnalyticLogShellAlgorithm models
  column : ℤ
  verticalFamily :
    lattice.VerticalFamilyConstruction logShellAlgorithm column
  verticalLogLinks :
    SourceAbsoluteLGPVerticalFullLogLinks lattice logShellAlgorithm
  presentationConstruction :
    lattice.PresentationConstruction logShellAlgorithm column
      verticalFamily.common
  multiradialAlgorithm :
    SourceTheorem311MultiradialAlgorithm
      (lattice.commonMonoAnalyticProcession column)
      presentationConstruction.toMultiradialPresentation
  siteLabeled : ℤ -> SourceTheorem311LabeledData.{u} theta.l
  labeledKummer :
    ∀ site,
      SourceTheorem311LabeledKummerIso
        (siteLabeled site) presentationConstruction.labeled
  siteSplitting :
    ∀ (site : ℤ) (place : SourceSelectedBadPlace theta)
      (label : IUTIIAbsoluteThetaLabel.{u} theta.l),
      SourceLGPSplittingMonoidAction
        (verticalFamily.sourcePacket site
          (SourceSelectedBadPlace.rationalPlace place) label).carrier
        ((verticalFamily.sourcePacket site
          (SourceSelectedBadPlace.rationalPlace place) label
          ).distinguishedSubmodule label.distinguishedFactor
            (SourceSelectedBadPlace.toAbove place))
  badPrimeLogKummer :
    ∀ (place : SourceSelectedBadPlace theta)
      (label : IUTIIAbsoluteThetaLabel.{u} theta.l),
      SourceTheorem311BadPrimeLogKummerData
        (fun site => siteSplitting site place label)
        (presentationConstruction.splitting place label)
        (fun site =>
          (verticalFamily.packetKummer site
            (SourceSelectedBadPlace.rationalPlace place) label).packetKummer)

namespace SourceTheorem311ColumnBoundary

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
    [SourceSelectedPlaceFiberFiniteness theta]
    [SourceSelectedBadPlaceFiniteness theta]

/-- The full absolute-label mono-analytic procession at the common column. -/
noncomputable def procession
    (boundary : SourceTheorem311ColumnBoundary models) :=
  boundary.lattice.commonMonoAnalyticProcession boundary.column

/-- The complete unquotiented packet, splitting, field, and Frobenioid output. -/
noncomputable def presentation
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceTheorem311MultiradialPresentation.{u} theta.l :=
  boundary.presentationConstruction.toMultiradialPresentation

/-- The common local packet family used simultaneously by the two directions. -/
noncomputable def localData
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceTheorem311LocalData.{u} theta.l :=
  boundary.verticalFamily.common.toTheorem311LocalData

/-- Ind1 is the actual procession-automorphism action induced by the functor. -/
noncomputable def ind1Action
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceTheorem311Ind1Action boundary.procession boundary.presentation.Realization :=
  boundary.multiradialAlgorithm.ind1Action

/-- Ind2 is derived summandwise from the common log-shell construction. -/
noncomputable def localInd2Action
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceTheorem311LocalInd2Action boundary.localData :=
  boundary.verticalFamily.common.toLocalInd2Action

/-- The complete Ind2 action fixes the nonlocal presentation coordinates. -/
noncomputable def ind2Action
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceEquivalenceAction boundary.localInd2Action.Choice
      boundary.presentation.Realization :=
  boundary.presentation.ind2Action boundary.localInd2Action

/-- The actual Ind1/Ind2 quotient of the source multiradial output. -/
noncomputable abbrev Quotient
    (boundary : SourceTheorem311ColumnBoundary models) :=
  boundary.multiradialAlgorithm.Quotient boundary.localInd2Action

/-- The adjacent packet relations derived from the full local log-links. -/
noncomputable def verticalUpperSemi
    (boundary : SourceTheorem311ColumnBoundary models) :
    boundary.lattice.VerticalUpperSemiData boundary.verticalFamily :=
  boundary.verticalLogLinks.toVerticalUpperSemiData boundary.verticalFamily

/-- Ind3 is constructed from the vertical family and its full local log-links. -/
noncomputable def ind3System
    (boundary : SourceTheorem311ColumnBoundary models) :
    SourceTheorem311Ind3System.{u} theta.l :=
  boundary.verticalFamily.toTheorem311Ind3System boundary.verticalUpperSemi

/-- The source-to-common packet Kummer comparison at one vertical site. -/
noncomputable def verticalLocalKummer
    (boundary : SourceTheorem311ColumnBoundary models) (site : ℤ) :
    SourceTheorem311VerticalLocalKummer
      (boundary.verticalFamily.site site).toTheorem311LocalData
      boundary.localData :=
  boundary.verticalFamily.verticalLocalKummer site

/-- Every actual procession automorphism is killed by the assembled quotient. -/
theorem quotient_sound_ind1
    (boundary : SourceTheorem311ColumnBoundary models)
    (automorphism : boundary.procession.MemberAutomorphismGroup)
    (value : boundary.presentation.Realization) :
    (Quotient.mk
        (sourceTheorem311IndeterminacySetoid
          boundary.ind1Action boundary.ind2Action) value :
        boundary.Quotient) =
      Quotient.mk
        (sourceTheorem311IndeterminacySetoid
          boundary.ind1Action boundary.ind2Action)
        (boundary.ind1Action.act automorphism value) :=
  boundary.multiradialAlgorithm.quotient_sound_ind1
    boundary.localInd2Action automorphism value

/-- Every independent local summand action is killed by the same quotient. -/
theorem quotient_sound_ind2
    (boundary : SourceTheorem311ColumnBoundary models)
    (choices : boundary.localInd2Action.Choice)
    (value : boundary.presentation.Realization) :
    (Quotient.mk
        (sourceTheorem311IndeterminacySetoid
          boundary.ind1Action boundary.ind2Action) value :
        boundary.Quotient) =
      Quotient.mk
        (sourceTheorem311IndeterminacySetoid
          boundary.ind1Action boundary.ind2Action)
        (boundary.ind2Action.act choices value) :=
  boundary.multiradialAlgorithm.quotient_sound_ind2
    boundary.localInd2Action choices value

/-- Vertical Kummer transport preserves the source normalized log-volume. -/
theorem vertical_logVolume_compatible
    (boundary : SourceTheorem311ColumnBoundary models)
    (site : ℤ)
    (rationalPlace : SourceRationalPlace)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l) :
    ((boundary.verticalFamily.site site).toTheorem311LocalData).logVolume
        rationalPlace label =
      boundary.localData.logVolume rationalPlace label :=
  (boundary.verticalLocalKummer site).logVolume_compatible
    rationalPlace label

/-- Ind3 normalized log-volume is independent of the vertical coordinate. -/
theorem ind3_logVolume_independent
    (boundary : SourceTheorem311ColumnBoundary models)
    (first second : ℤ)
    (rationalPlace : SourceRationalPlace)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l) :
    (boundary.ind3System.sourceFiniteStageVolume first rationalPlace label
        ).normalizedLogVolume.value =
      (boundary.ind3System.sourceFiniteStageVolume second rationalPlace label
        ).normalizedLogVolume.value :=
  boundary.ind3System.logVolume_eq_logVolume
    first second rationalPlace label

/-- The remaining adjacent bad-prime ambiguity has zero logarithm. -/
theorem badPrime_logarithm_eq
    (boundary : SourceTheorem311ColumnBoundary models)
    (place : SourceSelectedBadPlace theta)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l)
    (site : ℤ)
    (first : (boundary.siteSplitting site place label).monoidˣ)
    (second : (boundary.siteSplitting (site + 1) place label).monoidˣ)
    (related :
      (boundary.badPrimeLogKummer place label).AdmissibleAcrossLog
        site first second) :
    ((boundary.badPrimeLogKummer place label).logLinks.logarithm site
        ((boundary.badPrimeLogKummer place label).unitToLogUnit site first)
        ).toAdd =
      ((boundary.badPrimeLogKummer place label).logLinks.logarithm (site + 1)
        ((boundary.badPrimeLogKummer place label).unitToLogUnit
          (site + 1) second)).toAdd :=
  (boundary.badPrimeLogKummer place label).logarithm_eq_of_admissibleAcrossLog
    site first second related

end SourceTheorem311ColumnBoundary

/--
The source boundary for Theorem 3.11(iii) across two adjacent columns.

Unlike `SourceTheorem311ColumnBoundary`, this object owns both columns.  The
same-lattice and successor equalities ensure that its four indexed families
really compare `(n,m)` with `(n+1,m)`.  The final two equations tie the
horizontal `kappa` squares to the vertical labeled Kummer maps already used
by Theorem 3.11(ii).  Its clauses (a)--(b) cannot be populated with ordinary
`F`-prime-strips: the times-mu family is definitionally attached to the
mono-analytic transports of the corresponding theaters.
-/
structure SourceTheorem311HorizontalCorridorBoundary
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta)
    [SourceSelectedPlaceFiberFiniteness theta]
    [SourceSelectedBadPlaceFiniteness theta] where
  left : SourceTheorem311ColumnBoundary models
  right : SourceTheorem311ColumnBoundary models
  sameLattice : right.lattice = left.lattice
  adjacentColumns : right.column = left.column + 1
  timesMuConstruction :
    SourceTheorem311TimesMuPrimeStripConstruction left.lattice
  environmentMonoAnalyticPrimeStrips :
    SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily
      timesMuConstruction
  monoThetaSystems :
    SourceTheorem311MonoThetaProjectiveSystemFamily
      (SourceSelectedBadPlace theta)
  monoThetaClauseC :
    ∀ (site : ℤ) (place : SourceSelectedBadPlace theta),
      SourceTheorem311MonoThetaProjectiveSystemSquare
        monoThetaSystems left.column site place
  siteKappaClauseD :
    ∀ (site : ℤ) (label : IUTIIAbsoluteThetaLabel.{u} theta.l),
      SourceTheorem311LabeledHorizontalKummerSquare
        (left.siteLabeled site) (right.siteLabeled site) label
  commonKappaClauseD :
    ∀ label : IUTIIAbsoluteThetaLabel.{u} theta.l,
      SourceTheorem311LabeledHorizontalKummerSquare
        left.presentationConstruction.labeled
        right.presentationConstruction.labeled label
  siteCommonKappa_compatible :
    ∀ (site : ℤ) (label : IUTIIAbsoluteThetaLabel.{u} theta.l),
      ((left.labeledKummer site).kappaSolKummer label).hom ≫
          (commonKappaClauseD label).kappaSolHorizontal.hom =
        (siteKappaClauseD site label).kappaSolHorizontal.hom ≫
          ((right.labeledKummer site).kappaSolKummer label).hom
  siteCommonMInfinity_compatible :
    ∀ (site : ℤ) (label : IUTIIAbsoluteThetaLabel.{u} theta.l),
      ((left.labeledKummer site).mInfinityKummer label).hom ≫
          (commonKappaClauseD label).mInfinityHorizontal.hom =
        (siteKappaClauseD site label).mInfinityHorizontal.hom ≫
          ((right.labeledKummer site).mInfinityKummer label).hom

namespace SourceTheorem311HorizontalCorridorBoundary

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
    [SourceSelectedPlaceFiberFiniteness theta]
    [SourceSelectedBadPlaceFiniteness theta]

/-- The actual horizontal theta link whose realizations occur in the corridor. -/
def horizontalThetaLink
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    SourceThetaLinkCore
      (boundary.left.lattice.theater boundary.left.column site)
      (boundary.left.lattice.theater (boundary.left.column + 1) site) :=
  boundary.left.lattice.horizontalThetaLink boundary.left.column site

/-- All site and coric times-mu strips, computed by one reconstruction algorithm. -/
def timesMuPrimeStrips
    (boundary : SourceTheorem311HorizontalCorridorBoundary models) :
    SourceTheorem311TimesMuPrimeStripFamily boundary.left.lattice :=
  boundary.timesMuConstruction.toFamily

/-- The environment times-mu strips and comparisons, all induced by reconstruction. -/
def environmentPrimeStrips
    (boundary : SourceTheorem311HorizontalCorridorBoundary models) :
    SourceTheorem311EnvironmentTimesMuPrimeStripFamily
      boundary.timesMuConstruction.toFamily :=
  boundary.environmentMonoAnalyticPrimeStrips.toTimesMu

/--
Clause (iii)(a), derived from the mono-analytic theta link, Corollary 4.10(iv)
fullness, and the two-sided Theorem 1.5 Kummer comparisons.
-/
noncomputable def primeStripClauseA
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    SourceTheorem311TimesMuTrianglePrimeStripSquare
      boundary.timesMuPrimeStrips boundary.left.column site :=
  boundary.timesMuConstruction.toTriangleSquare boundary.left.column site

/-- The right column theater is propositionally the successor endpoint. -/
theorem right_theater_eq
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    boundary.right.lattice.theater boundary.right.column site =
      boundary.left.lattice.theater (boundary.left.column + 1) site := by
  rw [boundary.sameLattice, boundary.adjacentColumns]

/-- Clause (iii)(b), derived from clause (a) and the natural comparisons. -/
noncomputable def environmentPrimeStripClauseB
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    SourceTheorem311EnvironmentTimesMuPrimeStripSquare
      boundary.environmentPrimeStrips boundary.left.column site :=
  SourceTheorem311EnvironmentTimesMuPrimeStripSquare.ofTriangle
    boundary.environmentPrimeStrips boundary.left.column site
    (boundary.primeStripClauseA site)

/-- Clause (iii)(a) commutes at every vertical lattice site. -/
theorem primeStripClauseA_commutes
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (boundary.primeStripClauseA site).leftKummer
        (boundary.primeStripClauseA site).lowerHorizontal =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (boundary.primeStripClauseA site).upperHorizontal
        (boundary.primeStripClauseA site).rightKummer :=
  (boundary.primeStripClauseA site).commutes

/-- Clause (iii)(b) commutes at every vertical lattice site. -/
theorem environmentPrimeStripClauseB_commutes
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (boundary.environmentPrimeStripClauseB site).leftKummer
        (boundary.environmentPrimeStripClauseB site).lowerHorizontal =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (boundary.environmentPrimeStripClauseB site).upperHorizontal
        (boundary.environmentPrimeStripClauseB site).rightKummer :=
  (boundary.environmentPrimeStripClauseB site).commutes

/-- Clause (iii)(c) commutes at every site and selected bad place. -/
theorem monoThetaClauseC_commutes
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) (place : SourceSelectedBadPlace theta) :
    (boundary.monoThetaClauseC site place).leftKummer.groupDiagramIso.hom ≫
        (boundary.monoThetaClauseC site place).lowerHorizontal.groupDiagramIso.hom =
      (boundary.monoThetaClauseC site place).upperHorizontal.groupDiagramIso.hom ≫
        (boundary.monoThetaClauseC site place).rightKummer.groupDiagramIso.hom :=
  (boundary.monoThetaClauseC site place).commutes

/-- The site-level clause (iii)(d) square commutes for every absolute label. -/
theorem siteKappaClauseD_commutes
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (site : ℤ) (label : IUTIIAbsoluteThetaLabel.{u} theta.l) :
    (boundary.siteKappaClauseD site label).kappaSolHorizontal.hom ≫
        (boundary.right.siteLabeled site).kappaToMInfinity label =
      (boundary.left.siteLabeled site).kappaToMInfinity label ≫
        (boundary.siteKappaClauseD site label).mInfinityHorizontal.hom :=
  (boundary.siteKappaClauseD site label).kappaMInfinity_compatible

/-- The common-column clause (iii)(d) square commutes for every label. -/
theorem commonKappaClauseD_commutes
    (boundary : SourceTheorem311HorizontalCorridorBoundary models)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l) :
    (boundary.commonKappaClauseD label).kappaSolHorizontal.hom ≫
        boundary.right.presentationConstruction.labeled.kappaToMInfinity label =
      boundary.left.presentationConstruction.labeled.kappaToMInfinity label ≫
        (boundary.commonKappaClauseD label).mInfinityHorizontal.hom :=
  (boundary.commonKappaClauseD label).kappaMInfinity_compatible

end SourceTheorem311HorizontalCorridorBoundary

end Iut
