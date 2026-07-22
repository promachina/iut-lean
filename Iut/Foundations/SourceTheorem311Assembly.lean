/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceVerticalLogLink

/-!
# Source assembly for IUT III, Theorem 3.11

This module assembles the source-faithful constructions of
`SourceTheorem311` at one fixed horizontal column.  It deliberately does not
construct the upstream paper objects by choice: the absolute LGP Gaussian
log-theta lattice, the mono-analytic log-shell algorithm, the local integral
and finite-stage data, the full local log-links, the multiradial
functor, the labeled Kummer maps, and the horizontal compatibility squares
remain explicit inputs.

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
  horizontalCompatibility :
    SourceTheorem311HorizontalCompatibilitySystem models

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

/-- The first prime-strip horizontal Kummer square commutes. -/
theorem primeStripClauseA_commutes
    (boundary : SourceTheorem311ColumnBoundary models) :
    boundary.horizontalCompatibility.primeStripClauseA.verticalKummer.hom.left ≫
        boundary.horizontalCompatibility.primeStripClauseA.targetHorizontal.hom =
      boundary.horizontalCompatibility.primeStripClauseA.sourceHorizontal.hom ≫
        boundary.horizontalCompatibility.primeStripClauseA.verticalKummer.hom.right :=
  boundary.horizontalCompatibility.primeStripClauseA.commutes

/-- The environment/prime-strip horizontal Kummer square commutes. -/
theorem environmentPrimeStripClauseB_commutes
    (boundary : SourceTheorem311ColumnBoundary models) :
    boundary.horizontalCompatibility.environmentPrimeStripClauseB.verticalKummer.hom.left ≫
        boundary.horizontalCompatibility.environmentPrimeStripClauseB.targetHorizontal.hom =
      boundary.horizontalCompatibility.environmentPrimeStripClauseB.sourceHorizontal.hom ≫
        boundary.horizontalCompatibility.environmentPrimeStripClauseB.verticalKummer.hom.right :=
  boundary.horizontalCompatibility.environmentPrimeStripClauseB.commutes

/-- The mono-theta projective-system square of clause (iii)(c) commutes. -/
theorem monoThetaClauseC_commutes
    (boundary : SourceTheorem311ColumnBoundary models) :
    boundary.horizontalCompatibility.monoThetaClauseC.leftKummer.groupDiagramIso.hom ≫
        boundary.horizontalCompatibility.monoThetaClauseC.lowerHorizontal.groupDiagramIso.hom =
      boundary.horizontalCompatibility.monoThetaClauseC.upperHorizontal.groupDiagramIso.hom ≫
        boundary.horizontalCompatibility.monoThetaClauseC.rightKummer.groupDiagramIso.hom :=
  boundary.horizontalCompatibility.monoThetaClauseC.commutes

/-- The profinite kappa-solvable horizontal Kummer square commutes. -/
theorem kappaClauseD_commutes
    (boundary : SourceTheorem311ColumnBoundary models) :
    boundary.horizontalCompatibility.kappaClauseD.verticalKummer.hom.left ≫
        boundary.horizontalCompatibility.kappaClauseD.targetHorizontal.hom =
      boundary.horizontalCompatibility.kappaClauseD.sourceHorizontal.hom ≫
        boundary.horizontalCompatibility.kappaClauseD.verticalKummer.hom.right :=
  boundary.horizontalCompatibility.kappaClauseD.commutes

end SourceTheorem311ColumnBoundary

end Iut
