/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Theorem311

/-!
Step (xi) source layer for the Stage 1 IUT corridor.

This module contains the source-facing hull/determinant and IPL data that sit
between the Theorem 3.11 multiradial source records and the endpoint corridor:
hull/det bridge data, structured SHE/IPL transport sources, source obligation
and package-audit constructors, and the holomorphic hull/determinant Step (xi)
source objects.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

/--
Source-facing split hull+det evidence for a Stage 1 source package.

This records that the hull+det bridge used by the package is backed by a
separate common-hull construction and determinant/log-volume bound.
-/
structure IUTStage1SourceHullDetData
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  sourceData : package.preLedger.HullDetSourceData

namespace IUTStage1SourceHullDetData

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def ofUnionSubset
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hull : Region target)
    (hsubset :
      Region.Subset package.preLedger.output.comparisons.targetUnion hull)
    (hvolume :
      RegionMeasure.HasVolumeAtMost package.preLedger.measure hull
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionSubset
            (output := package.preLedger.output)
            (measure := package.preLedger.measure)
            (bound := package.preLedger.thetaSigned)
            operation hullOperation determinantOperation hull hsubset hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    IUTStage1SourceHullDetData package :=
  { sourceData :=
      IUTStage1PreLedgerData.HullDetSourceData.ofUnionSubset
        (data := package.preLedger)
        operation hullOperation determinantOperation hull hsubset hvolume hbridge }

def ofUnionHull
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (operator : HullOperator target)
    (hvolume :
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (operator.hull package.preLedger.output.comparisons.targetUnion)
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
            (output := package.preLedger.output)
            (measure := package.preLedger.measure)
            (bound := package.preLedger.thetaSigned)
            operation hullOperation determinantOperation operator hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    IUTStage1SourceHullDetData package :=
  { sourceData :=
      IUTStage1PreLedgerData.HullDetSourceData.ofUnionHull
        (data := package.preLedger)
        operation hullOperation determinantOperation operator hvolume hbridge }

def holomorphicHullShadowVolumeBound
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      hullData.logVolume
          (hullData.hullRegion
            package.preLedger.output.comparisons.targetUnion.toSet) <=
        package.preLedger.thetaSigned) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      ((hullData.toRegionHullOperator).hull
        package.preLedger.output.comparisons.targetUnion)
      package.preLedger.thetaSigned := by
  unfold RegionMeasure.HasVolumeAtMost
  rw [measure_eq_hullLogVolume]
  simpa using determinant_bound

def holomorphicHullShadowStructuredBridge
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      hullData.logVolume
          (hullData.hullRegion
            package.preLedger.output.comparisons.targetUnion.toSet) <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.StructuredHullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
    (output := package.preLedger.output)
    (measure := package.preLedger.measure)
    (bound := package.preLedger.thetaSigned)
    operation hullOperation determinantOperation
    hullData.toRegionHullOperator
    (holomorphicHullShadowVolumeBound (package := package)
      hullData measure_eq_hullLogVolume determinant_bound)

def holomorphicHullShadowHullDetBridgeData
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      hullData.logVolume
          (hullData.hullRegion
            package.preLedger.output.comparisons.targetUnion.toSet) <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  (holomorphicHullShadowStructuredBridge (package := package)
    operation hullOperation determinantOperation hullData
    measure_eq_hullLogVolume determinant_bound)
      |>.toHullDetHullBridgeData |>.toHullDetBridgeData

def ofHolomorphicHullShadow
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      hullData.logVolume
          (hullData.hullRegion
            package.preLedger.output.comparisons.targetUnion.toSet) <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        holomorphicHullShadowHullDetBridgeData (package := package)
          operation hullOperation determinantOperation hullData
          measure_eq_hullLogVolume determinant_bound) :
    IUTStage1SourceHullDetData package :=
  ofUnionHull (package := package)
    operation hullOperation determinantOperation
    hullData.toRegionHullOperator
    (holomorphicHullShadowVolumeBound (package := package)
      hullData measure_eq_hullLogVolume determinant_bound)
    hbridge

def canonicalApproximantHullShadowBound
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_targetUnion :
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    approximantSource.hullData.logVolume
        (approximantSource.hullData.hullRegion
          package.preLedger.output.comparisons.targetUnion.toSet) <=
      package.preLedger.thetaSigned := by
  rw [← theta_union_eq_targetUnion]
  calc
    approximantSource.hullData.logVolume
        (approximantSource.hullData.hullRegion
          approximantSource.thetaImageUnion) =
        approximantSource.approximantLogVolume := by
          change approximantSource.hullData.logVolume
              approximantSource.thetaHull =
            approximantSource.hullData.logVolume
              approximantSource.approximantRegion
          rw [← approximant_eq_canonical_hull]
    _ = approximantSource.determinant.normalizedLogVolume :=
        approximantSource.approximantLogVolume_eq_normalized_determinant
    _ <= package.preLedger.thetaSigned := determinant_bound

def canonicalApproximantHullDetBridgeData
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_targetUnion :
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  holomorphicHullShadowHullDetBridgeData (package := package)
    operation hullOperation determinantOperation approximantSource.hullData
    measure_eq_hullLogVolume
    (canonicalApproximantHullShadowBound (package := package)
      approximantSource theta_union_eq_targetUnion approximant_eq_canonical_hull
      determinant_bound)

def ofCanonicalApproximant
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_targetUnion :
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalApproximantHullDetBridgeData (package := package)
          operation hullOperation determinantOperation approximantSource
          theta_union_eq_targetUnion approximant_eq_canonical_hull
          measure_eq_hullLogVolume determinant_bound) :
    IUTStage1SourceHullDetData package :=
  ofHolomorphicHullShadow (package := package)
    operation hullOperation determinantOperation approximantSource.hullData
    measure_eq_hullLogVolume
    (canonicalApproximantHullShadowBound (package := package)
      approximantSource theta_union_eq_targetUnion approximant_eq_canonical_hull
      determinant_bound)
    hbridge

noncomputable def canonicalWeightedDeterminantApproximantSource
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource) :
    IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
      (Point target) index :=
  IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.ofWeightedDeterminant
    hullData possibleThetaImage qPilotRegion approximant
    q_subset_approximant determinantSource compatibility

noncomputable def canonicalHullWeightedDeterminantApproximantSource
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
  IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
    (Point target) index :=
  IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.ofCanonicalHullWeightedDeterminant
    hullData possibleThetaImage qPilotRegion q_subset_hull
    determinantSource compatibility

noncomputable def canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
  IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
    (Point target) index :=
  open IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow in
  ofCanonicalHullWeightedDeterminantOfQSubsetUnion
    hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
    determinantSource compatibility

theorem canonicalWeightedDeterminantApproximantSource_normalized_bound
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    (canonicalWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility
      |>.determinant).normalizedLogVolume <=
      package.preLedger.thetaSigned := by
  change determinantSource.toDeterminantLogVolume.normalizedLogVolume <=
    package.preLedger.thetaSigned
  rw [determinantSource.toDeterminantLogVolume_normalizedLogVolume_eq]
  exact determinant_bound

theorem canonicalWeightedDeterminantApproximantSource_normalized_bound_of_tensorPower
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    (canonicalWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility
      |>.determinant).normalizedLogVolume <=
      package.preLedger.thetaSigned :=
  canonicalWeightedDeterminantApproximantSource_normalized_bound
    (package := package)
    hullData possibleThetaImage qPilotRegion approximant
    q_subset_approximant determinantSource compatibility
    ((IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound)

theorem canonicalHullWeightedDeterminantApproximantSource_normalized_bound
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility |>.determinant).normalizedLogVolume <=
      package.preLedger.thetaSigned := by
  have hnorm :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility |>.determinant).normalizedLogVolume =
        determinantSource.determinantLogVolume := by
    simpa [canonicalHullWeightedDeterminantApproximantSource,
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.ofCanonicalHullWeightedDeterminant,
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.ofWeightedDeterminant] using
      determinantSource.toDeterminantLogVolume_normalizedLogVolume_eq
  rw [hnorm]
  exact determinant_bound

theorem canonicalHullWeightedDeterminantApproximantSource_eq_hull
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
    (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility).approximantRegion =
      (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility).thetaHull :=
  open IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow in
  ofCanonicalHullWeightedDeterminant_approximantRegion_eq_thetaHull
    hullData possibleThetaImage qPilotRegion q_subset_hull
    determinantSource compatibility

theorem canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion_eq_hull
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
    (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility).approximantRegion =
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility).thetaHull :=
  rfl

noncomputable def canonicalWeightedDeterminantHullDetBridgeData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let approximantSource :=
    canonicalWeightedDeterminantApproximantSource
      hullData possibleThetaImage qPilotRegion approximant
      q_subset_approximant determinantSource compatibility
  canonicalApproximantHullDetBridgeData (package := package)
    operation hullOperation determinantOperation approximantSource
    theta_union_eq_targetUnion approximant_eq_canonical_hull
    measure_eq_hullLogVolume
    (canonicalWeightedDeterminantApproximantSource_normalized_bound
      (package := package)
      hullData possibleThetaImage qPilotRegion approximant
      q_subset_approximant determinantSource compatibility
      determinant_bound)

noncomputable def canonicalTensorPowerWeightedDeterminantHullDetBridgeData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  canonicalWeightedDeterminantHullDetBridgeData (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion approximant q_subset_approximant determinantSource
    compatibility theta_union_eq_targetUnion approximant_eq_canonical_hull
    measure_eq_hullLogVolume determinant_bound

noncomputable def canonicalHullWeightedDeterminantHullDetBridgeData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let approximantSource :=
    canonicalHullWeightedDeterminantApproximantSource
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility
  canonicalApproximantHullDetBridgeData (package := package)
    operation hullOperation determinantOperation approximantSource
    theta_union_eq_targetUnion
    (canonicalHullWeightedDeterminantApproximantSource_eq_hull
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility)
    measure_eq_hullLogVolume
    (canonicalHullWeightedDeterminantApproximantSource_normalized_bound
      (package := package)
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility determinant_bound)

noncomputable def canonicalHullWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i) :=
    fun _ hx =>
      hullData.region_subset_hull (⋃ i, possibleThetaImage i)
        (q_subset_thetaImageUnion hx)
  canonicalHullWeightedDeterminantHullDetBridgeData (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    (by
      simpa [canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion,
        canonicalHullWeightedDeterminantApproximantSource]
        using theta_union_eq_targetUnion)
    measure_eq_hullLogVolume determinant_bound

noncomputable def canonicalHullTensorPowerWeightedDeterminantHullDetBridgeData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  canonicalHullWeightedDeterminantHullDetBridgeData (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    theta_union_eq_targetUnion measure_eq_hullLogVolume determinant_bound

noncomputable def canonicalHullTensorPowerWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  canonicalHullWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
    (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
    theta_union_eq_targetUnion measure_eq_hullLogVolume determinant_bound

noncomputable def ofCanonicalWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalWeightedDeterminantHullDetBridgeData (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility theta_union_eq_targetUnion
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          determinant_bound) :
    IUTStage1SourceHullDetData package :=
  let approximantSource :=
    canonicalWeightedDeterminantApproximantSource
      hullData possibleThetaImage qPilotRegion approximant
      q_subset_approximant determinantSource compatibility
  ofCanonicalApproximant (package := package)
    operation hullOperation determinantOperation approximantSource
    theta_union_eq_targetUnion approximant_eq_canonical_hull
    measure_eq_hullLogVolume
    (canonicalWeightedDeterminantApproximantSource_normalized_bound
      (package := package)
      hullData possibleThetaImage qPilotRegion approximant
      q_subset_approximant determinantSource compatibility
    determinant_bound)
    hbridge

noncomputable def ofCanonicalTensorPowerWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalTensorPowerWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility theta_union_eq_targetUnion
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          tensorPower_bound) :
    IUTStage1SourceHullDetData package :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  ofCanonicalWeightedDeterminant (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion approximant q_subset_approximant determinantSource
    compatibility theta_union_eq_targetUnion approximant_eq_canonical_hull
    measure_eq_hullLogVolume determinant_bound hbridge

noncomputable def ofCanonicalHullWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_targetUnion measure_eq_hullLogVolume
          determinant_bound) :
    IUTStage1SourceHullDetData package :=
  let approximantSource :=
    canonicalHullWeightedDeterminantApproximantSource
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility
  ofCanonicalApproximant (package := package)
    operation hullOperation determinantOperation approximantSource
    theta_union_eq_targetUnion
    (canonicalHullWeightedDeterminantApproximantSource_eq_hull
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility)
    measure_eq_hullLogVolume
    (canonicalHullWeightedDeterminantApproximantSource_normalized_bound
      (package := package)
      hullData possibleThetaImage qPilotRegion q_subset_hull
      determinantSource compatibility determinant_bound)
    hbridge

noncomputable def ofCanonicalHullWeightedDeterminantOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_targetUnion
          measure_eq_hullLogVolume determinant_bound) :
    IUTStage1SourceHullDetData package :=
  let q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i) :=
    fun _ hx =>
      hullData.region_subset_hull (⋃ i, possibleThetaImage i)
        (q_subset_thetaImageUnion hx)
  ofCanonicalHullWeightedDeterminant (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    (by
      simpa [canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion,
        canonicalHullWeightedDeterminantApproximantSource]
        using theta_union_eq_targetUnion)
    measure_eq_hullLogVolume determinant_bound hbridge

noncomputable def ofCanonicalHullTensorPowerWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_targetUnion measure_eq_hullLogVolume
          tensorPower_bound) :
    IUTStage1SourceHullDetData package :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  ofCanonicalHullWeightedDeterminant (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    theta_union_eq_targetUnion measure_eq_hullLogVolume determinant_bound hbridge

noncomputable def ofCanonicalHullTensorPowerWeightedDeterminantOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_targetUnion
          measure_eq_hullLogVolume tensorPower_bound) :
    IUTStage1SourceHullDetData package :=
  let determinant_bound :=
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
  ofCanonicalHullWeightedDeterminantOfQSubsetUnion (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
    theta_union_eq_targetUnion measure_eq_hullLogVolume determinant_bound
    hbridge

def stepAudit (data : IUTStage1SourceHullDetData package) :
    data.sourceData.structuredHullDet.StepAudit package.preLedger.certificate :=
  data.sourceData.stepAudit

theorem targetUnion_subset_hull
    (data : IUTStage1SourceHullDetData package) :
    Region.Subset package.preLedger.output.comparisons.targetUnion
      (data.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull :=
  data.sourceData.targetUnion_subset_hull

theorem determinantVolumeBound
    (data : IUTStage1SourceHullDetData package) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (data.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned :=
  data.sourceData.determinantVolumeBound

theorem hullDetBridge_eq
    (data : IUTStage1SourceHullDetData package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  data.sourceData.hullDetBridge_eq

def bridgeData
    (data : IUTStage1SourceHullDetData package) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData

theorem hullDetBridge_eq_bridgeData
    (data : IUTStage1SourceHullDetData package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      data.bridgeData :=
  data.sourceData.hullDetBridge_eq

theorem choiceTargetVolume_le_thetaSigned
    (data : IUTStage1SourceHullDetData package) (choice : index) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison choice) <=
      package.preLedger.thetaSigned :=
  data.sourceData.choiceTargetVolume_le_thetaSigned choice

theorem allTargetsAtMost
    (data : IUTStage1SourceHullDetData package) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  data.sourceData.allTargetsAtMost

theorem ofUnionSubset_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hull : Region target)
    (hsubset :
      Region.Subset package.preLedger.output.comparisons.targetUnion hull)
    (hvolume :
      RegionMeasure.HasVolumeAtMost package.preLedger.measure hull
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionSubset
            (output := package.preLedger.output)
            (measure := package.preLedger.measure)
            (bound := package.preLedger.thetaSigned)
            operation hullOperation determinantOperation hull hsubset hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    let data :=
      ofUnionSubset (package := package)
        operation hullOperation determinantOperation hull hsubset hvolume hbridge;
    Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro data
    exact
      ⟨data.targetUnion_subset_hull,
        data.determinantVolumeBound,
        data.allTargetsAtMost,
        data.hullDetBridge_eq⟩

theorem ofUnionHull_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (operator : HullOperator target)
    (hvolume :
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (operator.hull package.preLedger.output.comparisons.targetUnion)
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
            (output := package.preLedger.output)
            (measure := package.preLedger.measure)
            (bound := package.preLedger.thetaSigned)
            operation hullOperation determinantOperation operator hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    let data :=
      ofUnionHull (package := package)
        operation hullOperation determinantOperation operator hvolume hbridge;
    (data.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull =
        operator.hull package.preLedger.output.comparisons.targetUnion ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro data
    exact
      ⟨rfl,
        data.targetUnion_subset_hull,
        data.determinantVolumeBound,
        data.allTargetsAtMost,
        data.hullDetBridge_eq⟩

theorem ofHolomorphicHullShadow_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      hullData.logVolume
          (hullData.hullRegion
            package.preLedger.output.comparisons.targetUnion.toSet) <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        holomorphicHullShadowHullDetBridgeData (package := package)
          operation hullOperation determinantOperation hullData
          measure_eq_hullLogVolume determinant_bound) :
    let data :=
      ofHolomorphicHullShadow (package := package)
        operation hullOperation determinantOperation hullData
        measure_eq_hullLogVolume determinant_bound hbridge;
    (data.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull.toSet =
        hullData.hullRegion
          package.preLedger.output.comparisons.targetUnion.toSet ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro data
    exact
      ⟨rfl,
        data.targetUnion_subset_hull,
        data.determinantVolumeBound,
        data.allTargetsAtMost,
        data.hullDetBridge_eq⟩

theorem ofCanonicalApproximant_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_targetUnion :
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalApproximantHullDetBridgeData (package := package)
          operation hullOperation determinantOperation approximantSource
          theta_union_eq_targetUnion approximant_eq_canonical_hull
          measure_eq_hullLogVolume determinant_bound) :
    let data :=
      ofCanonicalApproximant (package := package)
        operation hullOperation determinantOperation approximantSource
        theta_union_eq_targetUnion approximant_eq_canonical_hull
        measure_eq_hullLogVolume determinant_bound hbridge;
    (data.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull.toSet =
        approximantSource.hullData.hullRegion
          package.preLedger.output.comparisons.targetUnion.toSet ∧
      approximantSource.approximantLogVolume =
        approximantSource.determinant.normalizedLogVolume ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        data.sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro data
    exact
      ⟨rfl,
        approximantSource.approximantLogVolume_eq_normalized_determinant,
        data.targetUnion_subset_hull,
        data.determinantVolumeBound,
        data.allTargetsAtMost,
        data.hullDetBridge_eq⟩

theorem ofCanonicalWeightedDeterminant_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalWeightedDeterminantHullDetBridgeData (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility theta_union_eq_targetUnion
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          determinant_bound) :
    let approximantSource :=
      canonicalWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility;
    let data :=
      ofCanonicalWeightedDeterminant (package := package)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion approximant q_subset_approximant
        determinantSource compatibility theta_union_eq_targetUnion
        approximant_eq_canonical_hull measure_eq_hullLogVolume
        determinant_bound hbridge;
    approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  by
    intro approximantSource data
    have hnormalized :
        approximantSource.determinant.normalizedLogVolume <=
          package.preLedger.thetaSigned :=
      canonicalWeightedDeterminantApproximantSource_normalized_bound
        (package := package)
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility
        determinant_bound
    have endpoint :=
      ofCanonicalApproximant_endpoint (package := package)
        operation hullOperation determinantOperation approximantSource
        theta_union_eq_targetUnion approximant_eq_canonical_hull
        measure_eq_hullLogVolume hnormalized hbridge
    have happ_volume :
        approximantSource.approximantLogVolume =
          determinantSource.determinantLogVolume := by
      simpa [approximantSource,
        canonicalWeightedDeterminantApproximantSource,
        IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.approximantLogVolume,
        IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow.approximantRegion]
        using compatibility.approximant_eq_determinantLogVolume
    exact
      ⟨theta_union_eq_targetUnion,
        happ_volume,
        hnormalized,
        endpoint.2.2.1,
        endpoint.2.2.2.1,
        endpoint.2.2.2.2.1⟩

theorem ofCanonicalHullTensorPowerWeightedDeterminant_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_targetUnion measure_eq_hullLogVolume
          tensorPower_bound) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility;
    let data :=
      ofCanonicalHullTensorPowerWeightedDeterminant (package := package)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion q_subset_hull determinantSource
        compatibility theta_union_eq_targetUnion measure_eq_hullLogVolume
        tensorPower_bound hbridge;
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
        package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  by
    intro approximantSource data
    have happ_eq_hull :
        approximantSource.approximantRegion = approximantSource.thetaHull :=
      canonicalHullWeightedDeterminantApproximantSource_eq_hull
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility
    have happ_volume :
        approximantSource.approximantLogVolume =
          determinantSource.determinantLogVolume := by
      open IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow in
      simpa [approximantSource, canonicalHullWeightedDeterminantApproximantSource,
        ofCanonicalHullWeightedDeterminant, ofWeightedDeterminant,
        approximantLogVolume, approximantRegion]
        using compatibility.approximant_eq_determinantLogVolume
    exact
      ⟨tensorPower_bound,
        happ_eq_hull,
        happ_volume,
        data.targetUnion_subset_hull,
        data.determinantVolumeBound,
        data.allTargetsAtMost⟩

theorem ofCanonicalHullWeightedDeterminantOfQSubsetUnion_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_targetUnion
          measure_eq_hullLogVolume determinant_bound) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility;
    let data :=
      ofCanonicalHullWeightedDeterminantOfQSubsetUnion (package := package)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
        theta_union_eq_targetUnion measure_eq_hullLogVolume determinant_bound
        hbridge;
    approximantSource.qPilotRegion ⊆ approximantSource.thetaImageUnion ∧
      approximantSource.qPilotRegion ⊆ approximantSource.thetaHull ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned :=
  by
    intro approximantSource data
    have happ_volume :
        approximantSource.approximantLogVolume =
          determinantSource.determinantLogVolume := by
      open IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow in
      simpa [approximantSource,
        canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion,
        ofCanonicalHullWeightedDeterminantOfQSubsetUnion,
        ofWeightedDeterminant, approximantLogVolume, approximantRegion]
        using compatibility.approximant_eq_determinantLogVolume
    exact
      ⟨q_subset_thetaImageUnion,
        approximantSource.qPilotRegion_subset_thetaHull,
        theta_union_eq_targetUnion,
        rfl,
        happ_volume,
        data.targetUnion_subset_hull,
        data.determinantVolumeBound⟩

open IUTStage1NaiveFrobeniusTensorPowerLogVolume in
theorem ofCanonicalHullTensorPowerWeightedDeterminantOfQSubsetUnion_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_targetUnion :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_targetUnion
          measure_eq_hullLogVolume tensorPower_bound) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility;
    let data :=
      ofCanonicalHullTensorPowerWeightedDeterminantOfQSubsetUnion
        (package := package)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
        theta_union_eq_targetUnion measure_eq_hullLogVolume tensorPower_bound
        hbridge;
    approximantSource.qPilotRegion ⊆ approximantSource.thetaImageUnion ∧
      approximantSource.qPilotRegion ⊆ approximantSource.thetaHull ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      Region.Subset package.preLedger.output.comparisons.targetUnion
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (data.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull package.preLedger.thetaSigned :=
  by
    intro approximantSource data
    let determinant_bound :
        determinantSource.determinantLogVolume <=
          package.preLedger.thetaSigned :=
      (ofWeightedDeterminant_normalizedLogVolume_le_iff
        determinantSource package.preLedger.thetaSigned).mp tensorPower_bound
    have hweighted :=
      ofCanonicalHullWeightedDeterminantOfQSubsetUnion_endpoint
        (package := package)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
        theta_union_eq_targetUnion measure_eq_hullLogVolume
        determinant_bound hbridge
    exact
      ⟨hweighted.1,
        hweighted.2.1,
        hweighted.2.2.1,
        tensorPower_bound,
        hweighted.2.2.2.1,
        hweighted.2.2.2.2.1,
        hweighted.2.2.2.2.2.1,
        hweighted.2.2.2.2.2.2⟩

end IUTStage1SourceHullDetData

/--
Strengthened source obligations that include split hull+det provenance.

`IUTStage1SourceObligations` build the public comparison endpoint. This record
is the stricter route a source-level IUT proof should target when it wants the
final comparison to remember its union-of-possible-images hull.
-/
structure IUTStage1SourceHullDetObligations
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  sourceObligations : IUTStage1SourceObligations package
  hullDetData : IUTStage1SourceHullDetData package

namespace IUTStage1SourceHullDetObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def toSourceObligations
    (obligations : IUTStage1SourceHullDetObligations package) :
    IUTStage1SourceObligations package :=
  obligations.sourceObligations

theorem algorithmCertified
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.preLedger.output.Certified :=
  obligations.sourceObligations.algorithm_certified

theorem sheArrowMatchesCertificate
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  obligations.sourceObligations.she_arrow_matches_certificate

theorem qPilotPositive
    (obligations : IUTStage1SourceHullDetObligations package) :
    0 < -package.preLedger.qSigned :=
  obligations.sourceObligations.q_pilot_positive

theorem normalization
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.preLedger.normalization :=
  obligations.sourceObligations.normalization

theorem targetUnion_subset_hull
    (obligations : IUTStage1SourceHullDetObligations package) :
    Region.Subset package.preLedger.output.comparisons.targetUnion
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull :=
  obligations.hullDetData.targetUnion_subset_hull

theorem determinantVolumeBound
    (obligations : IUTStage1SourceHullDetObligations package) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned :=
  obligations.hullDetData.determinantVolumeBound

theorem choiceTargetVolume_le_thetaSigned
    (obligations : IUTStage1SourceHullDetObligations package) (choice : index) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison choice) <=
      package.preLedger.thetaSigned :=
  obligations.hullDetData.choiceTargetVolume_le_thetaSigned choice

theorem allTargetsAtMost
    (obligations : IUTStage1SourceHullDetObligations package) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  obligations.hullDetData.allTargetsAtMost

end IUTStage1SourceHullDetObligations

/--
Strengthened source-facing SHE input for the Theorem 3.11 route.

This records a non-inert structured SHE context and only connects it to the
existing certificate/alignment fields. It does not construct a comparison
payload or endpoint.
-/
structure IUTStage1Theorem311StructuredSHE
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  context :
    QualitativeData.StructuredSHEContext package.preLedger.output.family
  she_datum_matches_certificate :
    context.sheDatum = package.preLedger.certificate.she
  she_arrow_matches_context :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      context.sheDatum

namespace IUTStage1Theorem311StructuredSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem hasStructuredSHE
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  structuredSHE.context.hasStructuredSHE

theorem sheDatumMatchesCertificate
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    structuredSHE.context.sheDatum = package.preLedger.certificate.she :=
  structuredSHE.she_datum_matches_certificate

theorem sheArrowMatchesContext
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      structuredSHE.context.sheDatum :=
  structuredSHE.she_arrow_matches_context

theorem hodgeTheaterSHEAlignment
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  structuredSHE.sheArrowMatchesContext.trans
    structuredSHE.sheDatumMatchesCertificate

def sheAlignment
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    IUTStage1Theorem311SHEAlignment package :=
  { alignment := structuredSHE.hodgeTheaterSHEAlignment }

theorem sheAlignment_hodgeTheaterSHEAlignment_eq
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    structuredSHE.sheAlignment.hodgeTheaterSHEAlignment =
      structuredSHE.hodgeTheaterSHEAlignment :=
  rfl

theorem domainHistory_ne_codomainHistory
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    structuredSHE.context.domainStructure.theater.side ≠
      structuredSHE.context.codomainStructure.theater.side :=
  structuredSHE.context.domainHistory_ne_codomainHistory

theorem commonContainerContextMatches
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    package.preLedger.chartedContainer.commonContainer.context =
      structuredSHE.context.sharedContext := by
  have hcontainer :
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum.sharedContext =
        package.preLedger.chartedContainer.commonContainer.context :=
    package.preLedger.chartedContainer.commonContainer.she_context_matches
  have harrow :
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum.sharedContext =
        structuredSHE.context.sheDatum.sharedContext := by
    exact congrArg
      (fun datum : QualitativeData.SHEDatum package.preLedger.output.family =>
        datum.sharedContext)
      structuredSHE.sheArrowMatchesContext
  exact hcontainer.symm.trans
    (harrow.trans structuredSHE.context.sheDatum_sharedContext)

end IUTStage1Theorem311StructuredSHE

/--
Compatibility checklist between the strengthened SHE context and the common
container used for the final `HDD o SHE` route.

Every field is an equality or history-separation proof already forced by the
structured SHE input and the common-container record. This checklist does not
add a comparison endpoint or identify the two arithmetic histories.
-/
structure IUTStage1Theorem311StructuredSHECommonContainerCompatibility
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) : Prop where
  she_arrow_matches_context :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      structuredSHE.context.sheDatum
  she_datum_matches_certificate :
    structuredSHE.context.sheDatum = package.preLedger.certificate.she
  common_container_context_matches :
    package.preLedger.chartedContainer.commonContainer.context =
      structuredSHE.context.sharedContext
  q_pilot_in_codomain :
    structuredSHE.context.qPilotStructure.theater =
      structuredSHE.context.codomainStructure.theater
  theta_pilot_in_domain :
    structuredSHE.context.thetaPilotStructure.theater =
      structuredSHE.context.domainStructure.theater
  simultaneous_valid : structuredSHE.context.simultaneous_valid
  histories_not_identified :
    structuredSHE.context.domainStructure.theater.side ≠
      structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311StructuredSHECommonContainerCompatibility

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {structuredSHE : IUTStage1Theorem311StructuredSHE package}

theorem ofStructuredSHE
    (structuredSHE : IUTStage1Theorem311StructuredSHE package) :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package structuredSHE :=
  { she_arrow_matches_context := structuredSHE.sheArrowMatchesContext,
    she_datum_matches_certificate := structuredSHE.sheDatumMatchesCertificate,
    common_container_context_matches :=
      structuredSHE.commonContainerContextMatches,
    q_pilot_in_codomain := structuredSHE.context.qPilotTheater_eq_codomain,
    theta_pilot_in_domain := structuredSHE.context.thetaPilotTheater_eq_domain,
    simultaneous_valid := structuredSHE.context.simultaneousValid,
    histories_not_identified :=
      structuredSHE.domainHistory_ne_codomainHistory }

theorem sheArrowMatchesContext
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      structuredSHE.context.sheDatum :=
  compatibility.she_arrow_matches_context

theorem sheDatumMatchesCertificate
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    structuredSHE.context.sheDatum = package.preLedger.certificate.she :=
  compatibility.she_datum_matches_certificate

theorem commonContainerContextMatches
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    package.preLedger.chartedContainer.commonContainer.context =
      structuredSHE.context.sharedContext :=
  compatibility.common_container_context_matches

theorem qPilotTheater_eq_codomain
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    structuredSHE.context.qPilotStructure.theater =
      structuredSHE.context.codomainStructure.theater :=
  compatibility.q_pilot_in_codomain

theorem thetaPilotTheater_eq_domain
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    structuredSHE.context.thetaPilotStructure.theater =
      structuredSHE.context.domainStructure.theater :=
  compatibility.theta_pilot_in_domain

theorem simultaneousValid
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    structuredSHE.context.simultaneous_valid :=
  compatibility.simultaneous_valid

theorem domainHistory_ne_codomainHistory
    (compatibility :
      IUTStage1Theorem311StructuredSHECommonContainerCompatibility
        package structuredSHE) :
    structuredSHE.context.domainStructure.theater.side ≠
      structuredSHE.context.codomainStructure.theater.side :=
  compatibility.histories_not_identified

end IUTStage1Theorem311StructuredSHECommonContainerCompatibility

/--
Source-facing subclaims for the Theorem 3.11 algorithmic certificate used in
Stage 1.

This record separates the opaque algorithmic output certificate from the
Hodge-theater/SHE alignment datum needed to connect the common-container SHE
arrow to the structured certificate stored in the pre-ledger data.
-/
structure IUTStage1Theorem311Subclaims
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  algorithm_output_certified : package.preLedger.output.Certified
  hodge_theater_she_alignment :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she

namespace IUTStage1Theorem311Subclaims

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem algorithmOutputCertified
    (subclaims : IUTStage1Theorem311Subclaims package) :
    package.preLedger.output.Certified :=
  subclaims.algorithm_output_certified

def algorithmicOutput
    (subclaims : IUTStage1Theorem311Subclaims package) :
    IUTStage1Theorem311AlgorithmicOutput package :=
  { certified := subclaims.algorithmOutputCertified }

theorem hodgeTheaterSHEAlignment
    (subclaims : IUTStage1Theorem311Subclaims package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  subclaims.hodge_theater_she_alignment

def sheAlignment
    (subclaims : IUTStage1Theorem311Subclaims package) :
    IUTStage1Theorem311SHEAlignment package :=
  { alignment := subclaims.hodgeTheaterSHEAlignment }

def ofAlgorithmicOutputAndSHEAlignment
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package)
    (sheAlignment :
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        package.preLedger.certificate.she) :
    IUTStage1Theorem311Subclaims package :=
  { algorithm_output_certified :=
      algorithmicOutput.algorithmOutputCertified,
    hodge_theater_she_alignment := sheAlignment }

def ofComponents
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package)
    (sheAlignment : IUTStage1Theorem311SHEAlignment package) :
    IUTStage1Theorem311Subclaims package :=
  ofAlgorithmicOutputAndSHEAlignment
    algorithmicOutput sheAlignment.hodgeTheaterSHEAlignment

theorem algorithmicOutput_certified_eq
    (subclaims : IUTStage1Theorem311Subclaims package) :
    subclaims.algorithmicOutput.algorithmOutputCertified =
      subclaims.algorithmOutputCertified :=
  rfl

theorem sheAlignment_hodgeTheaterSHEAlignment_eq
    (subclaims : IUTStage1Theorem311Subclaims package) :
    subclaims.sheAlignment.hodgeTheaterSHEAlignment =
      subclaims.hodgeTheaterSHEAlignment :=
  rfl

theorem ofAlgorithmicOutputAndSHEAlignment_algorithmicOutput_eq
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package)
    (sheAlignment :
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        package.preLedger.certificate.she) :
    (ofAlgorithmicOutputAndSHEAlignment
      algorithmicOutput sheAlignment).algorithmicOutput =
      algorithmicOutput :=
  Subsingleton.elim _ _

theorem ofComponents_algorithmicOutput_eq
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package)
    (sheAlignment : IUTStage1Theorem311SHEAlignment package) :
    (ofComponents algorithmicOutput sheAlignment).algorithmicOutput =
      algorithmicOutput :=
  Subsingleton.elim _ _

theorem ofComponents_sheAlignment_eq
    (algorithmicOutput : IUTStage1Theorem311AlgorithmicOutput package)
    (sheAlignment : IUTStage1Theorem311SHEAlignment package) :
    (ofComponents algorithmicOutput sheAlignment).sheAlignment =
      sheAlignment :=
  Subsingleton.elim _ _

end IUTStage1Theorem311Subclaims

/--
Theorem 3.11 source inputs paired with the local pre-ledger audit.

The pre-ledger audit exposes structured IPL/SHE/APT data and chart/membership
facts. The subclaims record the separate opaque output certificate and SHE
alignment still needed for ledger promotion.
-/
structure IUTStage1Theorem311StructuredInputs
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  preledger_audit : IUTStage1PreLedgerData.Audit package.preLedger
  theorem311_subclaims : IUTStage1Theorem311Subclaims package

namespace IUTStage1Theorem311StructuredInputs

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem theorem311Subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    IUTStage1Theorem311Subclaims package :=
  inputs.theorem311_subclaims

theorem hasStructuredIPL
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  inputs.preledger_audit.has_structured_ipl

theorem hasStructuredSHE
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  inputs.preledger_audit.has_structured_she

theorem hasStructuredAPT
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    QualitativeData.HasStructuredAPT package.preLedger.output.family :=
  inputs.preledger_audit.has_structured_apt

theorem algorithmOutputCertified
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    package.preLedger.output.Certified :=
  inputs.theorem311_subclaims.algorithmOutputCertified

def algorithmicOutput
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    IUTStage1Theorem311AlgorithmicOutput package :=
  inputs.theorem311Subclaims.algorithmicOutput

theorem hodgeTheaterSHEAlignment
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  inputs.theorem311_subclaims.hodgeTheaterSHEAlignment

def sheAlignment
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    IUTStage1Theorem311SHEAlignment package :=
  inputs.theorem311Subclaims.sheAlignment

theorem algorithmOutputCertified_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    inputs.algorithmOutputCertified =
      inputs.theorem311Subclaims.algorithmOutputCertified :=
  rfl

theorem algorithmicOutput_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    inputs.algorithmicOutput =
      inputs.theorem311Subclaims.algorithmicOutput :=
  rfl

theorem hodgeTheaterSHEAlignment_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    inputs.hodgeTheaterSHEAlignment =
      inputs.theorem311Subclaims.hodgeTheaterSHEAlignment :=
  rfl

theorem sheAlignment_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    inputs.sheAlignment =
      inputs.theorem311Subclaims.sheAlignment :=
  rfl

theorem components_rebuild_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package) :
    IUTStage1Theorem311Subclaims.ofComponents
      inputs.algorithmicOutput inputs.sheAlignment =
      inputs.theorem311Subclaims :=
  Subsingleton.elim _ _

end IUTStage1Theorem311StructuredInputs

/--
Structured Theorem 3.11 inputs equipped with the strengthened SHE context.

This is a conservative extension of `IUTStage1Theorem311StructuredInputs`; it
adds strengthened SHE context without producing an endpoint.
-/
structure IUTStage1Theorem311StructuredInputsWithSHE
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  inputs : IUTStage1Theorem311StructuredInputs package
  structured_she : IUTStage1Theorem311StructuredSHE package

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem theorem311StructuredInputs
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311StructuredInputs package :=
  bundle.inputs

def structuredSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311StructuredSHE package :=
  bundle.structured_she

theorem hasStructuredIPL
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  bundle.inputs.hasStructuredIPL

theorem hasStructuredSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  bundle.inputs.hasStructuredSHE

theorem hasStructuredSHE_from_context
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  bundle.structuredSHE.hasStructuredSHE

theorem hasStructuredAPT
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    QualitativeData.HasStructuredAPT package.preLedger.output.family :=
  bundle.inputs.hasStructuredAPT

theorem algorithmOutputCertified
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.output.Certified :=
  bundle.inputs.algorithmOutputCertified

theorem hodgeTheaterSHEAlignment
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  bundle.inputs.hodgeTheaterSHEAlignment

theorem hodgeTheaterSHEAlignment_from_context
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  bundle.structuredSHE.hodgeTheaterSHEAlignment

theorem sheAlignment_eq_context_sheAlignment
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.inputs.sheAlignment =
      bundle.structuredSHE.sheAlignment :=
  Subsingleton.elim _ _

theorem domainHistory_ne_codomainHistory
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  bundle.structuredSHE.domainHistory_ne_codomainHistory

theorem commonContainerCompatibility
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE :=
  IUTStage1Theorem311StructuredSHECommonContainerCompatibility.ofStructuredSHE
    bundle.structuredSHE

theorem commonContainerContextMatches
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext :=
  bundle.structuredSHE.commonContainerContextMatches

def hodgeTheaterDescentBridgeData
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1HodgeTheaterDescentBridgeData :=
  { domainTheater := bundle.structuredSHE.context.domainStructure.theater,
    codomainTheater := bundle.structuredSHE.context.codomainStructure.theater,
    descent := package.preLedger.chartedContainer.commonContainer.hddShe.hdd.descent,
    zeroColumnCheckpoint := fourthTriangleHDDSHECheckpoint,
    indeterminacyProfile := package.indeterminacies,
    histories_not_identified := bundle.domainHistory_ne_codomainHistory }

theorem hodgeTheaterDescentBridgeData_domainTheater_eq
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.domainTheater =
      bundle.structuredSHE.context.domainStructure.theater :=
  rfl

theorem hodgeTheaterDescentBridgeData_codomainTheater_eq
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.codomainTheater =
      bundle.structuredSHE.context.codomainStructure.theater :=
  rfl

theorem hodgeTheaterDescentBridgeData_descent_eq
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.descent =
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.descent :=
  rfl

theorem hodgeTheaterDescentBridgeData_checkpoint_eq
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  rfl

theorem hodgeTheaterDescentBridgeData_indeterminacyProfile_eq
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.indeterminacyProfile =
      package.indeterminacies :=
  rfl

theorem hodgeTheaterDescentBridgeData_histories_not_identified
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    bundle.hodgeTheaterDescentBridgeData.domainTheater.side ≠
      bundle.hodgeTheaterDescentBridgeData.codomainTheater.side :=
  bundle.hodgeTheaterDescentBridgeData.histories_not_identified

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Source-facing Theorem 3.11 multiradial record.

IUT III describes Theorem 3.11 as producing a multiradial representation whose
theta-pilot side is read through mono-analytic log-shell containers, while the
q-pilot side is read through tautological log documentation.  This record
collects the current formal ingredients of that source statement: structured
IPL/SHE/APT input, coric common-container data, possible theta-pilot images,
the 0-column/1-column pilot distinction, and the Hodge-theater history guard.
-/
structure IUTStage1Theorem311MultiradialSourceRecord
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) where
  bundle : IUTStage1Theorem311StructuredInputsWithSHE package
  coricData : IUTStage1CoricData package
  thetaPossibleImages : IUTStage1ThetaPilotPossibleImages package
  thetaColumn : IUTStage1LogThetaVerticalColumn
  qColumn : IUTStage1LogThetaVerticalColumn
  theta_column_eq : thetaColumn = IUTStage1LogThetaVerticalColumn.zeroThetaPilot
  q_column_eq : qColumn = IUTStage1LogThetaVerticalColumn.oneQPilot
  hodgeHistoryGuard :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311MultiradialSourceRecord

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311MultiradialSourceRecord package :=
  { bundle := bundle,
    coricData := IUTStage1CoricData.ofPackage package,
    thetaPossibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package,
    thetaColumn := IUTStage1LogThetaVerticalColumn.zeroThetaPilot,
    qColumn := IUTStage1LogThetaVerticalColumn.oneQPilot,
    theta_column_eq := rfl,
    q_column_eq := rfl,
    hodgeHistoryGuard := bundle.domainHistory_ne_codomainHistory }

theorem hasStructuredIPL
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  record.bundle.hasStructuredIPL

theorem hasStructuredSHE
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  record.bundle.hasStructuredSHE

theorem hasStructuredAPT
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    QualitativeData.HasStructuredAPT package.preLedger.output.family :=
  record.bundle.hasStructuredAPT

theorem multiradialOutputMatchesPackage
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.coricData.multiradialOutput = package.multiradialOutput :=
  record.coricData.multiradialOutputMatchesPackage

theorem thetaImagesUnion_eq_targetUnion
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.thetaPossibleImages.union =
      package.preLedger.output.comparisons.targetUnion :=
  record.thetaPossibleImages.union_eq_targetUnion

theorem thetaColumn_hasMultiradiality
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.thetaColumn.hasPilotMultiradiality = true := by
  rw [record.theta_column_eq]
  exact IUTStage1LogThetaVerticalColumn.thetaPilot_hasMultiradiality

theorem qColumn_lacksMultiradiality
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.qColumn.hasPilotMultiradiality = false := by
  rw [record.q_column_eq]
  exact IUTStage1LogThetaVerticalColumn.qPilot_lacksMultiradiality

theorem thetaColumn_logShellTreatment
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.thetaColumn.logShellTreatment =
      IUTStage1LogShellColumnTreatment.monoAnalyticContainers := by
  rw [record.theta_column_eq]
  exact IUTStage1LogThetaVerticalColumn.thetaPilot_logShellTreatment

theorem qColumn_logShellTreatment
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.qColumn.logShellTreatment =
      IUTStage1LogShellColumnTreatment.tautologicalLogDocumentation := by
  rw [record.q_column_eq]
  exact IUTStage1LogThetaVerticalColumn.qPilot_logShellTreatment

theorem columnLogShellTreatments_distinct
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.thetaColumn.logShellTreatment ≠ record.qColumn.logShellTreatment := by
  rw [record.theta_column_eq, record.q_column_eq]
  exact IUTStage1LogThetaVerticalColumn.logShellTreatment_distinguishes_columns

theorem hodgeHistories_not_identified
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    record.bundle.structuredSHE.context.domainStructure.theater.side ≠
      record.bundle.structuredSHE.context.codomainStructure.theater.side :=
  record.hodgeHistoryGuard

theorem sourceRecord_endpoint
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family ∧
      QualitativeData.HasStructuredSHE package.preLedger.output.family ∧
      QualitativeData.HasStructuredAPT package.preLedger.output.family ∧
      record.coricData.multiradialOutput = package.multiradialOutput ∧
      record.thetaPossibleImages.union =
        package.preLedger.output.comparisons.targetUnion ∧
      record.thetaColumn.hasPilotMultiradiality = true ∧
      record.qColumn.hasPilotMultiradiality = false ∧
      record.thetaColumn.logShellTreatment ≠ record.qColumn.logShellTreatment ∧
      record.bundle.structuredSHE.context.domainStructure.theater.side ≠
        record.bundle.structuredSHE.context.codomainStructure.theater.side :=
  ⟨record.hasStructuredIPL,
    record.hasStructuredSHE,
    record.hasStructuredAPT,
    record.multiradialOutputMatchesPackage,
    record.thetaImagesUnion_eq_targetUnion,
    record.thetaColumn_hasMultiradiality,
    record.qColumn_lacksMultiradiality,
    record.columnLogShellTreatments_distinct,
    record.hodgeHistories_not_identified⟩

end IUTStage1Theorem311MultiradialSourceRecord

/--
Typed IPL/log-link transport layer for the Theorem 3.11 source record.

The paper treats the log-link/IPL passage as preserving the relevant log-volume
information while relating distinct Hodge-theater sides.  This record replaces
an undifferentiated `HasStructuredIPL` use by an explicit datum: the underlying
IPL prime-strip link, the domain/codomain theaters taken from the structured
Theorem 3.11 source record, the two real log-volume readings, the preservation
equality, and the no-history-identification guard.
-/
structure IUTStage1IPLLogVolumeTransport
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package) where
  iplDatum : QualitativeData.IPLDatum package.preLedger.output.family
  sourceTheater : QualitativeData.HodgeTheaterId
  targetTheater : QualitativeData.HodgeTheaterId
  source_theater_eq :
    sourceTheater =
      record.bundle.structuredSHE.context.domainStructure.theater
  target_theater_eq :
    targetTheater =
      record.bundle.structuredSHE.context.codomainStructure.theater
  link_source_eq_input :
    iplDatum.link.source = iplDatum.inputPrimeStrip
  link_target_eq_output :
    iplDatum.link.target = iplDatum.outputPrimeStrip
  sourceLogVolume : Real
  targetLogVolume : Real
  targetLogVolume_eq_sourceLogVolume :
    targetLogVolume = sourceLogVolume
  histories_not_identified :
    sourceTheater.side ≠ targetTheater.side

namespace IUTStage1IPLLogVolumeTransport

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}

def ofSourceRecord
    (iplDatum : QualitativeData.IPLDatum package.preLedger.output.family)
    (link_source_eq_input :
      iplDatum.link.source = iplDatum.inputPrimeStrip)
    (link_target_eq_output :
      iplDatum.link.target = iplDatum.outputPrimeStrip)
    (sourceLogVolume targetLogVolume : Real)
    (targetLogVolume_eq_sourceLogVolume :
      targetLogVolume = sourceLogVolume) :
    IUTStage1IPLLogVolumeTransport record :=
  { iplDatum := iplDatum,
    sourceTheater :=
      record.bundle.structuredSHE.context.domainStructure.theater,
    targetTheater :=
      record.bundle.structuredSHE.context.codomainStructure.theater,
    source_theater_eq := rfl,
    target_theater_eq := rfl,
    link_source_eq_input := link_source_eq_input,
    link_target_eq_output := link_target_eq_output,
    sourceLogVolume := sourceLogVolume,
    targetLogVolume := targetLogVolume,
    targetLogVolume_eq_sourceLogVolume :=
      targetLogVolume_eq_sourceLogVolume,
    histories_not_identified := record.hodgeHistories_not_identified }

theorem hasStructuredIPL
    (transport : IUTStage1IPLLogVolumeTransport record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  ⟨transport.iplDatum⟩

theorem sourceTheater_eq_domain
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.sourceTheater =
      record.bundle.structuredSHE.context.domainStructure.theater :=
  transport.source_theater_eq

theorem targetTheater_eq_codomain
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.targetTheater =
      record.bundle.structuredSHE.context.codomainStructure.theater :=
  transport.target_theater_eq

theorem targetLogVolume_preserved
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.targetLogVolume = transport.sourceLogVolume :=
  transport.targetLogVolume_eq_sourceLogVolume

theorem sourceLogVolume_eq_targetLogVolume
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.sourceLogVolume = transport.targetLogVolume :=
  transport.targetLogVolume_preserved.symm

theorem histories_not_identified'
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.sourceTheater.side ≠ transport.targetTheater.side :=
  transport.histories_not_identified

theorem linkSource_eq_datum_source
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.iplDatum.link.source = transport.iplDatum.inputPrimeStrip :=
  transport.link_source_eq_input

theorem linkTarget_eq_datum_target
    (transport : IUTStage1IPLLogVolumeTransport record) :
    transport.iplDatum.link.target = transport.iplDatum.outputPrimeStrip :=
  transport.link_target_eq_output

theorem transport_endpoint
    (transport : IUTStage1IPLLogVolumeTransport record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family ∧
      transport.sourceTheater =
        record.bundle.structuredSHE.context.domainStructure.theater ∧
      transport.targetTheater =
        record.bundle.structuredSHE.context.codomainStructure.theater ∧
      transport.iplDatum.link.source =
        transport.iplDatum.inputPrimeStrip ∧
      transport.iplDatum.link.target =
        transport.iplDatum.outputPrimeStrip ∧
      transport.targetLogVolume = transport.sourceLogVolume ∧
      transport.sourceTheater.side ≠ transport.targetTheater.side :=
  ⟨transport.hasStructuredIPL,
    transport.sourceTheater_eq_domain,
    transport.targetTheater_eq_codomain,
    transport.linkSource_eq_datum_source,
    transport.linkTarget_eq_datum_target,
    transport.targetLogVolume_preserved,
    transport.histories_not_identified'⟩

end IUTStage1IPLLogVolumeTransport

/--
Theorem 3.11 IPL link source read from the pre-ledger certificate.

This keeps the actual `IPLDatum` fixed to the certificate bundled in the
source package.  The remaining open content is only the two endpoint
identifications saying that the link source and target are the input and output
prime strips.
-/
structure IUTStage1Theorem311IPLLinkSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package) where
  link_source_eq_input :
    package.preLedger.certificate.ipl.link.source =
      package.preLedger.certificate.ipl.inputPrimeStrip
  link_target_eq_output :
    package.preLedger.certificate.ipl.link.target =
      package.preLedger.certificate.ipl.outputPrimeStrip

namespace IUTStage1Theorem311IPLLinkSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}

def iplDatum
    (_linkSource : IUTStage1Theorem311IPLLinkSource record) :
    QualitativeData.IPLDatum package.preLedger.output.family :=
  package.preLedger.certificate.ipl

theorem iplDatum_eq_preledger_certificate
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    linkSource.iplDatum = package.preLedger.certificate.ipl :=
  rfl

theorem hasStructuredIPL
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  ⟨linkSource.iplDatum⟩

theorem record_hasStructuredIPL
    (_linkSource : IUTStage1Theorem311IPLLinkSource record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  record.hasStructuredIPL

theorem linkSource_eq_input
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    linkSource.iplDatum.link.source =
      linkSource.iplDatum.inputPrimeStrip :=
  linkSource.link_source_eq_input

theorem linkTarget_eq_output
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    linkSource.iplDatum.link.target =
      linkSource.iplDatum.outputPrimeStrip :=
  linkSource.link_target_eq_output

theorem source_endpoint
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family ∧
      linkSource.iplDatum = package.preLedger.certificate.ipl ∧
      linkSource.iplDatum.link.source =
        linkSource.iplDatum.inputPrimeStrip ∧
      linkSource.iplDatum.link.target =
        linkSource.iplDatum.outputPrimeStrip :=
  ⟨linkSource.hasStructuredIPL,
    linkSource.iplDatum_eq_preledger_certificate,
    linkSource.linkSource_eq_input,
    linkSource.linkTarget_eq_output⟩

end IUTStage1Theorem311IPLLinkSource

/--
Theorem 3.11 IPL-link construction source aligned with the pre-ledger
certificate.

The construction itself builds the input-prime-strip link with the correct
source and target endpoints.  The only remaining certificate-facing obligation
is that the package's certified `IPLDatum` is the datum generated by this
construction.
-/
structure IUTStage1Theorem311IPLLinkConstructionSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package) where
  construction :
    QualitativeData.InputPrimeStripLinkConstruction
      package.preLedger.output.family
  certificate_ipl_eq :
    package.preLedger.certificate.ipl = construction.toIPLDatum

namespace IUTStage1Theorem311IPLLinkConstructionSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}

def constructedDatum
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    QualitativeData.IPLDatum package.preLedger.output.family :=
  constructionSource.construction.toIPLDatum

def iplDatum
    (_constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    QualitativeData.IPLDatum package.preLedger.output.family :=
  package.preLedger.certificate.ipl

theorem iplDatum_eq_constructedDatum
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    constructionSource.iplDatum =
      constructionSource.constructedDatum :=
  constructionSource.certificate_ipl_eq

theorem constructedDatum_eq_iplDatum
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    constructionSource.constructedDatum =
      constructionSource.iplDatum :=
  constructionSource.iplDatum_eq_constructedDatum.symm

theorem hasStructuredIPL
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family :=
  ⟨constructionSource.iplDatum⟩

theorem linkSource_eq_input
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    constructionSource.iplDatum.link.source =
      constructionSource.iplDatum.inputPrimeStrip := by
  rw [constructionSource.iplDatum_eq_constructedDatum]
  exact
    QualitativeData.InputPrimeStripLinkConstruction.toIPLDatum_link_source_eq_input
      constructionSource.construction

theorem linkTarget_eq_output
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    constructionSource.iplDatum.link.target =
      constructionSource.iplDatum.outputPrimeStrip := by
  rw [constructionSource.iplDatum_eq_constructedDatum]
  exact
    QualitativeData.InputPrimeStripLinkConstruction.toIPLDatum_link_target_eq_output
      constructionSource.construction

def toIPLLinkSource
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    IUTStage1Theorem311IPLLinkSource record :=
  { link_source_eq_input := constructionSource.linkSource_eq_input,
    link_target_eq_output := constructionSource.linkTarget_eq_output }

theorem toIPLLinkSource_iplDatum_eq_certificate
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    constructionSource.toIPLLinkSource.iplDatum =
      package.preLedger.certificate.ipl :=
  rfl

theorem construction_source_endpoint
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family ∧
      constructionSource.iplDatum =
        constructionSource.constructedDatum ∧
      constructionSource.toIPLLinkSource.iplDatum =
        package.preLedger.certificate.ipl ∧
      constructionSource.toIPLLinkSource.iplDatum.link.source =
        constructionSource.toIPLLinkSource.iplDatum.inputPrimeStrip ∧
      constructionSource.toIPLLinkSource.iplDatum.link.target =
        constructionSource.toIPLLinkSource.iplDatum.outputPrimeStrip :=
  ⟨constructionSource.hasStructuredIPL,
    constructionSource.iplDatum_eq_constructedDatum,
    constructionSource.toIPLLinkSource_iplDatum_eq_certificate,
    constructionSource.toIPLLinkSource.linkSource_eq_input,
    constructionSource.toIPLLinkSource.linkTarget_eq_output⟩

end IUTStage1Theorem311IPLLinkConstructionSource

/--
Route-level wrapper for square-weighted full-label transport preservation.

The underlying preservation audit from
`IUTStage1ZModSquareWeightedFullLabelTransportAudit` already states the
coordinate, square-weight, and full-label-log-volume preservation obligations.
This wrapper additionally requires that its Hodge-theater/descent bridge is the
one extracted from the structured-SHE Theorem 3.11 route.
-/
structure IUTStage1StructuredSHESquareWeightTransportAudit
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (l : PrimeGeFive) where
  preservation_audit :
    IUTStage1ZModSquareWeightedFullLabelTransportAudit l
  bridge_eq_structured_she :
    preservation_audit.bridge = bundle.hodgeTheaterDescentBridgeData

namespace IUTStage1StructuredSHESquareWeightTransportAudit

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {l : PrimeGeFive}

def preservationAudit
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    IUTStage1ZModSquareWeightedFullLabelTransportAudit l :=
  audit.preservation_audit

theorem bridge_eq_structuredSHE
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.bridge = bundle.hodgeTheaterDescentBridgeData :=
  audit.bridge_eq_structured_she

theorem bridge_domainTheater_eq
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.bridge.domainTheater =
      bundle.structuredSHE.context.domainStructure.theater := by
  rw [audit.bridge_eq_structuredSHE]
  rfl

theorem bridge_codomainTheater_eq
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.bridge.codomainTheater =
      bundle.structuredSHE.context.codomainStructure.theater := by
  rw [audit.bridge_eq_structuredSHE]
  rfl

theorem bridge_descent_eq
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.bridge.descent =
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.descent := by
  rw [audit.bridge_eq_structuredSHE]
  rfl

theorem targetTransportedSummand_eq_sourceSummand
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l)
    (j : ZMod l.value) :
    audit.preservationAudit.targetProfile.weight
          (audit.preservationAudit.coordinateEquiv j) *
        audit.preservationAudit.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (audit.preservationAudit.coordinateEquiv j)) =
      audit.preservationAudit.sourceProfile.weight j *
        audit.preservationAudit.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  audit.preservationAudit.targetTransportedSummand_eq_sourceSummand j

theorem targetTransportedAverage_eq_sourceAverage
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.targetTransportedAverage =
      audit.preservationAudit.sourceAverage :=
  audit.preservationAudit.targetTransportedAverage_eq_sourceAverage

theorem sourceAverage_le_of_forall_targetFullLabel_le
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l)
    {c : Real}
    (hpointwise :
      ∀ j : ZMod l.value,
        audit.preservationAudit.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (audit.preservationAudit.coordinateEquiv j)) <= c) :
    audit.preservationAudit.sourceAverage <= c :=
  audit.preservationAudit.sourceAverage_le_of_forall_targetFullLabel_le
    hpointwise

theorem histories_not_identified
    (audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    audit.preservationAudit.bridge.domainTheater.side ≠
      audit.preservationAudit.bridge.codomainTheater.side :=
  audit.preservationAudit.histories_not_identified

theorem structuredSHE_histories_not_identified
    (_audit :
      IUTStage1StructuredSHESquareWeightTransportAudit package bundle l) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  bundle.domainHistory_ne_codomainHistory

end IUTStage1StructuredSHESquareWeightTransportAudit

/--
Explicit open obligations for constructing the structured-SHE square-weight
transport audit.

The structured-SHE bundle supplies the Hodge-theater/descent bridge.  The fields
below are exactly the additional square-weight/full-label data still needed to
turn that bridge into a preservation audit.
-/
structure IUTStage1StructuredSHESquareWeightTransportObligations
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  sourceProfile : IUTStage1ZModSquareWeightProfile l
  targetProfile : IUTStage1ZModSquareWeightProfile l
  sourceLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  targetLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  fullLabelLogVolume_preserved :
    ∀ j : ZMod l.value,
      targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)
  squareWeight_preserved :
    ∀ j : ZMod l.value,
      targetProfile.weight (coordinateEquiv j) =
        sourceProfile.weight j
  weightTotal_preserved :
    targetProfile.weightTotal = sourceProfile.weightTotal

namespace IUTStage1StructuredSHESquareWeightTransportObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {l : PrimeGeFive}

def suppliedBridge
    (_obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    IUTStage1HodgeTheaterDescentBridgeData :=
  bundle.hodgeTheaterDescentBridgeData

theorem suppliedBridge_histories_not_identified
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    obligations.suppliedBridge.domainTheater.side ≠
      obligations.suppliedBridge.codomainTheater.side :=
  bundle.hodgeTheaterDescentBridgeData_histories_not_identified

def toPreservationAudit
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    IUTStage1ZModSquareWeightedFullLabelTransportAudit l :=
  { bridge := obligations.suppliedBridge,
    coordinateEquiv := obligations.coordinateEquiv,
    sourceProfile := obligations.sourceProfile,
    targetProfile := obligations.targetProfile,
    sourceLogVolume := obligations.sourceLogVolume,
    targetLogVolume := obligations.targetLogVolume,
    fullLabelLogVolume_preserved := obligations.fullLabelLogVolume_preserved,
    squareWeight_preserved := obligations.squareWeight_preserved,
    weightTotal_preserved := obligations.weightTotal_preserved }

def toStructuredSHESquareWeightTransportAudit
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    IUTStage1StructuredSHESquareWeightTransportAudit package bundle l :=
  { preservation_audit := obligations.toPreservationAudit,
    bridge_eq_structured_she := rfl }

theorem toPreservationAudit_bridge_eq_structuredSHE
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    obligations.toPreservationAudit.bridge =
      bundle.hodgeTheaterDescentBridgeData :=
  rfl

theorem toStructuredSHESquareWeightTransportAudit_average_eq
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    let audit := obligations.toStructuredSHESquareWeightTransportAudit
    audit.preservationAudit.targetTransportedAverage =
      audit.preservationAudit.sourceAverage :=
  (obligations.toStructuredSHESquareWeightTransportAudit).targetTransportedAverage_eq_sourceAverage

theorem toStructuredSHESquareWeightTransportAudit_descent_eq
    (obligations :
      IUTStage1StructuredSHESquareWeightTransportObligations package bundle l) :
    let audit := obligations.toStructuredSHESquareWeightTransportAudit
    audit.preservationAudit.bridge.descent =
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.descent :=
  (obligations.toStructuredSHESquareWeightTransportAudit).bridge_descent_eq

end IUTStage1StructuredSHESquareWeightTransportObligations

/--
Reduced structured-SHE square-weight obligations.

Instead of asking separately for pointwise square-weight preservation and
total-weight preservation, this record asks for the coordinate equivalence to
preserve the canonical real square profile.  The two weight-preservation fields
of `IUTStage1StructuredSHESquareWeightTransportObligations` are then derived by
the `IUTStage1ZModSquareWeightProfile` lemmas.
-/
structure IUTStage1StructuredSHECoordinateSquareWeightObligations
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  sourceProfile : IUTStage1ZModSquareWeightProfile l
  targetProfile : IUTStage1ZModSquareWeightProfile l
  sourceLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  targetLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  coordinateSquare_preserved :
    IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
      (l := l) coordinateEquiv
  fullLabelLogVolume_preserved :
    ∀ j : ZMod l.value,
      targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

namespace IUTStage1StructuredSHECoordinateSquareWeightObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {l : PrimeGeFive}

theorem squareWeight_preserved
    (obligations :
      IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l) :
    ∀ j : ZMod l.value,
      obligations.targetProfile.weight (obligations.coordinateEquiv j) =
        obligations.sourceProfile.weight j :=
  IUTStage1ZModSquareWeightProfile.squareWeight_preserved_of_coordinateSquarePreserving
    obligations.sourceProfile obligations.targetProfile
    obligations.coordinateSquare_preserved

theorem weightTotal_preserved
    (obligations :
      IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l) :
    obligations.targetProfile.weightTotal =
      obligations.sourceProfile.weightTotal :=
  IUTStage1ZModSquareWeightProfile.weightTotal_preserved_of_coordinateSquarePreserving
    obligations.sourceProfile obligations.targetProfile
    obligations.coordinateSquare_preserved

def toStructuredSHESquareWeightTransportObligations
    (obligations :
      IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l) :
    IUTStage1StructuredSHESquareWeightTransportObligations package bundle l :=
  { coordinateEquiv := obligations.coordinateEquiv,
    sourceProfile := obligations.sourceProfile,
    targetProfile := obligations.targetProfile,
    sourceLogVolume := obligations.sourceLogVolume,
    targetLogVolume := obligations.targetLogVolume,
    fullLabelLogVolume_preserved :=
      obligations.fullLabelLogVolume_preserved,
    squareWeight_preserved := obligations.squareWeight_preserved,
    weightTotal_preserved := obligations.weightTotal_preserved }

theorem toStructuredSHESquareWeightTransportObligations_average_eq
    (obligations :
      IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l) :
    let transportObligations :=
      obligations.toStructuredSHESquareWeightTransportObligations
    let audit := transportObligations.toStructuredSHESquareWeightTransportAudit
    audit.preservationAudit.targetTransportedAverage =
      audit.preservationAudit.sourceAverage := by
  let full := obligations.toStructuredSHESquareWeightTransportObligations
  change
    full.toStructuredSHESquareWeightTransportAudit.preservationAudit.targetTransportedAverage =
      full.toStructuredSHESquareWeightTransportAudit.preservationAudit.sourceAverage
  exact full.toStructuredSHESquareWeightTransportAudit_average_eq

theorem toStructuredSHESquareWeightTransportObligations_bridge_eq
    (obligations :
      IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l) :
    let transportObligations :=
      obligations.toStructuredSHESquareWeightTransportObligations
    transportObligations.toPreservationAudit.bridge =
      bundle.hodgeTheaterDescentBridgeData := by
  let full := obligations.toStructuredSHESquareWeightTransportObligations
  change full.toPreservationAudit.bridge = bundle.hodgeTheaterDescentBridgeData
  exact full.toPreservationAudit_bridge_eq_structuredSHE

end IUTStage1StructuredSHECoordinateSquareWeightObligations

/--
Fully factored structured-SHE obligations for the square-weighted full-label
transport corridor.

This record asks for the two primitive preservation branches separately:

* coordinate-square preservation for the `j^2` weights;
* full-label map preservation plus value preservation for the log-volume branch.

The structured-SHE square-weight obligation records are derived from these
fields.
-/
structure IUTStage1StructuredSHEFactoredSquareFullLabelObligations
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (l : PrimeGeFive) where
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  sourceProfile : IUTStage1ZModSquareWeightProfile l
  targetProfile : IUTStage1ZModSquareWeightProfile l
  sourceLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  targetLogVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l
  coordinateSquare_preserved :
    IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
      (l := l) coordinateEquiv
  fullLabelMap_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
      (l := l) coordinateEquiv
  fullLabelValue_preserved :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
      sourceLogVolume targetLogVolume

namespace IUTStage1StructuredSHEFactoredSquareFullLabelObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {l : PrimeGeFive}

open IUTStage1ZModSquareWeightProfile

def comparisonLevel
    (_obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.pointwiseRepresentative

theorem comparisonLevel_eq_pointwiseRepresentative
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.comparisonLevel =
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  rfl

theorem comparisonLevel_ne_balancedSignCompatible
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.balancedSignCompatible :=
  IUTStage1SquareComparisonLevel.pointwise_ne_balanced

theorem fullLabelLogVolume_preserved
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    ∀ j : ZMod l.value,
      obligations.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (obligations.coordinateEquiv j)) =
        obligations.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  rw [obligations.fullLabelMap_preserved j]
  exact obligations.fullLabelValue_preserved
    (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

noncomputable def fromGaussianDegreeEvaluations
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (hcoord :
      IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
        (l := l) coordinateEquiv)
    (hmap :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) coordinateEquiv)
    (henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree) :
    IUTStage1StructuredSHEFactoredSquareFullLabelObligations
      package bundle l :=
  { coordinateEquiv := coordinateEquiv,
    sourceProfile := sourceProfile,
    targetProfile := targetProfile,
    sourceLogVolume :=
      sourceEvaluation.toCuspLabelLogVolumeCompatibility,
    targetLogVolume :=
      targetEvaluation.toCuspLabelLogVolumeCompatibility,
    coordinateSquare_preserved := hcoord,
    fullLabelMap_preserved := hmap,
    fullLabelValue_preserved :=
      sourceEvaluation.fullLabelLogVolumeValuePreserving_of_environmentDegree_eq
        targetEvaluation henv }

theorem fromGaussianDegreeEvaluations_targetLogVolume_fullLabel
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (hcoord :
      IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
        (l := l) coordinateEquiv)
    (hmap :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) coordinateEquiv)
    (henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree)
    (label : IUTStage1ZModCuspFullLabel l) :
    (fromGaussianDegreeEvaluations
        (package := package) (bundle := bundle)
        coordinateEquiv sourceProfile targetProfile
        sourceEvaluation targetEvaluation hcoord hmap henv).targetLogVolume.fullLabelLogVolume
        label =
      targetEvaluation.gaussianDegree label :=
  targetEvaluation.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume label

noncomputable def fromHodgeArakelovThetaValueEvaluations
    {F : Type v} [Field F] {X C : HyperbolicOrbicurveModel F}
    (sourceHA targetHA :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (canonicalOneDegree_preserved :
      targetHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    IUTStage1StructuredSHEFactoredSquareFullLabelObligations
      package bundle l :=
  fromGaussianDegreeEvaluations
    (package := package) (bundle := bundle)
    (Equiv.refl (ZMod l.value))
    (IUTStage1ZModSquareWeightProfile.canonicalSquareWeights l)
    (IUTStage1ZModSquareWeightProfile.canonicalSquareWeights l)
    sourceHA.toGaussianMonoidDegreeEvaluation
    targetHA.toGaussianMonoidDegreeEvaluation
    IUTStage1ZModSquareWeightProfile.coordinateSquarePreserving_refl
    IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_refl
    (sourceHA.environmentDegree_eq_of_canonicalOneDegree_eq
      targetHA canonicalOneDegree_preserved)

theorem fromHodgeArakelovThetaValueEvaluations_endpoint
    {F : Type v} [Field F] {X C : HyperbolicOrbicurveModel F}
    (sourceHA targetHA :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (canonicalOneDegree_preserved :
      targetHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    let obligations :=
      fromHodgeArakelovThetaValueEvaluations
        (package := package) (bundle := bundle)
        sourceHA targetHA canonicalOneDegree_preserved;
    sourceHA.thetaRootSource.canonicalFullLabel ≠
        IUTStage1ZModCuspFullLabel.zero ∧
      targetHA.thetaRootSource.canonicalFullLabel ≠
        IUTStage1ZModCuspFullLabel.zero ∧
      obligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      (∀ j : ZMod l.value,
        obligations.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          obligations.sourceLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) :=
  by
    intro obligations
    exact
      ⟨sourceHA.canonicalThetaRootLabel_ne_zero,
        targetHA.canonicalThetaRootLabel_ne_zero,
        obligations.comparisonLevel_eq_pointwiseRepresentative,
        by
          intro j
          simpa using obligations.fullLabelLogVolume_preserved j⟩

def toCoordinateSquareWeightObligations
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    IUTStage1StructuredSHECoordinateSquareWeightObligations package bundle l :=
  { coordinateEquiv := obligations.coordinateEquiv,
    sourceProfile := obligations.sourceProfile,
    targetProfile := obligations.targetProfile,
    sourceLogVolume := obligations.sourceLogVolume,
    targetLogVolume := obligations.targetLogVolume,
    coordinateSquare_preserved := obligations.coordinateSquare_preserved,
    fullLabelLogVolume_preserved :=
      obligations.fullLabelLogVolume_preserved }

def toStructuredSHESquareWeightTransportObligations
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    IUTStage1StructuredSHESquareWeightTransportObligations package bundle l := by
  let reduced := obligations.toCoordinateSquareWeightObligations
  exact reduced.toStructuredSHESquareWeightTransportObligations

def toStructuredSHESquareWeightTransportAudit
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    IUTStage1StructuredSHESquareWeightTransportAudit package bundle l := by
  let full := obligations.toStructuredSHESquareWeightTransportObligations
  exact full.toStructuredSHESquareWeightTransportAudit

theorem transportedAverage_eq
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    let audit := obligations.toStructuredSHESquareWeightTransportAudit
    audit.preservationAudit.targetTransportedAverage =
      audit.preservationAudit.sourceAverage := by
  let reduced := obligations.toCoordinateSquareWeightObligations
  let full := reduced.toStructuredSHESquareWeightTransportObligations
  let audit := full.toStructuredSHESquareWeightTransportAudit
  change
    audit.preservationAudit.targetTransportedAverage =
      audit.preservationAudit.sourceAverage
  exact reduced.toStructuredSHESquareWeightTransportObligations_average_eq

theorem bridge_eq_structuredSHE
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.toStructuredSHESquareWeightTransportAudit.preservationAudit.bridge =
      bundle.hodgeTheaterDescentBridgeData :=
  obligations.toStructuredSHESquareWeightTransportAudit.bridge_eq_structuredSHE

/--
Gaussian-to-factored-SHE preservation endpoint.

If the source and target Gaussian evaluations have the same environment degree,
then the constructed factored square/full-label obligations supply the
full-label value preservation branch, the structured-SHE transported average
equality, the pointwise representative comparison level, and the retained
distinction of Hodge-theater histories.
-/
theorem fromGaussianDegreeEvaluations_endpoint
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (hcoord :
      IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
        (l := l) coordinateEquiv)
    (hmap :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) coordinateEquiv)
    (henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree) :
    let obligations :=
      fromGaussianDegreeEvaluations
        (package := package) (bundle := bundle)
        coordinateEquiv sourceProfile targetProfile
        sourceEvaluation targetEvaluation hcoord hmap henv;
    let transportAudit := obligations.toStructuredSHESquareWeightTransportAudit;
    obligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      (∀ j : ZMod l.value,
        obligations.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (obligations.coordinateEquiv j)) =
          obligations.sourceLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      transportAudit.preservationAudit.targetTransportedAverage =
        transportAudit.preservationAudit.sourceAverage ∧
      obligations.coordinateEquiv = Equiv.refl (ZMod l.value) ∧
      bundle.structuredSHE.context.domainStructure.theater.side ≠
        bundle.structuredSHE.context.codomainStructure.theater.side := by
  intro obligations transportAudit
  exact
    ⟨obligations.comparisonLevel_eq_pointwiseRepresentative,
      obligations.fullLabelLogVolume_preserved,
      obligations.transportedAverage_eq,
      IUTStage1ZModSquareWeightProfile.coordinateSquarePreserving_eq_refl
        obligations.coordinateSquare_preserved,
      bundle.domainHistory_ne_codomainHistory⟩

theorem representativeSummand_constant_one_preserved
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    ∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant (l := l)
            (1 : Real))
          (obligations.coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant (l := l)
            (1 : Real))
          j :=
  representativeSummand_constant_one_preserved_of_coordinateSquarePreserving
    obligations.coordinateSquare_preserved

theorem representativeSummand_constant_one_preserved_iff_coordinateSquare
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    (∀ j : ZMod l.value,
      IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant (l := l)
            (1 : Real))
          (obligations.coordinateEquiv j) =
        IUTStage1ZModSquareWeightProfile.representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant (l := l)
            (1 : Real))
          j) ↔
      IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
        (l := l) obligations.coordinateEquiv :=
  representativeSummand_constant_one_preserved_iff_coordinateSquarePreserving
    obligations.coordinateEquiv

theorem coordinateEquiv_apply_eq
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    ∀ j : ZMod l.value, obligations.coordinateEquiv j = j :=
  coordinateSquarePreserving_apply_eq obligations.coordinateSquare_preserved

theorem coordinateEquiv_eq_refl
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.coordinateEquiv = Equiv.refl (ZMod l.value) :=
  coordinateSquarePreserving_eq_refl obligations.coordinateSquare_preserved

theorem coordinateIdentity_and_histories_not_identified
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.coordinateEquiv = Equiv.refl (ZMod l.value) ∧
      bundle.structuredSHE.context.domainStructure.theater.side ≠
        bundle.structuredSHE.context.codomainStructure.theater.side :=
  ⟨obligations.coordinateEquiv_eq_refl,
    bundle.domainHistory_ne_codomainHistory⟩

set_option linter.style.longLine false in
/--
Factored SHE preservation derived from Hodge--Arakelov theta evaluations.

This is the constructor-level audit for the finite SHE step: from the
source/target Hodge--Arakelov theta-value evaluations and canonical one-label
degree preservation, the factored square/full-label obligations supply
identity coordinate transport, coordinate-square preservation, full-label map
and value preservation, transported-average preservation, and the retained
separation of the two Hodge-theater histories.
-/
theorem fromHodgeArakelovThetaValueEvaluations_factoredSHE_endpoint
    {F : Type v} [Field F] {X C : HyperbolicOrbicurveModel F}
    (sourceHA targetHA :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (canonicalOneDegree_preserved :
      targetHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    let obligations :=
      fromHodgeArakelovThetaValueEvaluations
        (package := package) (bundle := bundle)
        sourceHA targetHA canonicalOneDegree_preserved;
    let transportAudit := obligations.toStructuredSHESquareWeightTransportAudit;
    obligations.coordinateEquiv = Equiv.refl (ZMod l.value) ∧
      IUTStage1ZModSquareWeightProfile.CoordinateSquarePreserving
        (l := l) obligations.coordinateEquiv ∧
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) obligations.coordinateEquiv ∧
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
        obligations.sourceLogVolume obligations.targetLogVolume ∧
      (∀ j : ZMod l.value,
        obligations.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (obligations.coordinateEquiv j)) =
          obligations.sourceLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      transportAudit.preservationAudit.targetTransportedAverage =
        transportAudit.preservationAudit.sourceAverage ∧
      bundle.structuredSHE.context.domainStructure.theater.side ≠
        bundle.structuredSHE.context.codomainStructure.theater.side := by
  intro obligations transportAudit
  exact
    ⟨obligations.coordinateEquiv_eq_refl,
      obligations.coordinateSquare_preserved,
      obligations.fullLabelMap_preserved,
      obligations.fullLabelValue_preserved,
      obligations.fullLabelLogVolume_preserved,
      obligations.transportedAverage_eq,
      bundle.domainHistory_ne_codomainHistory⟩

theorem coordinateEquiv_ne_neg
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.coordinateEquiv ≠ Equiv.neg (ZMod l.value) := by
  intro hneg
  have hcoord := obligations.coordinateSquare_preserved
  rw [hneg] at hcoord
  exact not_coordinateSquarePreserving_neg hcoord

theorem coordinateEquiv_ne_modularSquareOnlyNeg
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    obligations.coordinateEquiv ≠
      (IUTStage1FullLabelModularSquareOnlyTransport.neg l).coordinateEquiv := by
  simpa [IUTStage1FullLabelModularSquareOnlyTransport.neg] using
    obligations.coordinateEquiv_ne_neg

theorem coordinateEquiv_ne_balancedNegSelf
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l)
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    obligations.coordinateEquiv ≠
      (IUTStage1BalancedSquareFullLabelTransport.negSelf logVolume).coordinateEquiv := by
  simpa [IUTStage1BalancedSquareFullLabelTransport.negSelf] using
    obligations.coordinateEquiv_ne_neg

end IUTStage1StructuredSHEFactoredSquareFullLabelObligations

/--
Source-facing SHE synchronization package for the Theorem 3.11 route.

The paper-side SHE role is that the output construction is executable relative
to the arithmetic holomorphic structure in the 1-column.  At the current Stage 1
level, the available semantic source is Hodge--Arakelov theta-value data:
equality of the canonical one-label degree synchronizes the Gaussian
environment degrees, which then constructs the factored square/full-label
preservation package used by the route.
-/
structure IUTStage1SHESynchronizationSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  sourceHA :
    IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
      l X C
  targetHA :
    IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
      l X C
  canonicalOneDegree_preserved :
    targetHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))

namespace IUTStage1SHESynchronizationSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

noncomputable def ofThetaEvaluationSources
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    IUTStage1SHESynchronizationSource record l X C :=
  { sourceHA := sourceEvaluation.valueSource,
    targetHA := targetEvaluation.valueSource,
    canonicalOneDegree_preserved := canonicalOneDegree_preserved }

noncomputable def toFactoredObligations
    (sync : IUTStage1SHESynchronizationSource record l X C) :
  IUTStage1StructuredSHEFactoredSquareFullLabelObligations
      package record.bundle l :=
  IUTStage1StructuredSHEFactoredSquareFullLabelObligations.fromHodgeArakelovThetaValueEvaluations
    (package := package) (bundle := record.bundle)
    sync.sourceHA sync.targetHA sync.canonicalOneDegree_preserved

noncomputable def toStructuredSHESquareWeightTransportAudit
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    IUTStage1StructuredSHESquareWeightTransportAudit
      package record.bundle l :=
  sync.toFactoredObligations.toStructuredSHESquareWeightTransportAudit

theorem hasStructuredSHE
    (_sync : IUTStage1SHESynchronizationSource record l X C) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  IUTStage1Theorem311MultiradialSourceRecord.hasStructuredSHE record

theorem coordinateEquiv_eq_refl
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    sync.toFactoredObligations.coordinateEquiv =
      Equiv.refl (ZMod l.value) :=
  sync.toFactoredObligations.coordinateEquiv_eq_refl

theorem comparisonLevel_eq_pointwiseRepresentative
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    sync.toFactoredObligations.comparisonLevel =
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  sync.toFactoredObligations.comparisonLevel_eq_pointwiseRepresentative

theorem fullLabelLogVolume_preserved
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    ∀ j : ZMod l.value,
      sync.toFactoredObligations.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (sync.toFactoredObligations.coordinateEquiv j)) =
        sync.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  sync.toFactoredObligations.fullLabelLogVolume_preserved

theorem transportedAverage_eq
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.targetTransportedAverage =
      sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.sourceAverage :=
  sync.toFactoredObligations.transportedAverage_eq

theorem histories_not_identified
    (_sync : IUTStage1SHESynchronizationSource record l X C) :
    record.bundle.structuredSHE.context.domainStructure.theater.side ≠
      record.bundle.structuredSHE.context.codomainStructure.theater.side :=
  record.hodgeHistories_not_identified

theorem sourceThetaRootLabel_ne_zero
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    sync.sourceHA.thetaRootSource.canonicalFullLabel ≠
      IUTStage1ZModCuspFullLabel.zero :=
  sync.sourceHA.canonicalThetaRootLabel_ne_zero

theorem targetThetaRootLabel_ne_zero
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    sync.targetHA.thetaRootSource.canonicalFullLabel ≠
      IUTStage1ZModCuspFullLabel.zero :=
  sync.targetHA.canonicalThetaRootLabel_ne_zero

theorem synchronization_endpoint
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family ∧
      sync.toFactoredObligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      sync.toFactoredObligations.coordinateEquiv =
        Equiv.refl (ZMod l.value) ∧
      (∀ j : ZMod l.value,
        sync.toFactoredObligations.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (sync.toFactoredObligations.coordinateEquiv j)) =
          sync.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.targetTransportedAverage =
        sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.sourceAverage ∧
      record.bundle.structuredSHE.context.domainStructure.theater.side ≠
        record.bundle.structuredSHE.context.codomainStructure.theater.side :=
  ⟨sync.hasStructuredSHE,
    sync.comparisonLevel_eq_pointwiseRepresentative,
    sync.coordinateEquiv_eq_refl,
    sync.fullLabelLogVolume_preserved,
    sync.transportedAverage_eq,
    sync.histories_not_identified⟩

theorem ofThetaEvaluationSources_endpoint
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    let sync :=
      ofThetaEvaluationSources
        (record := record)
        sourceEvaluation targetEvaluation canonicalOneDegree_preserved;
    sync.sourceHA = sourceEvaluation.valueSource ∧
      sync.targetHA = targetEvaluation.valueSource ∧
      sourceEvaluation.thetaRootSource.canonicalFullLabel =
        IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value) ∧
      targetEvaluation.thetaRootSource.canonicalFullLabel =
        IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value) ∧
      QualitativeData.HasStructuredSHE package.preLedger.output.family ∧
      sync.toFactoredObligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      sync.toFactoredObligations.coordinateEquiv =
        Equiv.refl (ZMod l.value) ∧
      sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.targetTransportedAverage =
        sync.toStructuredSHESquareWeightTransportAudit.preservationAudit.sourceAverage ∧
      record.bundle.structuredSHE.context.domainStructure.theater.side ≠
        record.bundle.structuredSHE.context.codomainStructure.theater.side := by
  intro sync
  exact
    ⟨rfl,
      rfl,
      sourceEvaluation.canonicalFullLabel_eq_one,
      targetEvaluation.canonicalFullLabel_eq_one,
      sync.hasStructuredSHE,
      sync.comparisonLevel_eq_pointwiseRepresentative,
      sync.coordinateEquiv_eq_refl,
      sync.transportedAverage_eq,
      sync.histories_not_identified⟩

end IUTStage1SHESynchronizationSource

/--
Finite Hodge/SHE transport object for the current Stage 1 corridor.

This packages the finite Hodge--Arakelov shadow of simultaneous holomorphic
expressibility as transport data: the two Hodge-theater sides, the finite label
map, full-label log-volume preservation, transported-average preservation, and
the no-history-identification guard.  It is constructed from the current
Hodge--Arakelov synchronization source, but downstream bridge code can consume
this transport object instead of reaching directly into the synchronization
record.
-/
structure IUTStage1FiniteHodgeSHETransport
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  synchronization : IUTStage1SHESynchronizationSource record l X C
  sourceTheater : QualitativeData.HodgeTheaterId
  targetTheater : QualitativeData.HodgeTheaterId
  source_theater_eq :
    sourceTheater =
      record.bundle.structuredSHE.context.domainStructure.theater
  target_theater_eq :
    targetTheater =
      record.bundle.structuredSHE.context.codomainStructure.theater
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  coordinate_equiv_eq :
    coordinateEquiv =
      synchronization.toFactoredObligations.coordinateEquiv
  fullLabelLogVolume_preserved :
    ∀ j : ZMod l.value,
      synchronization.toFactoredObligations.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (coordinateEquiv j)) =
        synchronization.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)
  transportedAverage_preserved :
    let audit :=
      synchronization.toStructuredSHESquareWeightTransportAudit.preservationAudit
    audit.targetTransportedAverage = audit.sourceAverage
  histories_not_identified :
    sourceTheater.side ≠ targetTheater.side

namespace IUTStage1FiniteHodgeSHETransport

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

noncomputable def ofSynchronization
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    IUTStage1FiniteHodgeSHETransport record l X C :=
  { synchronization := sync,
    sourceTheater :=
      record.bundle.structuredSHE.context.domainStructure.theater,
    targetTheater :=
      record.bundle.structuredSHE.context.codomainStructure.theater,
    source_theater_eq := rfl,
    target_theater_eq := rfl,
    coordinateEquiv := sync.toFactoredObligations.coordinateEquiv,
    coordinate_equiv_eq := rfl,
    fullLabelLogVolume_preserved := sync.fullLabelLogVolume_preserved,
    transportedAverage_preserved := sync.transportedAverage_eq,
    histories_not_identified := record.hodgeHistories_not_identified }

def toSHESynchronizationSource
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    IUTStage1SHESynchronizationSource record l X C :=
  transport.synchronization

noncomputable def toFactoredObligations
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    IUTStage1StructuredSHEFactoredSquareFullLabelObligations
      package record.bundle l :=
  transport.synchronization.toFactoredObligations

theorem hasStructuredSHE
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family :=
  transport.synchronization.hasStructuredSHE

theorem sourceTheater_eq_domain
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    transport.sourceTheater =
      record.bundle.structuredSHE.context.domainStructure.theater :=
  transport.source_theater_eq

theorem targetTheater_eq_codomain
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    transport.targetTheater =
      record.bundle.structuredSHE.context.codomainStructure.theater :=
  transport.target_theater_eq

theorem coordinateEquiv_eq_factored
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    transport.coordinateEquiv =
      transport.toFactoredObligations.coordinateEquiv :=
  transport.coordinate_equiv_eq

theorem fullLabelLogVolume_preserved'
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    ∀ j : ZMod l.value,
      transport.toFactoredObligations.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (transport.coordinateEquiv j)) =
        transport.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  transport.fullLabelLogVolume_preserved

theorem transportedAverage_preserved'
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    let audit :=
      transport.synchronization.toStructuredSHESquareWeightTransportAudit
        |>.preservationAudit
    audit.targetTransportedAverage = audit.sourceAverage :=
  transport.transportedAverage_preserved

theorem histories_not_identified'
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    transport.sourceTheater.side ≠ transport.targetTheater.side :=
  transport.histories_not_identified

theorem finiteHodgeSHETransport_endpoint
    (transport : IUTStage1FiniteHodgeSHETransport record l X C) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family ∧
      transport.sourceTheater =
        record.bundle.structuredSHE.context.domainStructure.theater ∧
      transport.targetTheater =
        record.bundle.structuredSHE.context.codomainStructure.theater ∧
      transport.coordinateEquiv =
        transport.toFactoredObligations.coordinateEquiv ∧
      (∀ j : ZMod l.value,
        transport.toFactoredObligations.targetLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (transport.coordinateEquiv j)) =
          transport.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      (let audit :=
        transport.synchronization.toStructuredSHESquareWeightTransportAudit
          |>.preservationAudit
      audit.targetTransportedAverage = audit.sourceAverage) ∧
      transport.sourceTheater.side ≠ transport.targetTheater.side :=
  ⟨transport.hasStructuredSHE,
    transport.sourceTheater_eq_domain,
    transport.targetTheater_eq_codomain,
    transport.coordinateEquiv_eq_factored,
    transport.fullLabelLogVolume_preserved',
    transport.transportedAverage_preserved',
    transport.histories_not_identified'⟩

end IUTStage1FiniteHodgeSHETransport

/--
Typed witness for an allowed Hodge/SHE forgetful transport.

The witness records the two Hodge-theater sides, the descent operation along
which the finite comparison is read, the permission predicate for forgetting
the holomorphic structure, and the guard that this permission is not an
identification of the two histories.
-/
structure IUTStage1HodgeSHEAllowedForgetfulTransport where
  sourceTheater : QualitativeData.HodgeTheaterId
  targetTheater : QualitativeData.HodgeTheaterId
  descent : AlgorithmicOutput.DescentOperationId
  transportAllowed : Prop
  transport_allowed : transportAllowed
  histories_not_identified : sourceTheater.side ≠ targetTheater.side

namespace IUTStage1HodgeSHEAllowedForgetfulTransport

def ofDescentBridge
    (bridge : IUTStage1HodgeTheaterDescentBridgeData)
    (transportAllowed : Prop)
    (transport_allowed : transportAllowed) :
    IUTStage1HodgeSHEAllowedForgetfulTransport :=
  { sourceTheater := bridge.domainTheater,
    targetTheater := bridge.codomainTheater,
    descent := bridge.descent,
    transportAllowed := transportAllowed,
    transport_allowed := transport_allowed,
    histories_not_identified := bridge.histories_not_identified }

theorem transportAllowed_holds
    (transport : IUTStage1HodgeSHEAllowedForgetfulTransport) :
    transport.transportAllowed :=
  transport.transport_allowed

theorem source_history_ne_target_history
    (transport : IUTStage1HodgeSHEAllowedForgetfulTransport) :
    transport.sourceTheater.side ≠ transport.targetTheater.side :=
  transport.histories_not_identified

theorem ofDescentBridge_endpoint
    (bridge : IUTStage1HodgeTheaterDescentBridgeData)
    (transportAllowed : Prop)
    (transport_allowed : transportAllowed) :
    let transport :=
      ofDescentBridge bridge transportAllowed transport_allowed;
    transport.sourceTheater = bridge.domainTheater ∧
      transport.targetTheater = bridge.codomainTheater ∧
      transport.descent = bridge.descent ∧
      transport.transportAllowed ∧
      transport.sourceTheater.side ≠ transport.targetTheater.side := by
  intro transport
  exact
    ⟨rfl, rfl, rfl, transport.transportAllowed_holds,
      transport.source_history_ne_target_history⟩

/--
Canonical finite-stage permission predicate for the current Hodge/SHE
forgetful transport boundary.

At this stage the formal route only permits forgetting along a descent bridge
that still separates the two Hodge-theater histories.  This is intentionally a
finite shadow of the source-paper Hodge-theater forgetting operation, not a
claim that the full IUT functorial construction has been formalized.
-/
def historySeparatedAllowed
    (bridge : IUTStage1HodgeTheaterDescentBridgeData) : Prop :=
  bridge.domainTheater.side ≠ bridge.codomainTheater.side

def ofHistorySeparatedDescentBridge
    (bridge : IUTStage1HodgeTheaterDescentBridgeData) :
    IUTStage1HodgeSHEAllowedForgetfulTransport :=
  ofDescentBridge bridge
    (historySeparatedAllowed bridge)
    bridge.histories_not_identified

theorem ofHistorySeparatedDescentBridge_endpoint
    (bridge : IUTStage1HodgeTheaterDescentBridgeData) :
    let transport := ofHistorySeparatedDescentBridge bridge;
    transport.sourceTheater = bridge.domainTheater ∧
      transport.targetTheater = bridge.codomainTheater ∧
      transport.descent = bridge.descent ∧
      transport.transportAllowed =
        historySeparatedAllowed bridge ∧
      transport.sourceTheater.side ≠ transport.targetTheater.side := by
  intro transport
  exact
    ⟨rfl, rfl, rfl, rfl,
      transport.source_history_ne_target_history⟩

end IUTStage1HodgeSHEAllowedForgetfulTransport

/--
Source boundary for finite Hodge/SHE transport.

This refines the finite transport object by naming the Hodge-theater descent
bridge and the allowed forgetful transport that justify reading the finite
label comparison without identifying the two Hodge-theater histories.  The
current constructor still uses the Hodge--Arakelov synchronization source for
the finite log-volume preservation data; the descent bridge and forgetting
permission are now separate fields that can later be constructed from the
source-paper Hodge-theater machinery.
-/
structure IUTStage1FiniteHodgeSHETransportSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  synchronization : IUTStage1SHESynchronizationSource record l X C
  descentBridge : IUTStage1HodgeTheaterDescentBridgeData
  descentBridge_eq_structuredSHE :
    descentBridge = record.bundle.hodgeTheaterDescentBridgeData
  forgetfulTransport : IUTStage1HodgeSHEAllowedForgetfulTransport
  forgetful_source_eq :
    forgetfulTransport.sourceTheater = descentBridge.domainTheater
  forgetful_target_eq :
    forgetfulTransport.targetTheater = descentBridge.codomainTheater
  forgetful_descent_eq :
    forgetfulTransport.descent = descentBridge.descent
  coordinateEquiv : ZMod l.value ≃ ZMod l.value
  coordinate_equiv_eq :
    coordinateEquiv =
      synchronization.toFactoredObligations.coordinateEquiv
  fullLabelLogVolume_preserved :
    ∀ j : ZMod l.value,
      synchronization.toFactoredObligations.targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (coordinateEquiv j)) =
        synchronization.toFactoredObligations.sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)
  transportedAverage_preserved :
    let audit :=
      synchronization.toStructuredSHESquareWeightTransportAudit.preservationAudit
    audit.targetTransportedAverage = audit.sourceAverage

namespace IUTStage1FiniteHodgeSHETransportSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

noncomputable def ofSynchronization
    (sync : IUTStage1SHESynchronizationSource record l X C)
    (allowedForgetfulTransport : Prop)
    (allowed_forgetful_transport : allowedForgetfulTransport) :
    IUTStage1FiniteHodgeSHETransportSource record l X C :=
  { synchronization := sync,
    descentBridge := record.bundle.hodgeTheaterDescentBridgeData,
    descentBridge_eq_structuredSHE := rfl,
    forgetfulTransport :=
      IUTStage1HodgeSHEAllowedForgetfulTransport.ofDescentBridge
        record.bundle.hodgeTheaterDescentBridgeData
        allowedForgetfulTransport allowed_forgetful_transport,
    forgetful_source_eq := rfl,
    forgetful_target_eq := rfl,
    forgetful_descent_eq := rfl,
    coordinateEquiv := sync.toFactoredObligations.coordinateEquiv,
    coordinate_equiv_eq := rfl,
    fullLabelLogVolume_preserved := sync.fullLabelLogVolume_preserved,
    transportedAverage_preserved := sync.transportedAverage_eq }

noncomputable def ofThetaEvaluationSources
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    (allowedForgetfulTransport : Prop)
    (allowed_forgetful_transport : allowedForgetfulTransport) :
    IUTStage1FiniteHodgeSHETransportSource record l X C :=
  ofSynchronization
    (record := record)
    (IUTStage1SHESynchronizationSource.ofThetaEvaluationSources
      (record := record)
      sourceEvaluation targetEvaluation canonicalOneDegree_preserved)
    allowedForgetfulTransport allowed_forgetful_transport

noncomputable def ofSynchronizationHistorySeparated
    (sync : IUTStage1SHESynchronizationSource record l X C) :
    IUTStage1FiniteHodgeSHETransportSource record l X C :=
  ofSynchronization
    (record := record) sync
    (IUTStage1HodgeSHEAllowedForgetfulTransport.historySeparatedAllowed
      record.bundle.hodgeTheaterDescentBridgeData)
    record.bundle.hodgeTheaterDescentBridgeData_histories_not_identified

noncomputable def ofThetaEvaluationSourcesHistorySeparated
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    IUTStage1FiniteHodgeSHETransportSource record l X C :=
  ofSynchronizationHistorySeparated
    (record := record)
    (IUTStage1SHESynchronizationSource.ofThetaEvaluationSources
      (record := record)
      sourceEvaluation targetEvaluation canonicalOneDegree_preserved)

theorem descentBridge_domainTheater_eq
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.descentBridge.domainTheater =
      record.bundle.structuredSHE.context.domainStructure.theater := by
  rw [sourceData.descentBridge_eq_structuredSHE]
  exact record.bundle.hodgeTheaterDescentBridgeData_domainTheater_eq

theorem descentBridge_codomainTheater_eq
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.descentBridge.codomainTheater =
      record.bundle.structuredSHE.context.codomainStructure.theater := by
  rw [sourceData.descentBridge_eq_structuredSHE]
  exact record.bundle.hodgeTheaterDescentBridgeData_codomainTheater_eq

theorem histories_not_identified
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.descentBridge.domainTheater.side ≠
      sourceData.descentBridge.codomainTheater.side :=
  sourceData.descentBridge.histories_not_identified

theorem coordinateEquiv_eq_factored
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.coordinateEquiv =
      sourceData.synchronization.toFactoredObligations.coordinateEquiv :=
  sourceData.coordinate_equiv_eq

theorem allowedForgetfulTransport_holds
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.forgetfulTransport.transportAllowed :=
  sourceData.forgetfulTransport.transportAllowed_holds

theorem forgetfulTransport_sourceTheater_eq
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.forgetfulTransport.sourceTheater =
      sourceData.descentBridge.domainTheater :=
  sourceData.forgetful_source_eq

theorem forgetfulTransport_targetTheater_eq
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.forgetfulTransport.targetTheater =
      sourceData.descentBridge.codomainTheater :=
  sourceData.forgetful_target_eq

theorem forgetfulTransport_descent_eq
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.forgetfulTransport.descent =
      sourceData.descentBridge.descent :=
  sourceData.forgetful_descent_eq

noncomputable def toFiniteHodgeSHETransport
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    IUTStage1FiniteHodgeSHETransport record l X C :=
  { synchronization := sourceData.synchronization,
    sourceTheater := sourceData.descentBridge.domainTheater,
    targetTheater := sourceData.descentBridge.codomainTheater,
    source_theater_eq := sourceData.descentBridge_domainTheater_eq,
    target_theater_eq := sourceData.descentBridge_codomainTheater_eq,
    coordinateEquiv := sourceData.coordinateEquiv,
    coordinate_equiv_eq := sourceData.coordinate_equiv_eq,
    fullLabelLogVolume_preserved :=
      sourceData.fullLabelLogVolume_preserved,
    transportedAverage_preserved :=
      sourceData.transportedAverage_preserved,
    histories_not_identified := sourceData.histories_not_identified }

theorem source_endpoint
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    sourceData.descentBridge =
        record.bundle.hodgeTheaterDescentBridgeData ∧
      sourceData.descentBridge.domainTheater =
        record.bundle.structuredSHE.context.domainStructure.theater ∧
      sourceData.descentBridge.codomainTheater =
        record.bundle.structuredSHE.context.codomainStructure.theater ∧
      sourceData.forgetfulTransport.sourceTheater =
        sourceData.descentBridge.domainTheater ∧
      sourceData.forgetfulTransport.targetTheater =
        sourceData.descentBridge.codomainTheater ∧
      sourceData.forgetfulTransport.descent =
        sourceData.descentBridge.descent ∧
      sourceData.forgetfulTransport.transportAllowed ∧
      sourceData.coordinateEquiv =
        sourceData.synchronization.toFactoredObligations.coordinateEquiv ∧
      sourceData.descentBridge.domainTheater.side ≠
        sourceData.descentBridge.codomainTheater.side :=
  ⟨sourceData.descentBridge_eq_structuredSHE,
    sourceData.descentBridge_domainTheater_eq,
    sourceData.descentBridge_codomainTheater_eq,
    sourceData.forgetfulTransport_sourceTheater_eq,
    sourceData.forgetfulTransport_targetTheater_eq,
    sourceData.forgetfulTransport_descent_eq,
    sourceData.allowedForgetfulTransport_holds,
    sourceData.coordinateEquiv_eq_factored,
    sourceData.histories_not_identified⟩

theorem toFiniteHodgeSHETransport_endpoint
    (sourceData :
      IUTStage1FiniteHodgeSHETransportSource record l X C) :
    QualitativeData.HasStructuredSHE package.preLedger.output.family ∧
      sourceData.toFiniteHodgeSHETransport.sourceTheater =
        record.bundle.structuredSHE.context.domainStructure.theater ∧
      sourceData.toFiniteHodgeSHETransport.targetTheater =
        record.bundle.structuredSHE.context.codomainStructure.theater ∧
      sourceData.toFiniteHodgeSHETransport.coordinateEquiv =
        sourceData.toFiniteHodgeSHETransport.toFactoredObligations.coordinateEquiv ∧
      sourceData.forgetfulTransport.transportAllowed ∧
      sourceData.toFiniteHodgeSHETransport.sourceTheater.side ≠
        sourceData.toFiniteHodgeSHETransport.targetTheater.side := by
  let endpoint :=
    sourceData.toFiniteHodgeSHETransport.finiteHodgeSHETransport_endpoint
  exact
    ⟨endpoint.1,
      endpoint.2.1,
      endpoint.2.2.1,
      endpoint.2.2.2.1,
      sourceData.allowedForgetfulTransport_holds,
      endpoint.2.2.2.2.2.2⟩

theorem ofThetaEvaluationSources_endpoint
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    (allowedForgetfulTransport : Prop)
    (allowed_forgetful_transport : allowedForgetfulTransport) :
    let sourceData :=
      ofThetaEvaluationSources
        (record := record)
        sourceEvaluation targetEvaluation canonicalOneDegree_preserved
        allowedForgetfulTransport allowed_forgetful_transport;
    sourceData.synchronization.sourceHA = sourceEvaluation.valueSource ∧
      sourceData.synchronization.targetHA = targetEvaluation.valueSource ∧
      sourceData.forgetfulTransport.transportAllowed ∧
      sourceData.toFiniteHodgeSHETransport.sourceTheater.side ≠
        sourceData.toFiniteHodgeSHETransport.targetTheater.side ∧
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations.coordinateEquiv =
        Equiv.refl (ZMod l.value) := by
  intro sourceData
  exact
    ⟨rfl,
      rfl,
      sourceData.allowedForgetfulTransport_holds,
      sourceData.toFiniteHodgeSHETransport.histories_not_identified',
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations
        |>.comparisonLevel_eq_pointwiseRepresentative,
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations
        |>.coordinateEquiv_eq_refl⟩

theorem ofThetaEvaluationSourcesHistorySeparated_endpoint
    (sourceEvaluation targetEvaluation :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaEvaluationSource
        l X C)
    (canonicalOneDegree_preserved :
      targetEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    let sourceData :=
      ofThetaEvaluationSourcesHistorySeparated
        (record := record)
        sourceEvaluation targetEvaluation canonicalOneDegree_preserved;
    sourceData.synchronization.sourceHA = sourceEvaluation.valueSource ∧
      sourceData.synchronization.targetHA = targetEvaluation.valueSource ∧
      sourceData.forgetfulTransport.transportAllowed =
        IUTStage1HodgeSHEAllowedForgetfulTransport.historySeparatedAllowed
          record.bundle.hodgeTheaterDescentBridgeData ∧
      sourceData.forgetfulTransport.transportAllowed ∧
      sourceData.toFiniteHodgeSHETransport.sourceTheater.side ≠
        sourceData.toFiniteHodgeSHETransport.targetTheater.side ∧
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations.comparisonLevel =
        IUTStage1SquareComparisonLevel.pointwiseRepresentative ∧
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations.coordinateEquiv =
        Equiv.refl (ZMod l.value) := by
  intro sourceData
  exact
    ⟨rfl,
      rfl,
      rfl,
      sourceData.allowedForgetfulTransport_holds,
      sourceData.toFiniteHodgeSHETransport.histories_not_identified',
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations
        |>.comparisonLevel_eq_pointwiseRepresentative,
      sourceData.toFiniteHodgeSHETransport.toFactoredObligations
        |>.coordinateEquiv_eq_refl⟩

end IUTStage1FiniteHodgeSHETransportSource

/--
IPL/log-volume source constructed from finite Hodge/SHE transport.

The prime-strip link data remain explicit, but the Hodge-theater sides and the
log-volume preservation equality are read from the finite Hodge/SHE transport.
Thus the IPL layer no longer needs an independent source/target log-volume
equality when it is used through this source object.
-/
structure IUTStage1IPLLogVolumeTransportSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F)
    (finiteTransport : IUTStage1FiniteHodgeSHETransport record l X C) where
  iplDatum : QualitativeData.IPLDatum package.preLedger.output.family
  link_source_eq_input :
    iplDatum.link.source = iplDatum.inputPrimeStrip
  link_target_eq_output :
    iplDatum.link.target = iplDatum.outputPrimeStrip

namespace IUTStage1IPLLogVolumeTransportSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {finiteTransport : IUTStage1FiniteHodgeSHETransport record l X C}

def ofTheorem311IPLLinkSource
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    IUTStage1IPLLogVolumeTransportSource
      record l X C finiteTransport :=
  { iplDatum := linkSource.iplDatum,
    link_source_eq_input := linkSource.linkSource_eq_input,
    link_target_eq_output := linkSource.linkTarget_eq_output }

def ofTheorem311IPLLinkConstructionSource
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    IUTStage1IPLLogVolumeTransportSource
      record l X C finiteTransport :=
  ofTheorem311IPLLinkSource
    (l := l) (X := X) (C := C)
    (finiteTransport := finiteTransport)
    constructionSource.toIPLLinkSource

noncomputable def sourceLogVolume
    (_sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    Real :=
  let audit :=
    finiteTransport.synchronization.toStructuredSHESquareWeightTransportAudit
      |>.preservationAudit
  audit.sourceAverage

noncomputable def targetLogVolume
    (_sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    Real :=
  let audit :=
    finiteTransport.synchronization.toStructuredSHESquareWeightTransportAudit
      |>.preservationAudit
  audit.targetTransportedAverage

theorem targetLogVolume_preserved
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    sourceData.targetLogVolume = sourceData.sourceLogVolume :=
  finiteTransport.transportedAverage_preserved'

theorem ofTheorem311IPLLinkSource_endpoint
    (linkSource : IUTStage1Theorem311IPLLinkSource record) :
    let sourceData :=
      ofTheorem311IPLLinkSource
        (l := l) (X := X) (C := C)
        (finiteTransport := finiteTransport) linkSource;
    sourceData.iplDatum = package.preLedger.certificate.ipl ∧
      sourceData.iplDatum.link.source =
        sourceData.iplDatum.inputPrimeStrip ∧
      sourceData.iplDatum.link.target =
        sourceData.iplDatum.outputPrimeStrip ∧
      sourceData.targetLogVolume = sourceData.sourceLogVolume :=
  by
    intro sourceData
    exact
      ⟨rfl,
        linkSource.linkSource_eq_input,
        linkSource.linkTarget_eq_output,
        sourceData.targetLogVolume_preserved⟩

theorem ofTheorem311IPLLinkConstructionSource_endpoint
    (constructionSource :
      IUTStage1Theorem311IPLLinkConstructionSource record) :
    let sourceData :=
      ofTheorem311IPLLinkConstructionSource
        (l := l) (X := X) (C := C)
        (finiteTransport := finiteTransport) constructionSource;
    sourceData.iplDatum = package.preLedger.certificate.ipl ∧
      sourceData.iplDatum =
        constructionSource.constructedDatum ∧
      sourceData.iplDatum.link.source =
        sourceData.iplDatum.inputPrimeStrip ∧
      sourceData.iplDatum.link.target =
        sourceData.iplDatum.outputPrimeStrip ∧
      sourceData.targetLogVolume = sourceData.sourceLogVolume :=
  by
    intro sourceData
    exact
      ⟨rfl,
        constructionSource.iplDatum_eq_constructedDatum,
        constructionSource.linkSource_eq_input,
        constructionSource.linkTarget_eq_output,
        sourceData.targetLogVolume_preserved⟩

noncomputable def toIPLLogVolumeTransport
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    IUTStage1IPLLogVolumeTransport record :=
  { iplDatum := sourceData.iplDatum,
    sourceTheater := finiteTransport.sourceTheater,
    targetTheater := finiteTransport.targetTheater,
    source_theater_eq := finiteTransport.source_theater_eq,
    target_theater_eq := finiteTransport.target_theater_eq,
    link_source_eq_input := sourceData.link_source_eq_input,
    link_target_eq_output := sourceData.link_target_eq_output,
    sourceLogVolume := sourceData.sourceLogVolume,
    targetLogVolume := sourceData.targetLogVolume,
    targetLogVolume_eq_sourceLogVolume :=
      sourceData.targetLogVolume_preserved,
    histories_not_identified := finiteTransport.histories_not_identified }

set_option linter.style.longLine false in
/--
IPL log-volume provenance from the finite Hodge/SHE transport.

The IPL source does not introduce an independent log-volume equality: its
source log-volume is the source average of the finite Hodge/SHE transport
audit, its target log-volume is the transported target average, and preservation
is exactly the transported-average equality supplied by the finite
Hodge/SHE layer.
-/
theorem finiteTransportLogVolume_endpoint
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    let audit :=
      finiteTransport.synchronization.toStructuredSHESquareWeightTransportAudit
        |>.preservationAudit;
    sourceData.sourceLogVolume = audit.sourceAverage ∧
      sourceData.targetLogVolume = audit.targetTransportedAverage ∧
      sourceData.targetLogVolume = sourceData.sourceLogVolume ∧
      sourceData.toIPLLogVolumeTransport.sourceLogVolume = audit.sourceAverage ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume = audit.targetTransportedAverage ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume =
        sourceData.toIPLLogVolumeTransport.sourceLogVolume :=
  by
    intro audit
    exact
      ⟨rfl,
        rfl,
        sourceData.targetLogVolume_preserved,
        rfl,
        rfl,
        sourceData.toIPLLogVolumeTransport.targetLogVolume_preserved⟩

theorem finiteTransport_sourceTheater_eq
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    sourceData.toIPLLogVolumeTransport.sourceTheater =
      finiteTransport.sourceTheater :=
  rfl

theorem finiteTransport_targetTheater_eq
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    sourceData.toIPLLogVolumeTransport.targetTheater =
      finiteTransport.targetTheater :=
  rfl

theorem toIPLLogVolumeTransport_endpoint
    (sourceData :
      IUTStage1IPLLogVolumeTransportSource
        record l X C finiteTransport) :
    QualitativeData.HasStructuredIPL package.preLedger.output.family ∧
      sourceData.toIPLLogVolumeTransport.sourceTheater =
        finiteTransport.sourceTheater ∧
      sourceData.toIPLLogVolumeTransport.targetTheater =
        finiteTransport.targetTheater ∧
      sourceData.toIPLLogVolumeTransport.iplDatum.link.source =
        sourceData.toIPLLogVolumeTransport.iplDatum.inputPrimeStrip ∧
      sourceData.toIPLLogVolumeTransport.iplDatum.link.target =
        sourceData.toIPLLogVolumeTransport.iplDatum.outputPrimeStrip ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume =
        sourceData.toIPLLogVolumeTransport.sourceLogVolume ∧
      sourceData.toIPLLogVolumeTransport.sourceTheater.side ≠
        sourceData.toIPLLogVolumeTransport.targetTheater.side :=
  ⟨sourceData.toIPLLogVolumeTransport.hasStructuredIPL,
    sourceData.finiteTransport_sourceTheater_eq,
    sourceData.finiteTransport_targetTheater_eq,
    sourceData.toIPLLogVolumeTransport.linkSource_eq_datum_source,
    sourceData.toIPLLogVolumeTransport.linkTarget_eq_datum_target,
    sourceData.toIPLLogVolumeTransport.targetLogVolume_preserved,
    sourceData.toIPLLogVolumeTransport.histories_not_identified'⟩

end IUTStage1IPLLogVolumeTransportSource

/--
Finite Hodge/SHE transport with a constructed Theorem 3.11 IPL link.

This binds the two inputs that previously appeared side by side at many bridge
boundaries: the finite Hodge/SHE transport source and the constructed
input-prime-strip link.  The associated IPL/log-volume transport is projected
from this single source object, so the log-volume preservation is read from the
same finite Hodge/SHE transport that supplies the Hodge-theater sides.
-/
structure IUTStage1FiniteHodgeSHEIPLConstructionSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  transportSource : IUTStage1FiniteHodgeSHETransportSource record l X C
  iplConstructionSource :
    IUTStage1Theorem311IPLLinkConstructionSource record

namespace IUTStage1FiniteHodgeSHEIPLConstructionSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

noncomputable def finiteTransport
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    IUTStage1FiniteHodgeSHETransport record l X C :=
  sourceData.transportSource.toFiniteHodgeSHETransport

def constructedDatum
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    QualitativeData.IPLDatum package.preLedger.output.family :=
  sourceData.iplConstructionSource.constructedDatum

def iplDatum
    (_sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    QualitativeData.IPLDatum package.preLedger.output.family :=
  package.preLedger.certificate.ipl

noncomputable def toIPLLogVolumeTransportSource
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    IUTStage1IPLLogVolumeTransportSource
      record l X C sourceData.finiteTransport :=
  IUTStage1IPLLogVolumeTransportSource.ofTheorem311IPLLinkConstructionSource
    (l := l) (X := X) (C := C)
    (finiteTransport := sourceData.finiteTransport)
    sourceData.iplConstructionSource

noncomputable def toIPLLogVolumeTransport
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    IUTStage1IPLLogVolumeTransport record :=
  sourceData.toIPLLogVolumeTransportSource.toIPLLogVolumeTransport

theorem iplDatum_eq_constructedDatum
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    sourceData.iplDatum = sourceData.constructedDatum :=
  sourceData.iplConstructionSource.iplDatum_eq_constructedDatum

theorem targetLogVolume_preserved
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    sourceData.toIPLLogVolumeTransport.targetLogVolume =
      sourceData.toIPLLogVolumeTransport.sourceLogVolume :=
  sourceData.toIPLLogVolumeTransport.targetLogVolume_preserved

set_option linter.style.longLine false in
/--
Constructed IPL log-volume provenance from the finite Hodge/SHE transport.

For the combined finite Hodge/SHE plus constructed IPL-link source, the
resulting IPL transport reads its source and target log-volume values directly
from the finite Hodge/SHE transported-average audit.
-/
theorem constructedIPLFiniteTransportLogVolume_endpoint
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    let audit :=
      sourceData.finiteTransport.synchronization.toStructuredSHESquareWeightTransportAudit
        |>.preservationAudit;
    sourceData.toIPLLogVolumeTransport.sourceLogVolume = audit.sourceAverage ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume =
        audit.targetTransportedAverage ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume =
        sourceData.toIPLLogVolumeTransport.sourceLogVolume ∧
      sourceData.toIPLLogVolumeTransportSource.sourceLogVolume =
        audit.sourceAverage ∧
      sourceData.toIPLLogVolumeTransportSource.targetLogVolume =
        audit.targetTransportedAverage ∧
      sourceData.toIPLLogVolumeTransportSource.targetLogVolume =
        sourceData.toIPLLogVolumeTransportSource.sourceLogVolume :=
  by
    intro audit
    exact
      ⟨rfl,
        rfl,
        sourceData.targetLogVolume_preserved,
        rfl,
        rfl,
        sourceData.toIPLLogVolumeTransportSource.targetLogVolume_preserved⟩

set_option linter.style.longLine false in
theorem source_endpoint
    (sourceData :
      IUTStage1FiniteHodgeSHEIPLConstructionSource record l X C) :
    sourceData.toIPLLogVolumeTransport.iplDatum =
        package.preLedger.certificate.ipl ∧
      sourceData.toIPLLogVolumeTransport.iplDatum =
        sourceData.constructedDatum ∧
      sourceData.toIPLLogVolumeTransport.iplDatum.link.source =
        sourceData.toIPLLogVolumeTransport.iplDatum.inputPrimeStrip ∧
      sourceData.toIPLLogVolumeTransport.iplDatum.link.target =
        sourceData.toIPLLogVolumeTransport.iplDatum.outputPrimeStrip ∧
      sourceData.toIPLLogVolumeTransport.sourceTheater =
        sourceData.finiteTransport.sourceTheater ∧
      sourceData.toIPLLogVolumeTransport.targetTheater =
        sourceData.finiteTransport.targetTheater ∧
      sourceData.toIPLLogVolumeTransport.targetLogVolume =
        sourceData.toIPLLogVolumeTransport.sourceLogVolume ∧
      sourceData.transportSource.forgetfulTransport.transportAllowed ∧
      sourceData.toIPLLogVolumeTransport.sourceTheater.side ≠
        sourceData.toIPLLogVolumeTransport.targetTheater.side :=
  ⟨rfl,
    sourceData.iplDatum_eq_constructedDatum,
    sourceData.iplConstructionSource.linkSource_eq_input,
    sourceData.iplConstructionSource.linkTarget_eq_output,
    rfl,
    rfl,
    sourceData.targetLogVolume_preserved,
    sourceData.transportSource.allowedForgetfulTransport_holds,
    sourceData.toIPLLogVolumeTransport.histories_not_identified'⟩

end IUTStage1FiniteHodgeSHEIPLConstructionSource

/--
Boundary comparing the strengthened SHE/common-container route with the factored
square/full-label preservation interface.

The compatibility data records the simultaneous common-container bookkeeping,
but the primitive `j^2` and full-label preservation fields remain separate
obligations.
-/
structure IUTStage1StructuredSHEFactoredPreservationBoundary
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) where
  commonContainerCompatibility :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE

namespace IUTStage1StructuredSHEFactoredPreservationBoundary

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}

def ofBundle
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1StructuredSHEFactoredPreservationBoundary package bundle :=
  { commonContainerCompatibility := bundle.commonContainerCompatibility }

def missingFactoredSquareFullLabelData
    (_boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    Finset IUTStage1FactoredSquareFullLabelMissingDatum :=
  IUTStage1FactoredSquareFullLabelMissingDatum.all

theorem commonContainerContextMatches
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext :=
  boundary.commonContainerCompatibility.commonContainerContextMatches

theorem simultaneousValid
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    bundle.structuredSHE.context.simultaneous_valid :=
  boundary.commonContainerCompatibility.simultaneousValid

theorem domainHistory_ne_codomainHistory
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  boundary.commonContainerCompatibility.domainHistory_ne_codomainHistory

theorem coordinateSquarePreservation_missing
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation_mem_all

theorem fullLabelMapPreservation_missing
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation_mem_all

theorem fullLabelValuePreservation_missing
    (boundary :
      IUTStage1StructuredSHEFactoredPreservationBoundary package bundle) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      boundary.missingFactoredSquareFullLabelData :=
  IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation_mem_all

end IUTStage1StructuredSHEFactoredPreservationBoundary

/--
Audited entry from the strengthened SHE route into the existing `HDD o SHE`
boundedness API.

This record keeps the SHE/common-container compatibility proof next to the
boundedness facts obtained by applying the charted common container to the
pre-ledger certificate. It deliberately stops at target-volume bounds; the
q-side membership step and the final signed Corollary 3.12 packaging remain
separate.
-/
structure IUTStage1Theorem311AuditedHDDSHEBound
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) : Prop where
  compatibility :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE
  common_container_bound_audit :
    package.preLedger.chartedContainer.commonContainer.BoundAudit
      package.preLedger.certificate
  local_expression_valid :
    bundle.structuredSHE.context.simultaneousExpression.AllLocalValid
  chosen_target_volume_le_theta :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned
  all_targets_at_most_theta :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311AuditedHDDSHEBound

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  { compatibility := bundle.commonContainerCompatibility,
    common_container_bound_audit :=
      package.preLedger.chartedContainer.commonContainer.boundAudit
        package.preLedger.certificate,
    local_expression_valid :=
      bundle.structuredSHE.context.allLocalExpressionValid,
    chosen_target_volume_le_theta :=
      package.preLedger.chartedContainer.choice_targetVolume_le
        package.preLedger.certificate package.preLedger.chosenOutput.choice,
    all_targets_at_most_theta :=
      package.preLedger.chartedContainer.allTargetsAtMost
        package.preLedger.certificate,
    histories_not_identified := bundle.domainHistory_ne_codomainHistory }

theorem commonContainerCompatibility
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE :=
  audited.compatibility

theorem commonContainerBoundAudit
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.BoundAudit
      package.preLedger.certificate :=
  audited.common_container_bound_audit

theorem hddSHEDecompositionAudit
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.hddShe.DecompositionAudit
      package.preLedger.certificate :=
  audited.commonContainerBoundAudit.hddSHEDecomposition

theorem hddDecompositionAudit
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.DecompositionAudit
      package.preLedger.certificate :=
  audited.hddSHEDecompositionAudit.hddDecomposition

theorem hullDetBoundAudit
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge.BoundAudit
      package.preLedger.certificate :=
  audited.hddDecompositionAudit.hullDetBoundAudit

theorem sheArrowMatchesContext
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      bundle.structuredSHE.context.sheDatum :=
  audited.compatibility.sheArrowMatchesContext

theorem sheDatumMatchesCertificate
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.sheDatum =
      package.preLedger.certificate.she :=
  audited.compatibility.sheDatumMatchesCertificate

theorem sheArrowDatumMatchesCertificate
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  audited.sheArrowMatchesContext.trans audited.sheDatumMatchesCertificate

theorem commonContainerContextMatches
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext :=
  audited.compatibility.commonContainerContextMatches

theorem qPilotTheater_eq_codomain
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.qPilotStructure.theater =
      bundle.structuredSHE.context.codomainStructure.theater :=
  audited.compatibility.qPilotTheater_eq_codomain

theorem thetaPilotTheater_eq_domain
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.thetaPilotStructure.theater =
      bundle.structuredSHE.context.domainStructure.theater :=
  audited.compatibility.thetaPilotTheater_eq_domain

theorem localExpressionValid
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.simultaneousExpression.AllLocalValid :=
  audited.local_expression_valid

theorem qPilotExpressionValid
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.simultaneousExpression.q_pilot_expression_valid :=
  audited.localExpressionValid.2.2.1

theorem thetaPilotExpressionValid
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.simultaneousExpression.theta_pilot_expression_valid :=
  audited.localExpressionValid.2.2.2.1

theorem simultaneousValid
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.simultaneous_valid :=
  audited.localExpressionValid.2.2.2.2

theorem chosenTargetVolume_le_theta
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned :=
  audited.chosen_target_volume_le_theta

theorem allTargetsAtMost_theta
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  audited.all_targets_at_most_theta

theorem domainHistory_ne_codomainHistory
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  audited.histories_not_identified

end IUTStage1Theorem311AuditedHDDSHEBound

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem auditedHDDSHEBound
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  IUTStage1Theorem311AuditedHDDSHEBound.ofStructuredInputsWithSHE bundle

theorem auditedHDDSHE_chosenTargetVolume_le_theta
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned :=
  bundle.auditedHDDSHEBound.chosenTargetVolume_le_theta

theorem auditedHDDSHE_allTargetsAtMost_theta
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  bundle.auditedHDDSHEBound.allTargetsAtMost_theta

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Audited connection from the `HDD o SHE` bound to the charted target-volume
middle term used later in the signed comparison.

This is still not the q-to-Theta comparison. It only states that the named
middle term in the pre-ledger is the chosen target volume bounded by the
audited `HDD o SHE` route.
-/
structure IUTStage1Theorem311AuditedTargetVolumeMiddle
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) : Prop where
  audited_hdd_she_bound :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle
  target_signed_eq_chosen_volume :
    package.preLedger.targetVolume.targetSigned =
      RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice)
  target_signed_le_theta :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311AuditedTargetVolumeMiddle

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}

theorem ofAuditedHDDSHEBound
    (audited : IUTStage1Theorem311AuditedHDDSHEBound package bundle) :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle :=
  { audited_hdd_she_bound := audited,
    target_signed_eq_chosen_volume :=
      package.preLedger.targetSigned_eq_choiceTargetVolume,
    target_signed_le_theta := by
      rw [package.preLedger.targetSigned_eq_choiceTargetVolume]
      exact audited.chosenTargetVolume_le_theta,
    histories_not_identified := audited.domainHistory_ne_codomainHistory }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle :=
  ofAuditedHDDSHEBound bundle.auditedHDDSHEBound

theorem auditedHDDSHEBound
    (middle :
      IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  middle.audited_hdd_she_bound

theorem targetSigned_eq_chosenTargetVolume
    (middle :
      IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    package.preLedger.targetVolume.targetSigned =
      RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) :=
  middle.target_signed_eq_chosen_volume

theorem chosenTargetVolume_eq_targetSigned
    (middle :
      IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) =
      package.preLedger.targetVolume.targetSigned :=
  middle.targetSigned_eq_chosenTargetVolume.symm

theorem targetSigned_le_theta
    (middle :
      IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  middle.target_signed_le_theta

theorem domainHistory_ne_codomainHistory
    (middle :
      IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  middle.histories_not_identified

end IUTStage1Theorem311AuditedTargetVolumeMiddle

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem auditedTargetVolumeMiddle
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle :=
  IUTStage1Theorem311AuditedTargetVolumeMiddle.ofStructuredInputsWithSHE bundle

theorem auditedTargetSigned_eq_chosenTargetVolume
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.targetVolume.targetSigned =
      RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) :=
  bundle.auditedTargetVolumeMiddle.targetSigned_eq_chosenTargetVolume

theorem auditedTargetSigned_le_theta
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  bundle.auditedTargetVolumeMiddle.targetSigned_le_theta

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Audited lower-middle bridge from the charted q-side datum to the charted
target-volume middle term.

This records the membership/charting contribution to the eventual inequality
chain. It is intentionally separate from the `HDD o SHE` upper bound and from
the final signed q-to-Theta packaging.
-/
structure IUTStage1Theorem311AuditedMembershipMiddle
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) : Prop where
  target_volume_middle :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle
  q_charted :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord =
      package.preLedger.qSigned
  chosen_holds :
    package.preLedger.chosenOutput.comparison.Holds
      package.preLedger.qValue.qPoint
  q_signed_le_target :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311AuditedMembershipMiddle

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}

theorem ofTargetVolumeMiddle
    (middle : IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle) :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle :=
  { target_volume_middle := middle,
    q_charted := package.preLedger.qSigned_eq_chartedQ,
    chosen_holds := package.preLedger.chosenComparisonHoldsQ,
    q_signed_le_target := package.preLedger.qSigned_le_targetSigned,
    histories_not_identified := middle.domainHistory_ne_codomainHistory }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle :=
  ofTargetVolumeMiddle bundle.auditedTargetVolumeMiddle

theorem targetVolumeMiddle
    (middle :
      IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle :=
  middle.target_volume_middle

theorem qCharted
    (middle :
      IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord =
      package.preLedger.qSigned :=
  middle.q_charted

theorem chosenHolds
    (middle :
      IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    package.preLedger.chosenOutput.comparison.Holds
      package.preLedger.qValue.qPoint :=
  middle.chosen_holds

theorem qSigned_le_targetSigned
    (middle :
      IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned :=
  middle.q_signed_le_target

theorem domainHistory_ne_codomainHistory
    (middle :
      IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  middle.histories_not_identified

end IUTStage1Theorem311AuditedMembershipMiddle

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem auditedMembershipMiddle
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle :=
  IUTStage1Theorem311AuditedMembershipMiddle.ofStructuredInputsWithSHE bundle

theorem auditedQCharted
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord =
      package.preLedger.qSigned :=
  bundle.auditedMembershipMiddle.qCharted

theorem auditedChosenHolds
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.chosenOutput.comparison.Holds
      package.preLedger.qValue.qPoint :=
  bundle.auditedMembershipMiddle.chosenHolds

theorem auditedQSigned_le_targetSigned
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned :=
  bundle.auditedMembershipMiddle.qSigned_le_targetSigned

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Audited composition of the lower and upper middle inequalities.

This produces only the raw real inequality `qSigned <= thetaSigned`. It is not
the Corollary 3.12 endpoint: no q-positivity, source normalization, signed pilot
objects, or public comparison payload are introduced here.
-/
structure IUTStage1Theorem311AuditedRawInequality
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) : Prop where
  membership_middle :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle
  q_signed_le_target :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned
  target_signed_le_theta :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned
  q_signed_le_theta :
    package.preLedger.qSigned <= package.preLedger.thetaSigned
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311AuditedRawInequality

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}

theorem ofMembershipMiddle
    (middle : IUTStage1Theorem311AuditedMembershipMiddle package bundle) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  { membership_middle := middle,
    q_signed_le_target := middle.qSigned_le_targetSigned,
    target_signed_le_theta := middle.targetVolumeMiddle.targetSigned_le_theta,
    q_signed_le_theta :=
      le_trans middle.qSigned_le_targetSigned
        middle.targetVolumeMiddle.targetSigned_le_theta,
    histories_not_identified := middle.domainHistory_ne_codomainHistory }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  ofMembershipMiddle bundle.auditedMembershipMiddle

theorem membershipMiddle
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle) :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle :=
  raw.membership_middle

theorem qSigned_le_targetSigned
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle) :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned :=
  raw.q_signed_le_target

theorem targetSigned_le_theta
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  raw.target_signed_le_theta

theorem qSigned_le_thetaSigned
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  raw.q_signed_le_theta

theorem domainHistory_ne_codomainHistory
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  raw.histories_not_identified

end IUTStage1Theorem311AuditedRawInequality

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem auditedRawInequality
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  IUTStage1Theorem311AuditedRawInequality.ofStructuredInputsWithSHE bundle

theorem auditedRaw_qSigned_le_thetaSigned
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  bundle.auditedRawInequality.qSigned_le_thetaSigned

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Source-facing side conditions needed for Stage 1 ledger promotion.

These conditions are intentionally separate from the Theorem 3.11 subclaims:
they record the sign/normalization hypotheses that must accompany the
algorithmic and SHE-alignment data.
-/
structure IUTStage1SourceSideConditions
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  q_pilot_positive : 0 < -package.preLedger.qSigned
  source_normalization : package.preLedger.normalization

namespace IUTStage1SourceSideConditions

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem qPilotPositive
    (sideConditions : IUTStage1SourceSideConditions package) :
    0 < -package.preLedger.qSigned :=
  sideConditions.q_pilot_positive

theorem sourceNormalization
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.preLedger.normalization :=
  sideConditions.source_normalization

end IUTStage1SourceSideConditions

namespace IUTStage1SourceHullDetObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def sideConditions
    (obligations : IUTStage1SourceHullDetObligations package) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := obligations.qPilotPositive,
    source_normalization := obligations.normalization }

end IUTStage1SourceHullDetObligations

/--
Audited boundary between the raw real inequality and the signed comparison
payload used for Corollary 3.12-style statements.

The raw inequality is still sourced from the audited SHE/HDD/membership route.
The side conditions are supplied explicitly here, so q-positivity and source
normalization are not hidden inside the inequality composition.
-/
structure IUTStage1Theorem311AuditedSignedPayloadBoundary
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  raw_inequality :
    IUTStage1Theorem311AuditedRawInequality package bundle
  q_pilot_positive : 0 < -package.preLedger.qSigned
  source_normalization : package.preLedger.normalization
  theta_chart_trivial :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned
  theta_charted :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned
  q_signed_le_theta :
    package.preLedger.qSigned <= package.preLedger.thetaSigned
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace IUTStage1Theorem311AuditedSignedPayloadBoundary

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofRawInequality
    (raw : IUTStage1Theorem311AuditedRawInequality package bundle)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions :=
  { raw_inequality := raw,
    q_pilot_positive := sideConditions.qPilotPositive,
    source_normalization := sideConditions.sourceNormalization,
    theta_chart_trivial := package.preLedger.thetaChartTrivial,
    q_charted := package.preLedger.qSigned_eq_chartedQ,
    theta_charted := package.preLedger.thetaSigned_eq_chartedTheta,
    q_signed_le_theta := raw.qSigned_le_thetaSigned,
    histories_not_identified := raw.domainHistory_ne_codomainHistory }

theorem ofStructuredInputsWithSideConditions
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions :=
  ofRawInequality bundle.auditedRawInequality sideConditions

theorem rawInequality
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  boundary.raw_inequality

theorem qPilotPositive
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    0 < -package.preLedger.qSigned :=
  boundary.q_pilot_positive

theorem sourceNormalization
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    package.preLedger.normalization :=
  boundary.source_normalization

theorem thetaChartTrivial
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget :=
  boundary.theta_chart_trivial

theorem qCharted
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned :=
  boundary.q_charted

theorem thetaCharted
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  boundary.theta_charted

theorem qSigned_le_thetaSigned
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  boundary.q_signed_le_theta

def comparisonData
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    Corollary312ComparisonData :=
  { thetaSigned := package.preLedger.thetaSigned,
    qSigned := package.preLedger.qSigned,
    q_positive := boundary.qPilotPositive,
    qSigned_le_thetaSigned := boundary.qSigned_le_thetaSigned }

theorem comparisonData_qSigned
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    boundary.comparisonData.qSigned = package.preLedger.qSigned :=
  rfl

theorem comparisonData_thetaSigned
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    boundary.comparisonData.thetaSigned = package.preLedger.thetaSigned :=
  rfl

theorem comparisonData_qSigned_le_thetaSigned
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    boundary.comparisonData.qSigned <= boundary.comparisonData.thetaSigned :=
  boundary.comparisonData.qSigned_le_thetaSigned

theorem comparisonData_corollary312
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    Corollary312Inequality
      boundary.comparisonData.thetaPilot boundary.comparisonData.qPilot :=
  boundary.comparisonData.corollary312

theorem domainHistory_ne_codomainHistory
    (boundary :
      IUTStage1Theorem311AuditedSignedPayloadBoundary
        package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  boundary.histories_not_identified

end IUTStage1Theorem311AuditedSignedPayloadBoundary

namespace IUTStage1Theorem311StructuredInputsWithSHE

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem auditedSignedPayloadBoundary
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions :=
  IUTStage1Theorem311AuditedSignedPayloadBoundary.ofStructuredInputsWithSideConditions
    bundle sideConditions

def auditedComparisonData
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    Corollary312ComparisonData :=
  (bundle.auditedSignedPayloadBoundary sideConditions).comparisonData

theorem auditedComparisonData_qSigned_le_thetaSigned
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    (bundle.auditedComparisonData sideConditions).qSigned <=
      (bundle.auditedComparisonData sideConditions).thetaSigned :=
  (bundle.auditedSignedPayloadBoundary
    sideConditions).comparisonData_qSigned_le_thetaSigned

end IUTStage1Theorem311StructuredInputsWithSHE

/--
Source-facing hypotheses for the side conditions used in Stage 1 promotion.

This record gives source-oriented names to the q-pilot sign and normalization
assumptions before converting them to `IUTStage1SourceSideConditions`.
-/
structure IUTStage1SourceSideConditionHypotheses
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  q_pilot_log_volume_positive : 0 < -package.preLedger.qSigned
  source_normalized : package.preLedger.normalization

namespace IUTStage1SourceSideConditionHypotheses

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem qPilotLogVolumePositive
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    0 < -package.preLedger.qSigned :=
  hypotheses.q_pilot_log_volume_positive

theorem sourceNormalized
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.preLedger.normalization :=
  hypotheses.source_normalized

def toSideConditions
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := hypotheses.qPilotLogVolumePositive,
    source_normalization := hypotheses.sourceNormalized }

def ofSideConditions
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceSideConditionHypotheses package :=
  { q_pilot_log_volume_positive := sideConditions.qPilotPositive,
    source_normalized := sideConditions.sourceNormalization }

theorem toSideConditions_ofSideConditions
    (sideConditions : IUTStage1SourceSideConditions package) :
    (ofSideConditions sideConditions).toSideConditions = sideConditions :=
  Subsingleton.elim _ _

/--
Audit record tying side-condition hypotheses to their source-facing labels.

This record still carries no proof beyond the hypotheses themselves; it records
which labeled q-pilot log-volume and normalization data the hypotheses concern.
-/
structure Audit
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) : Prop where
  qPilotLogVolume_matches_labels :
    package.qPilotLogVolume = package.labels.qPilotLogVolume
  sourceNormalization_matches_labels :
    package.sourceNormalizationLabel = package.labels.sourceNormalization
  q_pilot_log_volume_positive : 0 < -package.preLedger.qSigned
  source_normalized : package.preLedger.normalization

theorem audit
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Audit hypotheses :=
  { qPilotLogVolume_matches_labels :=
      package.qPilotLogVolume_matches_labels,
    sourceNormalization_matches_labels :=
      package.sourceNormalization_matches_labels,
    q_pilot_log_volume_positive := hypotheses.qPilotLogVolumePositive,
    source_normalized := hypotheses.sourceNormalized }

namespace Audit

variable {hypotheses : IUTStage1SourceSideConditionHypotheses package}

theorem qPilotLogVolumeMatchesLabels
    (audit : Audit hypotheses) :
    package.qPilotLogVolume = package.labels.qPilotLogVolume :=
  audit.qPilotLogVolume_matches_labels

theorem sourceNormalizationMatchesLabels
    (audit : Audit hypotheses) :
    package.sourceNormalizationLabel = package.labels.sourceNormalization :=
  audit.sourceNormalization_matches_labels

theorem qPilotLogVolumePositive
    (audit : Audit hypotheses) :
    0 < -package.preLedger.qSigned :=
  audit.q_pilot_log_volume_positive

theorem sourceNormalized
    (audit : Audit hypotheses) :
    package.preLedger.normalization :=
  audit.source_normalized

end Audit

end IUTStage1SourceSideConditionHypotheses

namespace IUTStage1SourceObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

def ofSubclaimsAndSideConditions
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceObligations package :=
  { algorithm_certified := subclaims.algorithmOutputCertified,
    she_arrow_matches_certificate := subclaims.hodgeTheaterSHEAlignment,
    q_pilot_positive := sideConditions.qPilotPositive,
    normalization := sideConditions.sourceNormalization }

def ofStructuredInputsAndSideConditions
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceObligations package :=
  { algorithm_certified :=
      inputs.algorithmicOutput.algorithmOutputCertified,
    she_arrow_matches_certificate :=
      inputs.sheAlignment.hodgeTheaterSHEAlignment,
    q_pilot_positive := sideConditions.qPilotPositive,
    normalization := sideConditions.sourceNormalization }

theorem ofStructuredInputsAndSideConditions_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    ofStructuredInputsAndSideConditions inputs sideConditions =
      ofSubclaimsAndSideConditions inputs.theorem311Subclaims sideConditions :=
  rfl

def ofSubclaimsAndSideConditionHypotheses
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceObligations package :=
  ofSubclaimsAndSideConditions subclaims hypotheses.toSideConditions

def ofStructuredInputsAndSideConditionHypotheses
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceObligations package :=
  ofStructuredInputsAndSideConditions inputs hypotheses.toSideConditions

theorem ofStructuredInputsAndSideConditionHypotheses_eq_sideConditions
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ofStructuredInputsAndSideConditionHypotheses inputs hypotheses =
      ofStructuredInputsAndSideConditions inputs hypotheses.toSideConditions :=
  rfl

theorem ofStructuredInputsAndSideConditionHypotheses_eq_subclaims
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ofStructuredInputsAndSideConditionHypotheses inputs hypotheses =
      ofSubclaimsAndSideConditionHypotheses
        inputs.theorem311Subclaims hypotheses :=
  rfl

theorem ofSubclaimsAndSideConditionHypotheses_eq_sideConditions
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ofSubclaimsAndSideConditionHypotheses subclaims hypotheses =
      ofSubclaimsAndSideConditions subclaims hypotheses.toSideConditions :=
  rfl

end IUTStage1SourceObligations

/--
Named source-level gap below `IUTStage1SourceObligations`.

The fields use source-facing names for the mathematical work still needed to
turn a source package into a promoted source-obligation ledger.
-/
structure IUTStage1SourceObligationGap
    {source target : Copy} {index : Type u}
    (package : IUTStage1SourcePackage source target index) : Prop where
  theorem311_algorithm_certified : package.preLedger.output.Certified
  she_alignment :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she
  q_pilot_positive : 0 < -package.preLedger.qSigned
  source_normalization : package.preLedger.normalization

namespace IUTStage1SourceObligationGap

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem theorem311AlgorithmCertified
    (gap : IUTStage1SourceObligationGap package) :
    package.preLedger.output.Certified :=
  gap.theorem311_algorithm_certified

theorem sheAlignment
    (gap : IUTStage1SourceObligationGap package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  gap.she_alignment

theorem qPilotPositive
    (gap : IUTStage1SourceObligationGap package) :
    0 < -package.preLedger.qSigned :=
  gap.q_pilot_positive

theorem sourceNormalization
    (gap : IUTStage1SourceObligationGap package) :
    package.preLedger.normalization :=
  gap.source_normalization

def theorem311Subclaims
    (gap : IUTStage1SourceObligationGap package) :
    IUTStage1Theorem311Subclaims package :=
  { algorithm_output_certified := gap.theorem311AlgorithmCertified,
    hodge_theater_she_alignment := gap.sheAlignment }

def theorem311StructuredInputs
    (gap : IUTStage1SourceObligationGap package) :
    IUTStage1Theorem311StructuredInputs package :=
  { preledger_audit := package.preLedger.audit,
    theorem311_subclaims := gap.theorem311Subclaims }

theorem theorem311StructuredInputs_subclaims
    (gap : IUTStage1SourceObligationGap package) :
    gap.theorem311StructuredInputs.theorem311Subclaims =
      gap.theorem311Subclaims :=
  rfl

def sideConditions
    (gap : IUTStage1SourceObligationGap package) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := gap.qPilotPositive,
    source_normalization := gap.sourceNormalization }

def sideConditionHypotheses
    (gap : IUTStage1SourceObligationGap package) :
    IUTStage1SourceSideConditionHypotheses package :=
  IUTStage1SourceSideConditionHypotheses.ofSideConditions gap.sideConditions

def toSourceObligations
    (gap : IUTStage1SourceObligationGap package) :
    IUTStage1SourceObligations package :=
  { algorithm_certified := gap.theorem311AlgorithmCertified,
    she_arrow_matches_certificate := gap.sheAlignment,
    q_pilot_positive := gap.qPilotPositive,
    normalization := gap.sourceNormalization }

theorem toSourceObligations_eq_subclaimsAndSideConditions
    (gap : IUTStage1SourceObligationGap package) :
    gap.toSourceObligations =
      IUTStage1SourceObligations.ofSubclaimsAndSideConditions
        gap.theorem311Subclaims gap.sideConditions :=
  rfl

/--
Compact audit checklist for the source-level obligation gap.

This record gathers the four named source-gap projections before they are
promoted to `IUTStage1SourceObligations`.
-/
structure Audit
    (gap : IUTStage1SourceObligationGap package) : Prop where
  theorem311_algorithm_certified : package.preLedger.output.Certified
  she_alignment :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she
  q_pilot_positive : 0 < -package.preLedger.qSigned
  source_normalization : package.preLedger.normalization

theorem audit
    (gap : IUTStage1SourceObligationGap package) :
    Audit gap :=
  { theorem311_algorithm_certified := gap.theorem311AlgorithmCertified,
    she_alignment := gap.sheAlignment,
    q_pilot_positive := gap.qPilotPositive,
    source_normalization := gap.sourceNormalization }

namespace Audit

variable {gap : IUTStage1SourceObligationGap package}

theorem theorem311AlgorithmCertified
    (gapAudit : Audit gap) :
    package.preLedger.output.Certified :=
  gapAudit.theorem311_algorithm_certified

theorem sheAlignment
    (gapAudit : Audit gap) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  gapAudit.she_alignment

theorem qPilotPositive
    (gapAudit : Audit gap) :
    0 < -package.preLedger.qSigned :=
  gapAudit.q_pilot_positive

theorem sourceNormalization
    (gapAudit : Audit gap) :
    package.preLedger.normalization :=
  gapAudit.source_normalization

def theorem311Subclaims
    (gapAudit : Audit gap) :
    IUTStage1Theorem311Subclaims package :=
  { algorithm_output_certified := gapAudit.theorem311AlgorithmCertified,
    hodge_theater_she_alignment := gapAudit.sheAlignment }

def theorem311StructuredInputs
    (gapAudit : Audit gap) :
    IUTStage1Theorem311StructuredInputs package :=
  { preledger_audit := package.preLedger.audit,
    theorem311_subclaims := gapAudit.theorem311Subclaims }

theorem theorem311StructuredInputs_subclaims
    (gapAudit : Audit gap) :
    gapAudit.theorem311StructuredInputs.theorem311Subclaims =
      gapAudit.theorem311Subclaims :=
  rfl

def sideConditions
    (gapAudit : Audit gap) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := gapAudit.qPilotPositive,
    source_normalization := gapAudit.sourceNormalization }

def sideConditionHypotheses
    (gapAudit : Audit gap) :
    IUTStage1SourceSideConditionHypotheses package :=
  IUTStage1SourceSideConditionHypotheses.ofSideConditions
    gapAudit.sideConditions

def toSourceObligations
    (gapAudit : Audit gap) :
    IUTStage1SourceObligations package :=
  { algorithm_certified := gapAudit.theorem311AlgorithmCertified,
    she_arrow_matches_certificate := gapAudit.sheAlignment,
    q_pilot_positive := gapAudit.qPilotPositive,
    normalization := gapAudit.sourceNormalization }

theorem toSourceObligations_eq_subclaimsAndSideConditions
    (gapAudit : Audit gap) :
    gapAudit.toSourceObligations =
      IUTStage1SourceObligations.ofSubclaimsAndSideConditions
        gapAudit.theorem311Subclaims gapAudit.sideConditions :=
  rfl

theorem toSourceObligations_eq_gap
    (gapAudit : Audit gap) :
    gapAudit.toSourceObligations = gap.toSourceObligations :=
  Subsingleton.elim _ _

theorem canonical_toSourceObligations
    (gap : IUTStage1SourceObligationGap package) :
    (gap.audit).toSourceObligations = gap.toSourceObligations :=
  Subsingleton.elim _ _

end Audit

end IUTStage1SourceObligationGap

namespace IUTStage1SourceObligations

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}

theorem algorithmCertified
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.output.Certified :=
  obligations.algorithm_certified

theorem sheArrowMatchesCertificate
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  obligations.she_arrow_matches_certificate

theorem qPilotPositive
    (obligations : IUTStage1SourceObligations package) :
    0 < -package.preLedger.qSigned :=
  obligations.q_pilot_positive

theorem sourceNormalization
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.normalization :=
  obligations.normalization

def toLedgerPromotionObligations
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.LedgerPromotionObligations :=
  { certified := obligations.algorithmCertified,
    she_matches_certificate := obligations.sheArrowMatchesCertificate,
    q_positive := obligations.qPilotPositive,
    normalization_proof := obligations.sourceNormalization }

end IUTStage1SourceObligations

namespace IUTStage1SourcePackage

variable {source target : Copy} {index : Type u}

def promotedLedger
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    SourceObligationLedger
      package.preLedger.output
      package.preLedger.measure
      package.preLedger.thetaSigned
      package.preLedger.qSigned
      package.preLedger.normalization :=
  package.preLedger.promotedLedger obligations.toLedgerPromotionObligations

def promotedProvider
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    IUTSourceObligationProvider
      package.preLedger.output
      package.preLedger.measure
      package.preLedger.thetaSigned
      package.preLedger.qSigned
      package.preLedger.normalization :=
  package.preLedger.promotedProvider obligations.toLedgerPromotionObligations

theorem promotedProvider_ledger
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.promotedProvider obligations).ledger =
      package.promotedLedger obligations :=
  package.preLedger.promotedProvider_ledger obligations.toLedgerPromotionObligations

def comparisonPayloadInputs
    (package : IUTStage1SourcePackage source target index) :
    package.preLedger.ComparisonPayloadInputs :=
  package.preLedger.comparisonPayloadInputs

theorem comparisonPayloadInputs_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  package.comparisonPayloadInputs.qSignedLeThetaSigned

theorem comparisonPayloadInputs_thetaChartTrivial
    (package : IUTStage1SourcePackage source target index) :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget :=
  package.comparisonPayloadInputs.thetaChartTrivial

theorem comparisonPayloadInputs_qCharted
    (package : IUTStage1SourcePackage source target index) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord =
      package.preLedger.qSigned :=
  package.comparisonPayloadInputs.qCharted

theorem comparisonPayloadInputs_thetaCharted
    (package : IUTStage1SourcePackage source target index) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  package.comparisonPayloadInputs.thetaCharted

theorem comparisonPayloadInputs_chosenHolds
    (package : IUTStage1SourcePackage source target index) :
    package.preLedger.chosenOutput.comparison.Holds
      package.preLedger.qValue.qPoint :=
  package.comparisonPayloadInputs.chosenHolds

theorem comparisonPayloadInputs_qSigned_le_targetSigned
    (package : IUTStage1SourcePackage source target index) :
    package.preLedger.qSigned <=
      package.preLedger.targetVolume.targetSigned :=
  package.comparisonPayloadInputs.qSignedLeTargetSigned

theorem comparisonPayloadInputs_targetSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  package.comparisonPayloadInputs.targetSignedLeThetaSigned

def comparisonDataFromPayloadInputs
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    Corollary312ComparisonData :=
  package.comparisonPayloadInputs.comparisonData obligations.qPilotPositive

theorem comparisonDataFromPayloadInputs_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonDataFromPayloadInputs obligations).thetaSigned =
      package.preLedger.thetaSigned :=
  rfl

theorem comparisonDataFromPayloadInputs_qSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonDataFromPayloadInputs obligations).qSigned =
      package.preLedger.qSigned :=
  rfl

theorem comparisonDataFromPayloadInputs_corollary312
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  package.comparisonPayloadInputs.comparisonData_corollary312
    obligations.qPilotPositive

def comparisonData
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    Corollary312ComparisonData :=
  (package.promotedProvider obligations).comparisonData

theorem comparisonDataFromPayloadInputs_eq_comparisonData
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    package.comparisonDataFromPayloadInputs obligations =
      package.comparisonData obligations := by
  simp [comparisonDataFromPayloadInputs, comparisonData,
    IUTSourceObligationProvider.comparisonData, SourceObligationLedger.comparisonData,
    IUTStage1PreLedgerData.ComparisonPayloadInputs.comparisonData]

theorem comparisonDataFromPayloadInputs_stage1Comparison_eq
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonDataFromPayloadInputs obligations).stage1Comparison =
      (package.comparisonData obligations).stage1Comparison := by
  rw [package.comparisonDataFromPayloadInputs_eq_comparisonData obligations]

theorem comparisonDataFromPayloadInputs_corollary312_eq
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonDataFromPayloadInputs obligations).corollary312 =
      (package.comparisonData obligations).corollary312 :=
  Subsingleton.elim _ _

def auditedComparisonSourceObligations
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceObligations package :=
  IUTStage1SourceObligations.ofStructuredInputsAndSideConditions
    bundle.inputs sideConditions

theorem auditedComparisonData_eq_payloadInputs
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    bundle.auditedComparisonData sideConditions =
      package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations
          bundle sideConditions) := by
  simp [IUTStage1Theorem311StructuredInputsWithSHE.auditedComparisonData,
    IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData,
    IUTStage1SourcePackage.comparisonDataFromPayloadInputs,
    IUTStage1PreLedgerData.ComparisonPayloadInputs.comparisonData]

theorem auditedComparisonData_stage1Comparison_eq_payloadInputs
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    (bundle.auditedComparisonData sideConditions).stage1Comparison =
      (package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations
          bundle sideConditions)).stage1Comparison := by
  rw [package.auditedComparisonData_eq_payloadInputs bundle sideConditions]

/--
Public-audit view exposed through the audited Theorem 3.11 route.

This is a consistency wrapper, not a new endpoint. It keeps the signed payload
boundary and the equality with the existing payload-input route visible while
reusing `Corollary312ComparisonData.publicAudit`.
-/
structure AuditedPublicAudit
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  signed_payload_boundary :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions
  comparison_data_eq_payload_inputs :
    bundle.auditedComparisonData sideConditions =
      package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations bundle sideConditions)
  q_signed_le_theta :
    (bundle.auditedComparisonData sideConditions).qSigned <=
      (bundle.auditedComparisonData sideConditions).thetaSigned
  corollary312 :
    Corollary312Inequality
      (bundle.auditedComparisonData sideConditions).thetaPilot
      (bundle.auditedComparisonData sideConditions).qPilot
  stage_recovers_q_signed_le_theta :
    corollary312_from_stage1_comparison
        (bundle.auditedComparisonData sideConditions).stage1Comparison =
      corollary312_of_signed_le
        (bundle.auditedComparisonData
          sideConditions).qSigned_le_thetaSigned
  stage_comparison_eq_payload_inputs :
    (bundle.auditedComparisonData sideConditions).stage1Comparison =
      (package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations
          bundle sideConditions)).stage1Comparison
  theta_chart_trivial :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned
  theta_charted :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned
  source_normalization : package.preLedger.normalization
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace AuditedPublicAudit

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedPublicAudit package bundle sideConditions :=
  { signed_payload_boundary :=
      bundle.auditedSignedPayloadBoundary sideConditions,
    comparison_data_eq_payload_inputs :=
      package.auditedComparisonData_eq_payloadInputs bundle sideConditions,
    q_signed_le_theta :=
      (bundle.auditedComparisonData sideConditions).publicAudit_qSigned_le_thetaSigned,
    corollary312 :=
      (bundle.auditedComparisonData sideConditions).publicAudit_corollary312,
    stage_recovers_q_signed_le_theta :=
      (bundle.auditedComparisonData
        sideConditions).publicAudit_stage1Comparison_recovers,
    stage_comparison_eq_payload_inputs :=
      package.auditedComparisonData_stage1Comparison_eq_payloadInputs
        bundle sideConditions,
    theta_chart_trivial :=
      (bundle.auditedSignedPayloadBoundary sideConditions).thetaChartTrivial,
    q_charted :=
      (bundle.auditedSignedPayloadBoundary sideConditions).qCharted,
    theta_charted :=
      (bundle.auditedSignedPayloadBoundary sideConditions).thetaCharted,
    source_normalization :=
      (bundle.auditedSignedPayloadBoundary sideConditions).sourceNormalization,
    histories_not_identified :=
      (bundle.auditedSignedPayloadBoundary
        sideConditions).domainHistory_ne_codomainHistory }

theorem qSigned_le_thetaSigned
    (audit : AuditedPublicAudit package bundle sideConditions) :
    (bundle.auditedComparisonData sideConditions).qSigned <=
      (bundle.auditedComparisonData sideConditions).thetaSigned :=
  audit.q_signed_le_theta

theorem corollary312Endpoint
    (audit : AuditedPublicAudit package bundle sideConditions) :
    Corollary312Inequality
      (bundle.auditedComparisonData sideConditions).thetaPilot
      (bundle.auditedComparisonData sideConditions).qPilot :=
  audit.corollary312

theorem publicAudit
    (audit : AuditedPublicAudit package bundle sideConditions) :
    (bundle.auditedComparisonData sideConditions).qSigned <=
        (bundle.auditedComparisonData sideConditions).thetaSigned ∧
      Corollary312Inequality
        (bundle.auditedComparisonData sideConditions).thetaPilot
        (bundle.auditedComparisonData sideConditions).qPilot ∧
      corollary312_from_stage1_comparison
          (bundle.auditedComparisonData sideConditions).stage1Comparison =
        corollary312_of_signed_le
          (bundle.auditedComparisonData
            sideConditions).qSigned_le_thetaSigned :=
  ⟨audit.qSigned_le_thetaSigned, audit.corollary312Endpoint,
    audit.stage_recovers_q_signed_le_theta⟩

theorem comparisonDataEqPayloadInputs
    (audit : AuditedPublicAudit package bundle sideConditions) :
    bundle.auditedComparisonData sideConditions =
      package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations bundle sideConditions) :=
  audit.comparison_data_eq_payload_inputs

theorem sourceNormalization
    (audit : AuditedPublicAudit package bundle sideConditions) :
    package.preLedger.normalization :=
  audit.source_normalization

theorem thetaChartTrivial
    (audit : AuditedPublicAudit package bundle sideConditions) :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget :=
  audit.theta_chart_trivial

theorem qCharted
    (audit : AuditedPublicAudit package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned :=
  audit.q_charted

theorem thetaCharted
    (audit : AuditedPublicAudit package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  audit.theta_charted

theorem domainHistory_ne_codomainHistory
    (audit : AuditedPublicAudit package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  audit.histories_not_identified

end AuditedPublicAudit

theorem auditedPublicAudit
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedPublicAudit package bundle sideConditions :=
  AuditedPublicAudit.ofStructuredInputsWithSHE bundle sideConditions

/--
Audit object pairing the real-line chart readings with the non-identification
of Hodge-theater histories.

This is not a new comparison endpoint. It records the discipline needed around
the final common-target reading: q and Theta are charted into the target real
copy, while the domain and codomain Hodge-theater histories remain distinct.
-/
structure AuditedChartHistoryDiscipline
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  public_audit : AuditedPublicAudit package bundle sideConditions
  theta_chart_trivial :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned
  theta_charted :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned
  common_container_context_matches :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace AuditedChartHistoryDiscipline

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedChartHistoryDiscipline package bundle sideConditions :=
  { public_audit := package.auditedPublicAudit bundle sideConditions,
    theta_chart_trivial :=
      (package.auditedPublicAudit bundle sideConditions).thetaChartTrivial,
    q_charted := (package.auditedPublicAudit bundle sideConditions).qCharted,
    theta_charted :=
      (package.auditedPublicAudit bundle sideConditions).thetaCharted,
    common_container_context_matches := bundle.commonContainerContextMatches,
    histories_not_identified := bundle.domainHistory_ne_codomainHistory }

theorem publicAudit
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    AuditedPublicAudit package bundle sideConditions :=
  discipline.public_audit

theorem qCharted
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned :=
  discipline.q_charted

theorem thetaCharted
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  discipline.theta_charted

theorem commonContainerContextMatches
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext :=
  discipline.common_container_context_matches

theorem domainHistory_ne_codomainHistory
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  discipline.histories_not_identified

end AuditedChartHistoryDiscipline

theorem auditedChartHistoryDiscipline
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedChartHistoryDiscipline package bundle sideConditions :=
  AuditedChartHistoryDiscipline.ofStructuredInputsWithSHE bundle sideConditions

/--
Semantic wrapper for the allowed chart readings and the forbidden
Hodge-history identification.

The allowed operations are the q- and Theta-side readings through the named
real-comparison chart. The forbidden operation is identifying the domain and
codomain Hodge-theater histories. This record is derived from
`AuditedChartHistoryDiscipline`; it does not add new assumptions.
-/
structure AuditedAllowedChartTransport
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  chart_history_discipline :
    AuditedChartHistoryDiscipline package bundle sideConditions
  chart_transport_discipline :
    package.preLedger.chartedContainer.chart.TransportDiscipline
  allowed_q_to_target_reading :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned
  allowed_theta_to_target_reading :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned
  theta_target_transport_trivial :
    Transport.TrivialMonodromy
      package.preLedger.chartedContainer.chart.thetaToTarget
  forbidden_history_identification :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace AuditedAllowedChartTransport

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofChartHistoryDiscipline
    (discipline :
      AuditedChartHistoryDiscipline package bundle sideConditions) :
    AuditedAllowedChartTransport package bundle sideConditions :=
  { chart_history_discipline := discipline,
    chart_transport_discipline :=
      package.preLedger.chartedContainer.chart.transportDiscipline,
    allowed_q_to_target_reading := discipline.qCharted,
    allowed_theta_to_target_reading := discipline.thetaCharted,
    theta_target_transport_trivial := discipline.publicAudit.thetaChartTrivial,
    forbidden_history_identification :=
      discipline.domainHistory_ne_codomainHistory }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedAllowedChartTransport package bundle sideConditions :=
  ofChartHistoryDiscipline
    (package.auditedChartHistoryDiscipline bundle sideConditions)

theorem chartHistoryDiscipline
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    AuditedChartHistoryDiscipline package bundle sideConditions :=
  transport.chart_history_discipline

theorem chartTransportDiscipline
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    package.preLedger.chartedContainer.chart.TransportDiscipline :=
  transport.chart_transport_discipline

theorem qToTargetAllowedAtChart
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    package.preLedger.chartedContainer.chart.QToTargetAllowedReading :=
  transport.chartTransportDiscipline.q_to_target_allowed

theorem thetaToTargetAllowedAtChart
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    package.preLedger.chartedContainer.chart.ThetaToTargetAllowedReading :=
  transport.chartTransportDiscipline.theta_to_target_allowed

theorem allowedQToTargetReading
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned :=
  transport.allowed_q_to_target_reading

theorem allowedThetaToTargetReading
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  transport.allowed_theta_to_target_reading

theorem forbiddenHistoryIdentification
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  transport.forbidden_history_identification

end AuditedAllowedChartTransport

theorem auditedAllowedChartTransport
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedAllowedChartTransport package bundle sideConditions :=
  AuditedAllowedChartTransport.ofStructuredInputsWithSHE bundle sideConditions

/--
Audit object tying the q-pilot sign condition to the charted q-side reading.

The sign condition in the final payload is about `preLedger.qSigned`; this
record keeps the proof that `qSigned` is the real obtained by applying the
q-to-target chart to the q-side point.
-/
structure AuditedQPilotChartSign
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  allowed_chart_transport :
    AuditedAllowedChartTransport package bundle sideConditions
  q_charted :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned
  q_pilot_positive : 0 < -package.preLedger.qSigned
  charted_q_pilot_positive :
    0 < -
      (Transport.map package.preLedger.chartedContainer.chart.qToTarget
        package.preLedger.qValue.qPoint).coord

namespace AuditedQPilotChartSign

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofAllowedChartTransport
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    AuditedQPilotChartSign package bundle sideConditions :=
  { allowed_chart_transport := transport,
    q_charted := transport.allowedQToTargetReading,
    q_pilot_positive := sideConditions.qPilotPositive,
    charted_q_pilot_positive := by
      rw [transport.allowedQToTargetReading]
      exact sideConditions.qPilotPositive }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedQPilotChartSign package bundle sideConditions :=
  ofAllowedChartTransport
    (package.auditedAllowedChartTransport bundle sideConditions)

theorem allowedChartTransport
    (audit : AuditedQPilotChartSign package bundle sideConditions) :
    AuditedAllowedChartTransport package bundle sideConditions :=
  audit.allowed_chart_transport

theorem qCharted
    (audit : AuditedQPilotChartSign package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord = package.preLedger.qSigned :=
  audit.q_charted

theorem qPilotPositive
    (audit : AuditedQPilotChartSign package bundle sideConditions) :
    0 < -package.preLedger.qSigned :=
  audit.q_pilot_positive

theorem chartedQPilotPositive
    (audit : AuditedQPilotChartSign package bundle sideConditions) :
    0 < -
      (Transport.map package.preLedger.chartedContainer.chart.qToTarget
        package.preLedger.qValue.qPoint).coord :=
  audit.charted_q_pilot_positive

end AuditedQPilotChartSign

theorem auditedQPilotChartSign
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedQPilotChartSign package bundle sideConditions :=
  AuditedQPilotChartSign.ofStructuredInputsWithSHE bundle sideConditions

/--
Audit object tying the Theta-side target bound to the charted Theta reading.

The HDD-after-SHE route bounds the chosen target volume by `thetaSigned`; this
record keeps the proof that `thetaSigned` is the real obtained from the
Theta-side charted point.
-/
structure AuditedThetaChartBound
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  allowed_chart_transport :
    AuditedAllowedChartTransport package bundle sideConditions
  hdd_she_bound :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle
  theta_charted :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned
  chosen_target_volume_le_theta :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned
  chosen_target_volume_le_charted_theta :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord

namespace AuditedThetaChartBound

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofAllowedChartTransport
    (transport :
      AuditedAllowedChartTransport package bundle sideConditions) :
    AuditedThetaChartBound package bundle sideConditions :=
  { allowed_chart_transport := transport,
    hdd_she_bound := bundle.auditedHDDSHEBound,
    theta_charted := transport.allowedThetaToTargetReading,
    chosen_target_volume_le_theta :=
      bundle.auditedHDDSHEBound.chosenTargetVolume_le_theta,
    chosen_target_volume_le_charted_theta := by
      rw [transport.allowedThetaToTargetReading]
      exact bundle.auditedHDDSHEBound.chosenTargetVolume_le_theta }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedThetaChartBound package bundle sideConditions :=
  ofAllowedChartTransport
    (package.auditedAllowedChartTransport bundle sideConditions)

theorem allowedChartTransport
    (audit : AuditedThetaChartBound package bundle sideConditions) :
    AuditedAllowedChartTransport package bundle sideConditions :=
  audit.allowed_chart_transport

theorem hddSHEBound
    (audit : AuditedThetaChartBound package bundle sideConditions) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  audit.hdd_she_bound

theorem thetaCharted
    (audit : AuditedThetaChartBound package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      package.preLedger.thetaSigned :=
  audit.theta_charted

theorem chosenTargetVolume_le_theta
    (audit : AuditedThetaChartBound package bundle sideConditions) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned :=
  audit.chosen_target_volume_le_theta

theorem chosenTargetVolume_le_chartedTheta
    (audit : AuditedThetaChartBound package bundle sideConditions) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord :=
  audit.chosen_target_volume_le_charted_theta

end AuditedThetaChartBound

theorem auditedThetaChartBound
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedThetaChartBound package bundle sideConditions :=
  AuditedThetaChartBound.ofStructuredInputsWithSHE bundle sideConditions

/--
Audit object for the final inequality stated directly between charted q and
charted Theta readings.

This is the charted version of the raw `qSigned <= thetaSigned` comparison.
It keeps both chart equations in the proof boundary.
-/
structure AuditedChartedComparisonBoundary
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  q_pilot_chart_sign :
    AuditedQPilotChartSign package bundle sideConditions
  theta_chart_bound :
    AuditedThetaChartBound package bundle sideConditions
  preledger_charted_chain :
    package.preLedger.ChartedComparisonChain
  raw_inequality :
    IUTStage1Theorem311AuditedRawInequality package bundle
  q_signed_le_theta :
    package.preLedger.qSigned <= package.preLedger.thetaSigned
  charted_q_le_charted_theta :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord

namespace AuditedChartedComparisonBoundary

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofChartAudits
    (qAudit : AuditedQPilotChartSign package bundle sideConditions)
    (thetaAudit : AuditedThetaChartBound package bundle sideConditions) :
    AuditedChartedComparisonBoundary package bundle sideConditions :=
  { q_pilot_chart_sign := qAudit,
    theta_chart_bound := thetaAudit,
    preledger_charted_chain := package.preLedger.chartedComparisonChain,
    raw_inequality := bundle.auditedRawInequality,
    q_signed_le_theta := bundle.auditedRawInequality.qSigned_le_thetaSigned,
    charted_q_le_charted_theta :=
      package.preLedger.chartedComparisonChain.chartedQ_le_chartedTheta }

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedChartedComparisonBoundary package bundle sideConditions :=
  ofChartAudits
    (package.auditedQPilotChartSign bundle sideConditions)
    (package.auditedThetaChartBound bundle sideConditions)

theorem qPilotChartSign
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    AuditedQPilotChartSign package bundle sideConditions :=
  boundary.q_pilot_chart_sign

theorem thetaChartBound
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    AuditedThetaChartBound package bundle sideConditions :=
  boundary.theta_chart_bound

theorem hddSHEBound
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  boundary.theta_chart_bound.hddSHEBound

theorem hddSHECommonContainerCompatibility
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE :=
  boundary.hddSHEBound.commonContainerCompatibility

theorem hddSHECommonContainerBoundAudit
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.BoundAudit
      package.preLedger.certificate :=
  boundary.hddSHEBound.commonContainerBoundAudit

theorem hddSHEDecompositionAudit
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.hddShe.DecompositionAudit
      package.preLedger.certificate :=
  boundary.hddSHEBound.hddSHEDecompositionAudit

theorem hddDecompositionAudit
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.DecompositionAudit
      package.preLedger.certificate :=
  boundary.hddSHEBound.hddDecompositionAudit

theorem hullDetBoundAudit
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge.BoundAudit
      package.preLedger.certificate :=
  boundary.hddSHEBound.hullDetBoundAudit

theorem hddSHESHEArrowMatchesContext
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      bundle.structuredSHE.context.sheDatum :=
  boundary.hddSHEBound.sheArrowMatchesContext

theorem hddSHESHEDatumMatchesCertificate
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    bundle.structuredSHE.context.sheDatum =
      package.preLedger.certificate.she :=
  boundary.hddSHEBound.sheDatumMatchesCertificate

theorem hddSHESHEArrowDatumMatchesCertificate
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  boundary.hddSHEBound.sheArrowDatumMatchesCertificate

theorem hddSHECommonContainerContextMatches
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.commonContainer.context =
      bundle.structuredSHE.context.sharedContext :=
  boundary.hddSHEBound.commonContainerContextMatches

theorem hddSHEQPilotTheater_eq_codomain
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    bundle.structuredSHE.context.qPilotStructure.theater =
      bundle.structuredSHE.context.codomainStructure.theater :=
  boundary.hddSHEBound.qPilotTheater_eq_codomain

theorem hddSHEThetaPilotTheater_eq_domain
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    bundle.structuredSHE.context.thetaPilotStructure.theater =
      bundle.structuredSHE.context.domainStructure.theater :=
  boundary.hddSHEBound.thetaPilotTheater_eq_domain

theorem hddSHELocalExpressionValid
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    bundle.structuredSHE.context.simultaneousExpression.AllLocalValid :=
  boundary.hddSHEBound.localExpressionValid

theorem hddSHEChosenTargetVolume_le_theta
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned :=
  boundary.hddSHEBound.chosenTargetVolume_le_theta

theorem hddSHEAllTargetsAtMost_theta
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  boundary.hddSHEBound.allTargetsAtMost_theta

theorem hddSHEDomainHistory_ne_codomainHistory
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  boundary.hddSHEBound.domainHistory_ne_codomainHistory

theorem preLedgerChartedChain
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.ChartedComparisonChain :=
  boundary.preledger_charted_chain

theorem qChartTransport_eq_comparisonTransport
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chartedContainer.chart.qToTarget =
      package.preLedger.chosenOutput.comparison.transport :=
  boundary.preledger_charted_chain.qChartTransport_eq_comparisonTransport

theorem membershipVolumeControl
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.chosenOutput.comparison.MembershipControlsTargetVolume
      package.preLedger.measure :=
  boundary.preledger_charted_chain.membershipVolumeControl

theorem targetSigned_eq_choiceTargetVolume
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.targetVolume.targetSigned =
      RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) :=
  boundary.preledger_charted_chain.targetSigned_eq_choiceTargetVolume

theorem choiceTargetVolume_le_thetaSigned
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    RegionMeasure.targetVolume package.preLedger.measure
        (package.preLedger.output.comparison
          package.preLedger.chosenOutput.choice) <=
      package.preLedger.thetaSigned :=
  boundary.preledger_charted_chain.choiceTargetVolume_le_thetaSigned

theorem qSigned_le_thetaSigned
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  boundary.q_signed_le_theta

theorem chartedQ_le_chartedTheta
    (boundary :
      AuditedChartedComparisonBoundary package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord :=
  boundary.charted_q_le_charted_theta

end AuditedChartedComparisonBoundary

theorem auditedChartedComparisonBoundary
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedChartedComparisonBoundary package bundle sideConditions :=
  AuditedChartedComparisonBoundary.ofStructuredInputsWithSHE bundle sideConditions

/--
Compact checkpoint summary for the audited structured-SHE route.

The summary is proof-only: it does not create a new endpoint or hide any
construction. It records that the major audited checkpoints are simultaneously
available for the same package, structured-SHE bundle, and side conditions.
-/
structure AuditedStructuredSHERouteSummary
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  has_structured_she :
    QualitativeData.HasStructuredSHE package.preLedger.output.family
  common_container_compatibility :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE
  hdd_she_bound : IUTStage1Theorem311AuditedHDDSHEBound package bundle
  target_volume_middle :
    IUTStage1Theorem311AuditedTargetVolumeMiddle package bundle
  membership_middle :
    IUTStage1Theorem311AuditedMembershipMiddle package bundle
  raw_inequality :
    IUTStage1Theorem311AuditedRawInequality package bundle
  signed_payload_boundary :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions
  charted_comparison_boundary :
    AuditedChartedComparisonBoundary package bundle sideConditions
  public_audit : AuditedPublicAudit package bundle sideConditions
  comparison_data_eq_payload_inputs :
    bundle.auditedComparisonData sideConditions =
      package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations bundle sideConditions)
  q_signed_le_theta :
    (bundle.auditedComparisonData sideConditions).qSigned <=
      (bundle.auditedComparisonData sideConditions).thetaSigned
  source_normalization : package.preLedger.normalization
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace AuditedStructuredSHERouteSummary

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedStructuredSHERouteSummary package bundle sideConditions :=
  { has_structured_she := bundle.hasStructuredSHE_from_context,
    common_container_compatibility := bundle.commonContainerCompatibility,
    hdd_she_bound := bundle.auditedHDDSHEBound,
    target_volume_middle := bundle.auditedTargetVolumeMiddle,
    membership_middle := bundle.auditedMembershipMiddle,
    raw_inequality := bundle.auditedRawInequality,
    signed_payload_boundary :=
      bundle.auditedSignedPayloadBoundary sideConditions,
    charted_comparison_boundary :=
      package.auditedChartedComparisonBoundary bundle sideConditions,
    public_audit := package.auditedPublicAudit bundle sideConditions,
    comparison_data_eq_payload_inputs :=
      package.auditedComparisonData_eq_payloadInputs bundle sideConditions,
    q_signed_le_theta :=
      (package.auditedPublicAudit bundle sideConditions).qSigned_le_thetaSigned,
    source_normalization := sideConditions.sourceNormalization,
    histories_not_identified := bundle.domainHistory_ne_codomainHistory }

theorem publicAudit
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    AuditedPublicAudit package bundle sideConditions :=
  summary.public_audit

theorem signedPayloadBoundary
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions :=
  summary.signed_payload_boundary

theorem rawInequality
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  summary.raw_inequality

theorem chartedComparisonBoundary
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    AuditedChartedComparisonBoundary package bundle sideConditions :=
  summary.charted_comparison_boundary

theorem chartedQ_le_chartedTheta
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord :=
  summary.charted_comparison_boundary.chartedQ_le_chartedTheta

theorem comparisonDataEqPayloadInputs
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    bundle.auditedComparisonData sideConditions =
      package.comparisonDataFromPayloadInputs
        (package.auditedComparisonSourceObligations bundle sideConditions) :=
  summary.comparison_data_eq_payload_inputs

theorem qSigned_le_thetaSigned
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    (bundle.auditedComparisonData sideConditions).qSigned <=
      (bundle.auditedComparisonData sideConditions).thetaSigned :=
  summary.q_signed_le_theta

theorem sourceNormalization
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    package.preLedger.normalization :=
  summary.source_normalization

theorem domainHistory_ne_codomainHistory
    (summary :
      AuditedStructuredSHERouteSummary package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  summary.histories_not_identified

end AuditedStructuredSHERouteSummary

theorem auditedStructuredSHERouteSummary
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedStructuredSHERouteSummary package bundle sideConditions :=
  AuditedStructuredSHERouteSummary.ofStructuredInputsWithSHE
    bundle sideConditions

/--
Named checkpoints for the audited Theorem 3.11 to Corollary 3.12 route.

This record connects the proof-level audit route to the source-facing names used
for the debated transition: the fourth-triangle `HDD o SHE` step, the
simultaneous common-container comparison, and the final signed payload boundary.
-/
structure AuditedTheorem311ToCorollary312Checkpoints
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) : Prop where
  route_summary :
    AuditedStructuredSHERouteSummary package bundle sideConditions
  theorem311_input_label : package.input = package.labels.input
  corollary312_comparison_label :
    package.logVolumeComparison = package.labels.logVolumeComparison
  fourth_triangle_hdd_she :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle
  simultaneous_common_container :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE
  target_volume_chain :
    IUTStage1Theorem311AuditedRawInequality package bundle
  signed_payload_boundary :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions
  charted_comparison_boundary :
    AuditedChartedComparisonBoundary package bundle sideConditions
  public_audit : AuditedPublicAudit package bundle sideConditions
  histories_not_identified :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side

namespace AuditedTheorem311ToCorollary312Checkpoints

variable {package : IUTStage1SourcePackage source target index}
variable {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
variable {sideConditions : IUTStage1SourceSideConditions package}

theorem ofStructuredInputsWithSHE
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedTheorem311ToCorollary312Checkpoints
      package bundle sideConditions :=
  { route_summary :=
      package.auditedStructuredSHERouteSummary bundle sideConditions,
    theorem311_input_label := package.input_matches_labels,
    corollary312_comparison_label :=
      package.logVolumeComparison_matches_labels,
    fourth_triangle_hdd_she := bundle.auditedHDDSHEBound,
    simultaneous_common_container := bundle.commonContainerCompatibility,
    target_volume_chain := bundle.auditedRawInequality,
    signed_payload_boundary :=
      bundle.auditedSignedPayloadBoundary sideConditions,
    charted_comparison_boundary :=
      package.auditedChartedComparisonBoundary bundle sideConditions,
    public_audit := package.auditedPublicAudit bundle sideConditions,
    histories_not_identified := bundle.domainHistory_ne_codomainHistory }

theorem routeSummary
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    AuditedStructuredSHERouteSummary package bundle sideConditions :=
  checkpoints.route_summary

theorem theorem311InputLabel
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    package.input = package.labels.input :=
  checkpoints.theorem311_input_label

theorem corollary312ComparisonLabel
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    package.logVolumeComparison = package.labels.logVolumeComparison :=
  checkpoints.corollary312_comparison_label

theorem fourthTriangleHDDSHE
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    IUTStage1Theorem311AuditedHDDSHEBound package bundle :=
  checkpoints.fourth_triangle_hdd_she

theorem simultaneousCommonContainer
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    IUTStage1Theorem311StructuredSHECommonContainerCompatibility
      package bundle.structuredSHE :=
  checkpoints.simultaneous_common_container

theorem targetVolumeChain
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    IUTStage1Theorem311AuditedRawInequality package bundle :=
  checkpoints.target_volume_chain

theorem signedPayloadBoundary
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    IUTStage1Theorem311AuditedSignedPayloadBoundary
      package bundle sideConditions :=
  checkpoints.signed_payload_boundary

theorem chartedComparisonBoundary
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    AuditedChartedComparisonBoundary package bundle sideConditions :=
  checkpoints.charted_comparison_boundary

theorem chartedQ_le_chartedTheta
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    (Transport.map package.preLedger.chartedContainer.chart.qToTarget
      package.preLedger.qValue.qPoint).coord <=
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord :=
  checkpoints.charted_comparison_boundary.chartedQ_le_chartedTheta

theorem publicAudit
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    AuditedPublicAudit package bundle sideConditions :=
  checkpoints.public_audit

theorem domainHistory_ne_codomainHistory
    (checkpoints :
      AuditedTheorem311ToCorollary312Checkpoints
        package bundle sideConditions) :
    bundle.structuredSHE.context.domainStructure.theater.side ≠
      bundle.structuredSHE.context.codomainStructure.theater.side :=
  checkpoints.histories_not_identified

end AuditedTheorem311ToCorollary312Checkpoints

theorem auditedTheorem311ToCorollary312Checkpoints
    (package : IUTStage1SourcePackage source target index)
    (bundle : IUTStage1Theorem311StructuredInputsWithSHE package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    AuditedTheorem311ToCorollary312Checkpoints
      package bundle sideConditions :=
  AuditedTheorem311ToCorollary312Checkpoints.ofStructuredInputsWithSHE
    bundle sideConditions

theorem comparisonData_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonData obligations).thetaSigned =
      package.preLedger.thetaSigned :=
  rfl

theorem comparisonData_qSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonData obligations).qSigned =
      package.preLedger.qSigned :=
  rfl

theorem comparisonData_stage1Comparison_eq
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonData obligations).stage1Comparison =
      (package.promotedProvider obligations).stage1Comparison :=
  rfl

theorem comparisonData_corollary312_eq
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    (package.comparisonData obligations).corollary312 =
      (package.promotedProvider obligations).corollary312 :=
  rfl

theorem publicAudit
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider obligations).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned) :=
  package.preLedger.publicAudit obligations.toLedgerPromotionObligations

theorem publicAudit_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  (package.publicAudit obligations).1

theorem publicAudit_corollary312
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAudit obligations).2.1

theorem publicAudit_stage1Comparison_recovers_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      corollary312_of_signed_le
        (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned :=
  (package.publicAudit obligations).2.2

def comparisonDataOfHullDetObligations
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    Corollary312ComparisonData :=
  package.comparisonData obligations.toSourceObligations

theorem comparisonDataOfHullDetObligations_eq
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.comparisonDataOfHullDetObligations obligations =
      package.comparisonData obligations.toSourceObligations :=
  rfl

theorem comparisonDataOfHullDetObligations_corollary312
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.comparisonDataOfHullDetObligations obligations).corollary312

theorem publicAuditOfHullDetObligations
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            obligations.toSourceObligations).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            obligations.toSourceObligations).ledger.qSigned_le_thetaSigned) :=
  package.publicAudit obligations.toSourceObligations

theorem publicAuditOfHullDetObligations_corollary312
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAuditOfHullDetObligations obligations).2.1

def obligationsFromParts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceObligations package :=
  IUTStage1SourceObligations.ofSubclaimsAndSideConditions
    subclaims sideConditions

def obligationsFromHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceObligations package :=
  package.obligationsFromParts subclaims hypotheses.toSideConditions

theorem obligationsFromHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.obligationsFromHypotheses subclaims hypotheses =
      package.obligationsFromParts subclaims hypotheses.toSideConditions :=
  rfl

theorem obligationsFromHypotheses_eq_ofHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.obligationsFromHypotheses subclaims hypotheses =
      IUTStage1SourceObligations.ofSubclaimsAndSideConditionHypotheses
        subclaims hypotheses :=
  rfl

def obligationsFromStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    IUTStage1SourceObligations package :=
  IUTStage1SourceObligations.ofStructuredInputsAndSideConditions
    inputs sideConditions

theorem obligationsFromStructuredInputs_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.obligationsFromStructuredInputs inputs sideConditions =
      package.obligationsFromParts
        inputs.theorem311Subclaims sideConditions :=
  rfl

theorem obligationsFromStructuredInputs_eq_ofStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.obligationsFromStructuredInputs inputs sideConditions =
      IUTStage1SourceObligations.ofStructuredInputsAndSideConditions
        inputs sideConditions :=
  rfl

def obligationsFromStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceObligations package :=
  package.obligationsFromStructuredInputs inputs hypotheses.toSideConditions

theorem obligationsFromStructuredHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.obligationsFromStructuredHypotheses inputs hypotheses =
      package.obligationsFromStructuredInputs
        inputs hypotheses.toSideConditions :=
  rfl

theorem obligationsFromStructuredHypotheses_eq_hypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.obligationsFromStructuredHypotheses inputs hypotheses =
      package.obligationsFromHypotheses
        inputs.theorem311Subclaims hypotheses :=
  rfl

theorem obligationsFromStructuredHypotheses_eq_ofStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.obligationsFromStructuredHypotheses inputs hypotheses =
      IUTStage1SourceObligations.ofStructuredInputsAndSideConditionHypotheses
        inputs hypotheses :=
  rfl

theorem publicAuditOfParts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            (package.obligationsFromParts
              subclaims sideConditions)).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            (package.obligationsFromParts
              subclaims sideConditions)).ledger.qSigned_le_thetaSigned) :=
  package.publicAudit (package.obligationsFromParts subclaims sideConditions)

theorem publicAuditOfParts_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  (package.publicAuditOfParts subclaims sideConditions).1

theorem publicAuditOfParts_corollary312
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAuditOfParts subclaims sideConditions).2.1

theorem publicAuditOfParts_stage1Comparison_recovers_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    corollary312_from_stage1_comparison
        (package.promotedProvider
          (package.obligationsFromParts
            subclaims sideConditions)).stage1Comparison =
      corollary312_of_signed_le
      (package.promotedProvider
        (package.obligationsFromParts
          subclaims sideConditions)).ledger.qSigned_le_thetaSigned :=
  (package.publicAuditOfParts subclaims sideConditions).2.2

theorem publicAuditOfHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            (package.obligationsFromHypotheses
              subclaims hypotheses)).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            (package.obligationsFromHypotheses
              subclaims hypotheses)).ledger.qSigned_le_thetaSigned) :=
  package.publicAudit
    (package.obligationsFromHypotheses subclaims hypotheses)

theorem publicAuditOfHypotheses_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  (package.publicAuditOfHypotheses subclaims hypotheses).1

theorem publicAuditOfHypotheses_corollary312
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAuditOfHypotheses subclaims hypotheses).2.1

theorem publicAuditOfHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.publicAuditOfHypotheses subclaims hypotheses =
      package.publicAuditOfParts subclaims hypotheses.toSideConditions :=
  rfl

theorem publicAuditOfStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            (package.obligationsFromStructuredInputs
              inputs sideConditions)).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            (package.obligationsFromStructuredInputs
              inputs sideConditions)).ledger.qSigned_le_thetaSigned) :=
  package.publicAudit
    (package.obligationsFromStructuredInputs inputs sideConditions)

theorem publicAuditOfStructuredInputs_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  (package.publicAuditOfStructuredInputs inputs sideConditions).1

theorem publicAuditOfStructuredInputs_corollary312
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAuditOfStructuredInputs inputs sideConditions).2.1

theorem publicAuditOfStructuredInputs_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.publicAuditOfStructuredInputs inputs sideConditions =
      package.publicAuditOfParts
        inputs.theorem311Subclaims sideConditions :=
  rfl

theorem publicAuditOfStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            (package.obligationsFromStructuredHypotheses
              inputs hypotheses)).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            (package.obligationsFromStructuredHypotheses
              inputs hypotheses)).ledger.qSigned_le_thetaSigned) :=
  package.publicAudit
    (package.obligationsFromStructuredHypotheses inputs hypotheses)

theorem publicAuditOfStructuredHypotheses_qSigned_le_thetaSigned
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  (package.publicAuditOfStructuredHypotheses inputs hypotheses).1

theorem publicAuditOfStructuredHypotheses_corollary312
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  (package.publicAuditOfStructuredHypotheses inputs hypotheses).2.1

theorem publicAuditOfStructuredHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.publicAuditOfStructuredHypotheses inputs hypotheses =
      package.publicAuditOfStructuredInputs
        inputs hypotheses.toSideConditions :=
  rfl

theorem publicAuditOfStructuredHypotheses_eq_hypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.publicAuditOfStructuredHypotheses inputs hypotheses =
      package.publicAuditOfHypotheses
        inputs.theorem311Subclaims hypotheses :=
  rfl

theorem stage1Comparison_recovers_corollary312
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      (package.promotedProvider obligations).ledger.corollary312 :=
  (package.promotedProvider obligations).stage1Comparison_recovers_corollary312

/-- Compact audit checklist for a source-facing Stage 1 package. -/
structure Audit
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) : Prop where
  input_matches_labels : package.input = package.labels.input
  multiradialOutput_matches_labels :
    package.multiradialOutput = package.labels.multiradialOutput
  logVolumeComparison_matches_labels :
    package.logVolumeComparison = package.labels.logVolumeComparison
  thetaPilot_matches_labels : package.thetaPilot = package.labels.thetaPilot
  qPilot_matches_labels : package.qPilot = package.labels.qPilot
  logKummer_matches_labels : package.logKummer = package.labels.logKummer
  indeterminacies_matches_labels :
    package.indeterminacies = package.labels.indeterminacies
  qPilotLogVolume_matches_labels :
    package.qPilotLogVolume = package.labels.qPilotLogVolume
  sourceNormalization_matches_labels :
    package.sourceNormalizationLabel = package.labels.sourceNormalization
  algorithm_certified : package.preLedger.output.Certified
  she_arrow_matches_certificate :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization
  promoted_provider_ledger :
    (package.promotedProvider obligations).ledger =
      package.promotedLedger obligations
  qSigned_le_thetaSigned :
    package.preLedger.qSigned <= package.preLedger.thetaSigned
  corollary312 :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned)
  stage_recovers_qSigned_le_thetaSigned :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      corollary312_of_signed_le
        (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned
  stage_recovers_corollary312 :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      (package.promotedProvider obligations).ledger.corollary312

theorem audit
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    Audit package obligations :=
  { input_matches_labels := package.input_matches_labels,
    multiradialOutput_matches_labels :=
      package.multiradialOutput_matches_labels,
    logVolumeComparison_matches_labels :=
      package.logVolumeComparison_matches_labels,
    thetaPilot_matches_labels := package.thetaPilot_matches_labels,
    qPilot_matches_labels := package.qPilot_matches_labels,
    logKummer_matches_labels := package.logKummer_matches_labels,
    indeterminacies_matches_labels :=
      package.indeterminacies_matches_labels,
    qPilotLogVolume_matches_labels :=
      package.qPilotLogVolume_matches_labels,
    sourceNormalization_matches_labels :=
      package.sourceNormalization_matches_labels,
    algorithm_certified := obligations.algorithmCertified,
    she_arrow_matches_certificate := obligations.sheArrowMatchesCertificate,
    q_pilot_positive := obligations.qPilotPositive,
    normalization := obligations.sourceNormalization,
    promoted_provider_ledger := package.promotedProvider_ledger obligations,
    qSigned_le_thetaSigned :=
      package.publicAudit_qSigned_le_thetaSigned obligations,
    corollary312 := package.publicAudit_corollary312 obligations,
    stage_recovers_qSigned_le_thetaSigned :=
      package.publicAudit_stage1Comparison_recovers_qSigned_le_thetaSigned
        obligations,
    stage_recovers_corollary312 :=
      package.stage1Comparison_recovers_corollary312 obligations }

def ComparisonDataEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) : Prop :=
  ∃ _sourceAudit : Audit package obligations,
    ∃ data : Corollary312ComparisonData,
      data = package.comparisonData obligations ∧
        data.qSigned <= data.thetaSigned ∧
        Corollary312Inequality data.thetaPilot data.qPilot ∧
        corollary312_from_stage1_comparison data.stage1Comparison =
          corollary312_of_signed_le data.qSigned_le_thetaSigned

theorem auditedComparisonDataEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    package.ComparisonDataEndpoint obligations :=
  ⟨package.audit obligations, package.comparisonData obligations, rfl,
    (package.comparisonData obligations).publicAudit⟩

namespace ComparisonDataEndpoint

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceObligations package}

theorem sourceAuditExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ _sourceAudit : Audit package obligations, True := by
  rcases endpoint with ⟨sourceAudit, _data, _hdata, _hle, _hcorollary, _hrecovers⟩
  exact ⟨sourceAudit, trivial⟩

theorem comparisonDataExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ data : Corollary312ComparisonData,
      data = package.comparisonData obligations := by
  rcases endpoint with ⟨_sourceAudit, data, hdata, _hle, _hcorollary, _hrecovers⟩
  exact ⟨data, hdata⟩

theorem qSignedLeThetaSigned
    (endpoint : package.ComparisonDataEndpoint obligations) :
    (package.comparisonData obligations).qSigned <=
      (package.comparisonData obligations).thetaSigned := by
  rcases endpoint with ⟨_sourceAudit, data, hdata, hle, _hcorollary, _hrecovers⟩
  cases hdata
  exact hle

theorem corollary312Endpoint
    (endpoint : package.ComparisonDataEndpoint obligations) :
    Corollary312Inequality
      (package.comparisonData obligations).thetaPilot
      (package.comparisonData obligations).qPilot := by
  rcases endpoint with ⟨_sourceAudit, data, hdata, _hle, hcorollary, _hrecovers⟩
  cases hdata
  exact hcorollary

theorem stageRecoversQSignedLeThetaSigned
    (endpoint : package.ComparisonDataEndpoint obligations) :
    corollary312_from_stage1_comparison
        (package.comparisonData obligations).stage1Comparison =
      corollary312_of_signed_le
        (package.comparisonData obligations).qSigned_le_thetaSigned := by
  rcases endpoint with ⟨_sourceAudit, data, hdata, _hle, _hcorollary, hrecovers⟩
  cases hdata
  exact hrecovers

theorem publicAudit
    (endpoint : package.ComparisonDataEndpoint obligations) :
    (package.comparisonData obligations).qSigned <=
        (package.comparisonData obligations).thetaSigned ∧
      Corollary312Inequality
        (package.comparisonData obligations).thetaPilot
        (package.comparisonData obligations).qPilot ∧
      corollary312_from_stage1_comparison
          (package.comparisonData obligations).stage1Comparison =
        corollary312_of_signed_le
          (package.comparisonData obligations).qSigned_le_thetaSigned :=
  ⟨endpoint.qSignedLeThetaSigned,
    endpoint.corollary312Endpoint,
    endpoint.stageRecoversQSignedLeThetaSigned⟩

theorem publicAudit_eq_comparisonData_publicAudit
    (endpoint : package.ComparisonDataEndpoint obligations) :
    endpoint.publicAudit =
      (package.comparisonData obligations).publicAudit :=
  Subsingleton.elim _ _

theorem publicAudit_eq_package_publicAudit
    (endpoint : package.ComparisonDataEndpoint obligations) :
    endpoint.publicAudit = package.publicAudit obligations :=
  Subsingleton.elim _ _

end ComparisonDataEndpoint

/--
Endpoint audit for the strengthened hull+det obligation route.

This packages the old comparison endpoint together with the source-facing hull
facts, so the public comparison and the union-of-possible-images provenance are
checked at the same boundary.
-/
structure HullDetComparisonEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) : Prop where
  comparison_endpoint :
    package.ComparisonDataEndpoint obligations.toSourceObligations
  public_audit :
    package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
        (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
      (corollary312_from_stage1_comparison
          (package.promotedProvider
            obligations.toSourceObligations).stage1Comparison =
        corollary312_of_signed_le
          (package.promotedProvider
            obligations.toSourceObligations).ledger.qSigned_le_thetaSigned)
  target_union_subset_hull :
    Region.Subset package.preLedger.output.comparisons.targetUnion
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
  determinant_volume_bound :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned
  all_targets_at_most :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned

theorem auditedHullDetComparisonEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.HullDetComparisonEndpoint obligations :=
  { comparison_endpoint :=
      package.auditedComparisonDataEndpoint obligations.toSourceObligations,
    public_audit := package.publicAuditOfHullDetObligations obligations,
    target_union_subset_hull := obligations.targetUnion_subset_hull,
    determinant_volume_bound := obligations.determinantVolumeBound,
    all_targets_at_most := obligations.allTargetsAtMost }

namespace HullDetComparisonEndpoint

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceHullDetObligations package}

theorem corollary312Endpoint
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  endpoint.public_audit.2.1

theorem qSignedLeThetaSigned
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  endpoint.public_audit.1

theorem targetUnion_subset_hull
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    Region.Subset package.preLedger.output.comparisons.targetUnion
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull :=
  endpoint.target_union_subset_hull

theorem determinantVolumeBound
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned :=
  endpoint.determinant_volume_bound

theorem allTargetsAtMost
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    RegionComparisonFamily.AllTargetsAtMost package.preLedger.measure
      package.preLedger.output.comparisons package.preLedger.thetaSigned :=
  endpoint.all_targets_at_most

theorem comparisonEndpointCorollary312
    (endpoint : package.HullDetComparisonEndpoint obligations) :
    Corollary312Inequality
      (package.comparisonData obligations.toSourceObligations).thetaPilot
      (package.comparisonData obligations.toSourceObligations).qPilot :=
  endpoint.comparison_endpoint.corollary312Endpoint

end HullDetComparisonEndpoint

/--
Hull+det endpoint stated in terms of source-level Theta-pilot possible images.

This keeps the source interpretation of `targetUnion` attached to the final
audited comparison endpoint.
-/
structure ThetaPilotHullEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) where
  possible_images : IUTStage1ThetaPilotPossibleImages package
  hull_endpoint : package.HullDetComparisonEndpoint obligations
  possible_images_union_subset_hull :
    Region.Subset possible_images.union
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
  possible_images_union_eq_targetUnion :
    possible_images.union = package.preLedger.output.comparisons.targetUnion

def auditedThetaPilotHullEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceHullDetObligations package) :
    package.ThetaPilotHullEndpoint obligations :=
  let possibleImages := IUTStage1ThetaPilotPossibleImages.ofPackage package
  { possible_images := possibleImages,
    hull_endpoint := package.auditedHullDetComparisonEndpoint obligations,
    possible_images_union_subset_hull :=
      possibleImages.union_subset_target obligations.targetUnion_subset_hull,
    possible_images_union_eq_targetUnion :=
      possibleImages.union_eq_targetUnion }

namespace ThetaPilotHullEndpoint

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceHullDetObligations package}

theorem corollary312Endpoint
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  endpoint.hull_endpoint.corollary312Endpoint

theorem possibleImagesUnion_subset_hull
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    Region.Subset endpoint.possible_images.union
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull :=
  endpoint.possible_images_union_subset_hull

theorem possibleImagesUnion_eq_targetUnion
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    endpoint.possible_images.union =
      package.preLedger.output.comparisons.targetUnion :=
  endpoint.possible_images_union_eq_targetUnion

theorem determinantVolumeBound
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (obligations.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned :=
  endpoint.hull_endpoint.determinantVolumeBound

theorem thetaPilotMatchesPackage
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    endpoint.possible_images.thetaPilot = package.thetaPilot :=
  endpoint.possible_images.thetaPilotMatchesPackage

theorem indeterminaciesMatchPackage
    (endpoint : package.ThetaPilotHullEndpoint obligations) :
    endpoint.possible_images.indeterminacies = package.indeterminacies :=
  endpoint.possible_images.indeterminaciesMatchPackage

end ThetaPilotHullEndpoint

/--
Theorem 3.11 source-facing hull plus determinant constructor.

This record connects the multiradial Theorem 3.11 source record to the
source-level hull/determinant data used in Step (xi-c)--(xi-f).  The algorithmic
certificate and SHE alignment are read from the Theorem 3.11 record; the
remaining inputs are exactly the current side conditions and the supplied
hull/determinant source data.
-/
structure IUTStage1Theorem311HullDetSourceConstructor
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package) where
  hullDetData : IUTStage1SourceHullDetData package
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization

namespace IUTStage1Theorem311HullDetSourceConstructor

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}

theorem canonicalApproximantThetaUnion_eq_targetUnion
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_record :
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet) :
    approximantSource.thetaImageUnion =
      package.preLedger.output.comparisons.targetUnion.toSet := by
  calc
    approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet :=
      theta_union_eq_record
    _ = package.preLedger.output.comparisons.targetUnion.toSet := by
      rw [record.thetaImagesUnion_eq_targetUnion]

def canonicalApproximantHullDetData
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_record :
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  IUTStage1SourceHullDetData.canonicalApproximantHullDetBridgeData
    (package := package)
    operation hullOperation determinantOperation approximantSource
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record) approximantSource theta_union_eq_record)
    approximant_eq_canonical_hull measure_eq_hullLogVolume determinant_bound

def hullDetDataOfCanonicalApproximant
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_record :
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalApproximantHullDetData (record := record)
          operation hullOperation determinantOperation approximantSource
          theta_union_eq_record approximant_eq_canonical_hull
          measure_eq_hullLogVolume determinant_bound) :
    IUTStage1SourceHullDetData package :=
  IUTStage1SourceHullDetData.ofCanonicalApproximant
    (package := package)
    operation hullOperation determinantOperation approximantSource
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record) approximantSource theta_union_eq_record)
    approximant_eq_canonical_hull measure_eq_hullLogVolume determinant_bound
    hbridge

def ofCanonicalApproximant
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_record :
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalApproximantHullDetData (record := record)
          operation hullOperation determinantOperation approximantSource
          theta_union_eq_record approximant_eq_canonical_hull
          measure_eq_hullLogVolume determinant_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  { hullDetData :=
      hullDetDataOfCanonicalApproximant (record := record)
        operation hullOperation determinantOperation approximantSource
        theta_union_eq_record approximant_eq_canonical_hull
        measure_eq_hullLogVolume determinant_bound hbridge,
    q_pilot_positive := q_pilot_positive,
    normalization := normalization }

noncomputable def canonicalWeightedDeterminantApproximantSource
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource) :
    IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
      (Point target) index :=
  IUTStage1SourceHullDetData.canonicalWeightedDeterminantApproximantSource
    hullData possibleThetaImage qPilotRegion approximant
    q_subset_approximant determinantSource compatibility

noncomputable def canonicalWeightedDeterminantHullDetData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_record :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        IUTStage1SourceHullDetData.canonicalWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility
          (canonicalApproximantThetaUnion_eq_targetUnion
            (record := record)
            (canonicalWeightedDeterminantApproximantSource
              hullData possibleThetaImage qPilotRegion approximant
              q_subset_approximant determinantSource compatibility)
            theta_union_eq_record)
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          determinant_bound) :
    IUTStage1SourceHullDetData package :=
  IUTStage1SourceHullDetData.ofCanonicalWeightedDeterminant
    (package := package)
    operation hullOperation determinantOperation hullData
    possibleThetaImage qPilotRegion approximant q_subset_approximant
    determinantSource compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility)
      theta_union_eq_record)
    approximant_eq_canonical_hull measure_eq_hullLogVolume determinant_bound
    hbridge

noncomputable def ofCanonicalWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_record :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        IUTStage1SourceHullDetData.canonicalWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility
          (canonicalApproximantThetaUnion_eq_targetUnion
            (record := record)
            (canonicalWeightedDeterminantApproximantSource
              hullData possibleThetaImage qPilotRegion approximant
              q_subset_approximant determinantSource compatibility)
            theta_union_eq_record)
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          determinant_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  { hullDetData :=
      canonicalWeightedDeterminantHullDetData (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion approximant q_subset_approximant
        determinantSource compatibility theta_union_eq_record
        approximant_eq_canonical_hull measure_eq_hullLogVolume
        determinant_bound hbridge,
    q_pilot_positive := q_pilot_positive,
    normalization := normalization }

noncomputable def canonicalHullWeightedDeterminantApproximantSource
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
    IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
      (Point target) index :=
  IUTStage1SourceHullDetData.canonicalHullWeightedDeterminantApproximantSource
    hullData possibleThetaImage qPilotRegion q_subset_hull
    determinantSource compatibility

noncomputable def canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
    {β : Type v} [Fintype β]
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource) :
    IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
      (Point target) index :=
  IUTStage1SourceHullDetData.canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
    hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
    determinantSource compatibility

noncomputable def canonicalHullWeightedDeterminantHullDetData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  IUTStage1SourceHullDetData.canonicalHullWeightedDeterminantHullDetBridgeData
    (package := package)
    operation hullOperation determinantOperation hullData
    possibleThetaImage qPilotRegion q_subset_hull determinantSource
    compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume determinant_bound

noncomputable def canonicalHullWeightedDeterminantHullDetSourceData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullWeightedDeterminantHullDetData (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_record measure_eq_hullLogVolume
          determinant_bound) :
    IUTStage1SourceHullDetData package :=
  IUTStage1SourceHullDetData.ofCanonicalHullWeightedDeterminant
    (package := package)
    operation hullOperation determinantOperation hullData
    possibleThetaImage qPilotRegion q_subset_hull determinantSource
    compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume determinant_bound hbridge

noncomputable def ofCanonicalHullWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullWeightedDeterminantHullDetData (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_record measure_eq_hullLogVolume
          determinant_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  { hullDetData :=
      canonicalHullWeightedDeterminantHullDetSourceData (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion q_subset_hull determinantSource
        compatibility theta_union_eq_record measure_eq_hullLogVolume
        determinant_bound hbridge,
    q_pilot_positive := q_pilot_positive,
    normalization := normalization }

noncomputable def canonicalHullTensorPowerWeightedDeterminantHullDetData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  IUTStage1SourceHullDetData.canonicalHullTensorPowerWeightedDeterminantHullDetBridgeData
    (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume tensorPower_bound

noncomputable def canonicalHullTensorPowerHullDetDataOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  open IUTStage1SourceHullDetData in
  canonicalHullTensorPowerWeightedDeterminantHullDetBridgeDataOfQSubsetUnion
    (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume tensorPower_bound

noncomputable def canonicalHullTensorPowerWeightedDeterminantHullDetSourceData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetData (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_record measure_eq_hullLogVolume
          tensorPower_bound) :
    IUTStage1SourceHullDetData package :=
  IUTStage1SourceHullDetData.ofCanonicalHullTensorPowerWeightedDeterminant
    (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_hull determinantSource compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume tensorPower_bound hbridge

noncomputable def canonicalHullTensorPowerHullDetSourceDataOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerHullDetDataOfQSubsetUnion (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_record
          measure_eq_hullLogVolume tensorPower_bound) :
    IUTStage1SourceHullDetData package :=
  open IUTStage1SourceHullDetData in
  ofCanonicalHullTensorPowerWeightedDeterminantOfQSubsetUnion
    (package := package)
    operation hullOperation determinantOperation hullData possibleThetaImage
    qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
    (canonicalApproximantThetaUnion_eq_targetUnion
      (record := record)
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility)
      theta_union_eq_record)
    measure_eq_hullLogVolume tensorPower_bound hbridge

noncomputable def ofCanonicalHullTensorPowerWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetData (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_record measure_eq_hullLogVolume
          tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  { hullDetData :=
      canonicalHullTensorPowerWeightedDeterminantHullDetSourceData
        (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion q_subset_hull determinantSource
        compatibility theta_union_eq_record measure_eq_hullLogVolume
        tensorPower_bound hbridge,
    q_pilot_positive := q_pilot_positive,
    normalization := normalization }

noncomputable def ofCanonicalHullTensorPowerOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerHullDetDataOfQSubsetUnion (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_record
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  { hullDetData :=
      canonicalHullTensorPowerHullDetSourceDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility theta_union_eq_record
        measure_eq_hullLogVolume tensorPower_bound hbridge,
    q_pilot_positive := q_pilot_positive,
    normalization := normalization }

def recordThetaPossibleImage
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    (choice : index) : Set (Point target) :=
  (record.thetaPossibleImages.images.region choice).toSet

def recordThetaPossibleImageUnion
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    Set (Point target) :=
  Set.iUnion fun choice : index => recordThetaPossibleImage record choice

theorem recordThetaPossibleImage_union_eq
    (record : IUTStage1Theorem311MultiradialSourceRecord package) :
    recordThetaPossibleImageUnion record =
      record.thetaPossibleImages.union.toSet := by
  ext x
  simp [recordThetaPossibleImageUnion, recordThetaPossibleImage,
    IUTStage1ThetaPilotPossibleImages.union, RegionFamily.union,
    Region.toSet]

theorem qPilotRegion_subset_recordUnion_of_choice
    (choice : index)
    (qPilotRegion : Set (Point target))
    (q_subset_choice :
      qPilotRegion ⊆ recordThetaPossibleImage record choice) :
    qPilotRegion ⊆ recordThetaPossibleImageUnion record := by
  intro x hx
  rw [recordThetaPossibleImage_union_eq record]
  exact
    RegionFamily.choice_subset_union
      record.thetaPossibleImages.images choice x (q_subset_choice hx)

noncomputable def recordCanonicalHullTensorPowerWeightedDeterminantHullDetData
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆
        hullData.hullRegion (recordThetaPossibleImageUnion record))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  canonicalHullTensorPowerWeightedDeterminantHullDetData (record := record)
    operation hullOperation determinantOperation hullData
    (recordThetaPossibleImage record) qPilotRegion q_subset_hull
    determinantSource compatibility
    (recordThetaPossibleImage_union_eq record)
    measure_eq_hullLogVolume tensorPower_bound

noncomputable def recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_recordUnion :
      qPilotRegion ⊆ recordThetaPossibleImageUnion record)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  let q_subset_hull :
      qPilotRegion ⊆
        hullData.hullRegion (recordThetaPossibleImageUnion record) :=
    fun _ hx =>
      hullData.region_subset_hull (recordThetaPossibleImageUnion record)
        (q_subset_recordUnion hx)
  recordCanonicalHullTensorPowerWeightedDeterminantHullDetData
    (record := record)
    operation hullOperation determinantOperation hullData qPilotRegion
    q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
    tensorPower_bound

noncomputable def ofRecordCanonicalHullTensorPowerWeightedDeterminant
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆
        hullData.hullRegion (recordThetaPossibleImageUnion record))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerWeightedDeterminantHullDetData
          (record := record)
          operation hullOperation determinantOperation hullData qPilotRegion
          q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
          tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  ofCanonicalHullTensorPowerWeightedDeterminant (record := record)
    operation hullOperation determinantOperation hullData
    (recordThetaPossibleImage record) qPilotRegion q_subset_hull
    determinantSource compatibility
    (recordThetaPossibleImage_union_eq record)
    measure_eq_hullLogVolume tensorPower_bound hbridge
    q_pilot_positive normalization

noncomputable def ofRecordCanonicalHullTensorPowerOfQSubsetUnion
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_recordUnion :
      qPilotRegion ⊆ recordThetaPossibleImageUnion record)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
          (record := record)
          operation hullOperation determinantOperation hullData qPilotRegion
          q_subset_recordUnion determinantSource compatibility
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  let q_subset_hull :
      qPilotRegion ⊆
        hullData.hullRegion (recordThetaPossibleImageUnion record) :=
    fun _ hx =>
      hullData.region_subset_hull (recordThetaPossibleImageUnion record)
        (q_subset_recordUnion hx)
  ofRecordCanonicalHullTensorPowerWeightedDeterminant (record := record)
    operation hullOperation determinantOperation hullData qPilotRegion
    q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
    tensorPower_bound hbridge q_pilot_positive normalization

def toSourceObligations
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    IUTStage1SourceObligations package :=
  { algorithm_certified := record.bundle.algorithmOutputCertified,
    she_arrow_matches_certificate := record.bundle.hodgeTheaterSHEAlignment,
    q_pilot_positive := constructor.q_pilot_positive,
    normalization := constructor.normalization }

def toHullDetObligations
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    IUTStage1SourceHullDetObligations package :=
  { sourceObligations := constructor.toSourceObligations,
    hullDetData := constructor.hullDetData }

def toThetaPilotHullEndpoint
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    package.ThetaPilotHullEndpoint constructor.toHullDetObligations :=
  package.auditedThetaPilotHullEndpoint constructor.toHullDetObligations

theorem algorithmCertified
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    package.preLedger.output.Certified :=
  constructor.toHullDetObligations.algorithmCertified

theorem sheArrowMatchesCertificate
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  constructor.toHullDetObligations.sheArrowMatchesCertificate

theorem possibleImagesUnion_eq_record
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    constructor.toThetaPilotHullEndpoint.possible_images.union =
      record.thetaPossibleImages.union := by
  calc
    constructor.toThetaPilotHullEndpoint.possible_images.union =
        package.preLedger.output.comparisons.targetUnion :=
      constructor.toThetaPilotHullEndpoint.possibleImagesUnion_eq_targetUnion
    _ = record.thetaPossibleImages.union :=
      record.thetaImagesUnion_eq_targetUnion.symm

theorem recordPossibleImagesUnion_subset_hull
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    Region.Subset record.thetaPossibleImages.union
      (constructor.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull := by
  rw [record.thetaImagesUnion_eq_targetUnion]
  exact constructor.toHullDetObligations.targetUnion_subset_hull

theorem determinantVolumeBound
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    RegionMeasure.HasVolumeAtMost package.preLedger.measure
      (constructor.hullDetData.sourceData.structuredHullDet.applyHull
        package.preLedger.certificate).hull
      package.preLedger.thetaSigned :=
  constructor.toHullDetObligations.determinantVolumeBound

theorem qSigned_le_thetaSigned
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  constructor.toThetaPilotHullEndpoint.hull_endpoint.qSignedLeThetaSigned

theorem corollary312Endpoint
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  constructor.toThetaPilotHullEndpoint.corollary312Endpoint

theorem hullDetSource_endpoint
    (constructor :
      IUTStage1Theorem311HullDetSourceConstructor record) :
    package.preLedger.output.Certified ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        package.preLedger.certificate.she ∧
      constructor.toThetaPilotHullEndpoint.possible_images.union =
        record.thetaPossibleImages.union ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨constructor.algorithmCertified,
    constructor.sheArrowMatchesCertificate,
    constructor.possibleImagesUnion_eq_record,
    constructor.recordPossibleImagesUnion_subset_hull,
    constructor.determinantVolumeBound,
    constructor.qSigned_le_thetaSigned⟩

theorem ofCanonicalApproximant_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (approximantSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow
        (Point target) index)
    (theta_union_eq_record :
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      approximantSource.approximantRegion =
        approximantSource.thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        approximantSource.hullData.toRegionMeasure)
    (determinant_bound :
      approximantSource.determinant.normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalApproximantHullDetData (record := record)
          operation hullOperation determinantOperation approximantSource
          theta_union_eq_record approximant_eq_canonical_hull
          measure_eq_hullLogVolume determinant_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let constructor :=
      ofCanonicalApproximant (record := record)
        operation hullOperation determinantOperation approximantSource
        theta_union_eq_record approximant_eq_canonical_hull
        measure_eq_hullLogVolume determinant_bound hbridge
        q_pilot_positive normalization;
    approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      approximantSource.approximantLogVolume =
        approximantSource.determinant.normalizedLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    intro constructor
    exact
      ⟨theta_union_eq_record,
        canonicalApproximantThetaUnion_eq_targetUnion
          (record := record) approximantSource theta_union_eq_record,
        approximantSource.approximantLogVolume_eq_normalized_determinant,
        constructor.algorithmCertified,
    constructor.recordPossibleImagesUnion_subset_hull,
    constructor.determinantVolumeBound,
    constructor.qSigned_le_thetaSigned⟩

theorem ofCanonicalWeightedDeterminant_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (approximant :
      IUTStage1HullLogVolumeApproximant
        hullData (⋃ i, possibleThetaImage i))
    (q_subset_approximant :
      qPilotRegion ⊆ approximant.approximant)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        approximant determinantSource)
    (theta_union_eq_record :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (approximant_eq_canonical_hull :
      (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).approximantRegion =
        (canonicalWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion approximant
          q_subset_approximant determinantSource compatibility).thetaHull)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (determinant_bound :
      determinantSource.determinantLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        IUTStage1SourceHullDetData.canonicalWeightedDeterminantHullDetBridgeData
          (package := package)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion approximant q_subset_approximant
          determinantSource compatibility
          (canonicalApproximantThetaUnion_eq_targetUnion
            (record := record)
            (canonicalWeightedDeterminantApproximantSource
              hullData possibleThetaImage qPilotRegion approximant
              q_subset_approximant determinantSource compatibility)
            theta_union_eq_record)
          approximant_eq_canonical_hull measure_eq_hullLogVolume
          determinant_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let approximantSource :=
      canonicalWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion approximant
        q_subset_approximant determinantSource compatibility;
    let constructor :=
      ofCanonicalWeightedDeterminant (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion approximant q_subset_approximant
        determinantSource compatibility theta_union_eq_record
        approximant_eq_canonical_hull measure_eq_hullLogVolume
        determinant_bound hbridge q_pilot_positive normalization;
    approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    intro approximantSource constructor
    have htarget :
        approximantSource.thetaImageUnion =
          package.preLedger.output.comparisons.targetUnion.toSet :=
      canonicalApproximantThetaUnion_eq_targetUnion
        (record := record) approximantSource theta_union_eq_record
    have sourceEndpoint :=
      IUTStage1SourceHullDetData.ofCanonicalWeightedDeterminant_endpoint
        (package := package)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion approximant q_subset_approximant
        determinantSource compatibility htarget approximant_eq_canonical_hull
        measure_eq_hullLogVolume determinant_bound hbridge
    exact
      ⟨theta_union_eq_record,
        htarget,
        sourceEndpoint.2.1,
        constructor.algorithmCertified,
        constructor.recordPossibleImagesUnion_subset_hull,
        constructor.determinantVolumeBound,
        constructor.qSigned_le_thetaSigned⟩

theorem ofCanonicalHullTensorPowerWeightedDeterminant_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSource
          hullData possibleThetaImage qPilotRegion q_subset_hull
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerWeightedDeterminantHullDetData
          (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_hull determinantSource
          compatibility theta_union_eq_record measure_eq_hullLogVolume
          tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSource
        hullData possibleThetaImage qPilotRegion q_subset_hull
        determinantSource compatibility;
    let constructor :=
      ofCanonicalHullTensorPowerWeightedDeterminant (record := record)
        operation hullOperation determinantOperation hullData
        possibleThetaImage qPilotRegion q_subset_hull determinantSource
        compatibility theta_union_eq_record measure_eq_hullLogVolume
        tensorPower_bound hbridge q_pilot_positive normalization;
    approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    intro approximantSource constructor
    have htarget :
        approximantSource.thetaImageUnion =
          package.preLedger.output.comparisons.targetUnion.toSet :=
      canonicalApproximantThetaUnion_eq_targetUnion
        (record := record) approximantSource theta_union_eq_record
    have sourceEndpoint :=
      IUTStage1SourceHullDetData.ofCanonicalHullTensorPowerWeightedDeterminant_endpoint
        (package := package)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_hull determinantSource compatibility htarget
        measure_eq_hullLogVolume tensorPower_bound hbridge
    exact
      ⟨theta_union_eq_record,
        htarget,
        sourceEndpoint.1,
        sourceEndpoint.2.1,
        sourceEndpoint.2.2.1,
        constructor.algorithmCertified,
        constructor.recordPossibleImagesUnion_subset_hull,
        constructor.determinantVolumeBound,
        constructor.qSigned_le_thetaSigned⟩

theorem ofCanonicalHullTensorPowerOfQSubsetUnion_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (possibleThetaImage : index -> Set (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_thetaImageUnion :
      qPilotRegion ⊆ ⋃ i, possibleThetaImage i)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (⋃ i, possibleThetaImage i))
        determinantSource)
    (theta_union_eq_record :
      (canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
          hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility).thetaImageUnion =
        record.thetaPossibleImages.union.toSet)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        canonicalHullTensorPowerHullDetDataOfQSubsetUnion (record := record)
          operation hullOperation determinantOperation hullData
          possibleThetaImage qPilotRegion q_subset_thetaImageUnion
          determinantSource compatibility theta_union_eq_record
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion
        hullData possibleThetaImage qPilotRegion q_subset_thetaImageUnion
        determinantSource compatibility;
    let constructor :=
      ofCanonicalHullTensorPowerOfQSubsetUnion (record := record)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_thetaImageUnion determinantSource compatibility
        theta_union_eq_record measure_eq_hullLogVolume tensorPower_bound hbridge
        q_pilot_positive normalization;
    qPilotRegion ⊆ approximantSource.thetaImageUnion ∧
      qPilotRegion ⊆ approximantSource.thetaHull ∧
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    intro approximantSource constructor
    have q_subset_hull :
        qPilotRegion ⊆ hullData.hullRegion (⋃ i, possibleThetaImage i) :=
      fun _ hx =>
        hullData.region_subset_hull (⋃ i, possibleThetaImage i)
          (q_subset_thetaImageUnion hx)
    have directEndpoint :=
      ofCanonicalHullTensorPowerWeightedDeterminant_endpoint
        (record := record)
        operation hullOperation determinantOperation hullData possibleThetaImage
        qPilotRegion q_subset_hull determinantSource compatibility
        (by
          simpa [canonicalHullWeightedDeterminantApproximantSourceOfQSubsetUnion,
            canonicalHullWeightedDeterminantApproximantSource]
            using theta_union_eq_record)
        measure_eq_hullLogVolume tensorPower_bound hbridge
        q_pilot_positive normalization
    exact
      ⟨q_subset_thetaImageUnion,
        approximantSource.qPilotRegion_subset_thetaHull,
        theta_union_eq_record,
        directEndpoint.2.1,
        tensorPower_bound,
        directEndpoint.2.2.2.1,
        directEndpoint.2.2.2.2.1,
        directEndpoint.2.2.2.2.2.1,
        directEndpoint.2.2.2.2.2.2.1,
        directEndpoint.2.2.2.2.2.2.2.1,
        directEndpoint.2.2.2.2.2.2.2.2⟩

theorem ofRecordCanonicalHullTensorPowerWeightedDeterminant_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_hull :
      qPilotRegion ⊆
        hullData.hullRegion (recordThetaPossibleImageUnion record))
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerWeightedDeterminantHullDetData
          (record := record)
          operation hullOperation determinantOperation hullData qPilotRegion
          q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
          tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSource
        hullData (recordThetaPossibleImage record) qPilotRegion q_subset_hull
        determinantSource compatibility;
    let constructor :=
      ofRecordCanonicalHullTensorPowerWeightedDeterminant (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound hbridge q_pilot_positive normalization;
    approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ofCanonicalHullTensorPowerWeightedDeterminant_endpoint
    operation hullOperation determinantOperation hullData
    (recordThetaPossibleImage record) qPilotRegion q_subset_hull
    determinantSource compatibility (recordThetaPossibleImage_union_eq record)
    measure_eq_hullLogVolume tensorPower_bound hbridge q_pilot_positive
    normalization

theorem ofRecordCanonicalHullTensorPowerOfQSubsetUnion_endpoint
    {β : Type v} [Fintype β]
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target))
    (qPilotRegion : Set (Point target))
    (q_subset_recordUnion :
      qPilotRegion ⊆ recordThetaPossibleImageUnion record)
    (determinantSource :
      IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          hullData (recordThetaPossibleImageUnion record))
        determinantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure = hullData.toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hbridge :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
          (record := record)
          operation hullOperation determinantOperation hullData qPilotRegion
          q_subset_recordUnion determinantSource compatibility
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization) :
    let q_subset_hull :
        qPilotRegion ⊆
          hullData.hullRegion (recordThetaPossibleImageUnion record) :=
      fun _ hx =>
        hullData.region_subset_hull (recordThetaPossibleImageUnion record)
          (q_subset_recordUnion hx);
    let approximantSource :=
      canonicalHullWeightedDeterminantApproximantSource
        hullData (recordThetaPossibleImage record) qPilotRegion q_subset_hull
        determinantSource compatibility;
    let constructor :=
      ofRecordCanonicalHullTensorPowerOfQSubsetUnion (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        q_subset_recordUnion determinantSource compatibility
        measure_eq_hullLogVolume tensorPower_bound hbridge q_pilot_positive
        normalization;
    qPilotRegion ⊆ recordThetaPossibleImageUnion record ∧
      qPilotRegion ⊆ approximantSource.thetaHull ∧
      approximantSource.thetaImageUnion =
        record.thetaPossibleImages.union.toSet ∧
      approximantSource.thetaImageUnion =
        package.preLedger.output.comparisons.targetUnion.toSet ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      approximantSource.approximantRegion = approximantSource.thetaHull ∧
      approximantSource.approximantLogVolume =
        determinantSource.determinantLogVolume ∧
      package.preLedger.output.Certified ∧
      Region.Subset record.thetaPossibleImages.union
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (constructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    intro q_subset_hull approximantSource constructor
    have hendpoint :=
      ofRecordCanonicalHullTensorPowerWeightedDeterminant_endpoint
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        q_subset_hull determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound hbridge q_pilot_positive normalization
    exact
      ⟨q_subset_recordUnion,
        approximantSource.qPilotRegion_subset_thetaHull,
        hendpoint.1,
        hendpoint.2.1,
        hendpoint.2.2.1,
        hendpoint.2.2.2.1,
        hendpoint.2.2.2.2.1,
        hendpoint.2.2.2.2.2.1,
        hendpoint.2.2.2.2.2.2.1,
        hendpoint.2.2.2.2.2.2.2.1,
        hendpoint.2.2.2.2.2.2.2.2⟩

end IUTStage1Theorem311HullDetSourceConstructor

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Source-facing holomorphic-hull/determinant boundary for the record-native
Step (xi) Ob4 route.

The fields are the current mathematical payload that still has to be
constructed from the source papers: a holomorphic hull on the Theorem 3.11
possible-image union, q-pilot containment in that union, a weighted determinant
source, tensor-power normalization, and equality with the package's named
hull/determinant bridge.  From this package Lean constructs the existing
Theorem 3.11 hull/determinant constructor.
-/
structure IUTStage1HolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qPilotRegion : Set (Point target)
  q_subset_recordUnion :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
        record
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        q_subset_recordUnion determinantSource compatibility
        measure_eq_hullLogVolume tensorPower_bound
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization

namespace IUTStage1HolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

noncomputable def toHullDetSourceConstructor
    (sourceData :
      IUTStage1HolomorphicHullDeterminantSource (β := β) record) :
    IUTStage1Theorem311HullDetSourceConstructor record :=
  IUTStage1Theorem311HullDetSourceConstructor.ofRecordCanonicalHullTensorPowerOfQSubsetUnion
    (record := record)
    sourceData.operation sourceData.hullOperation
    sourceData.determinantOperation sourceData.hullData
    sourceData.qPilotRegion sourceData.q_subset_recordUnion
    sourceData.determinantSource sourceData.compatibility
    sourceData.measure_eq_hullLogVolume sourceData.tensorPower_bound
    sourceData.hullDetBridge_eq sourceData.q_pilot_positive
    sourceData.normalization

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1HolomorphicHullDeterminantSource (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toHullDetSourceConstructor.qSigned_le_thetaSigned

theorem hullDetSource_endpoint
    (sourceData :
      IUTStage1HolomorphicHullDeterminantSource (β := β) record) :
    package.preLedger.output.Certified ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        package.preLedger.certificate.she ∧
      sourceData.toHullDetSourceConstructor.toThetaPilotHullEndpoint.possible_images.union =
        record.thetaPossibleImages.union ∧
      Region.Subset record.thetaPossibleImages.union
        (sourceData.toHullDetSourceConstructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (sourceData.toHullDetSourceConstructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toHullDetSourceConstructor.hullDetSource_endpoint

theorem source_endpoint
    (sourceData :
      IUTStage1HolomorphicHullDeterminantSource (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_recordUnion,
    sourceData.tensorPower_bound,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1HolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Side-conditioned Step (xi) holomorphic-hull/determinant source.

This is the record-native hull source with q-pilot positivity and source
normalization read from the shared Stage 1 side-condition object.  The
holomorphic hull, possible-image containment, determinant compatibility, and
bridge equality remain the active Step (xi) hull/determinant payload.
-/
structure IUTStage1SideConditionedHolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qPilotRegion : Set (Point target)
  q_subset_recordUnion :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
        record
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        q_subset_recordUnion determinantSource compatibility
        measure_eq_hullLogVolume tensorPower_bound
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1SideConditionedHolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

theorem qPilotPositive
    (sourceData :
      IUTStage1SideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    0 < -package.preLedger.qSigned :=
  sourceData.sideConditions.qPilotPositive

theorem sourceNormalization
    (sourceData :
      IUTStage1SideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.normalization :=
  sourceData.sideConditions.sourceNormalization

noncomputable def toHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1SideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1HolomorphicHullDeterminantSource (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_recordUnion := sourceData.q_subset_recordUnion,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    q_pilot_positive := sourceData.qPilotPositive,
    normalization := sourceData.sourceNormalization }

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1SideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toHolomorphicHullDeterminantSource.qSigned_le_thetaSigned

theorem source_endpoint
    (sourceData :
      IUTStage1SideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_recordUnion,
    sourceData.tensorPower_bound,
    sourceData.qPilotPositive,
    sourceData.sourceNormalization,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1SideConditionedHolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image side-conditioned Step (xi) holomorphic-hull/determinant source.

This refines `IUTStage1SideConditionedHolomorphicHullDeterminantSource` by
fixing the q-pilot region to the possible-image region associated to a chosen
Theorem 3.11 multiradial output.  The containment in the record possible-image
union is then definitional via union introduction, so the source object no
longer carries an arbitrary q-region or a separate `q \subseteq P_rec` proof.
-/
structure IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    Set (Point target) :=
  IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
    record sourceData.qChoice

theorem qPilotRegion_eq_possibleImage
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion =
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record sourceData.qChoice :=
  rfl

theorem q_subset_recordUnion
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
        record :=
  IUTStage1Theorem311HullDetSourceConstructor.qPilotRegion_subset_recordUnion_of_choice
    (record := record)
    sourceData.qChoice sourceData.qPilotRegion (fun _ hx => hx)

noncomputable def toSideConditionedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1SideConditionedHolomorphicHullDeterminantSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_recordUnion := sourceData.q_subset_recordUnion,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    sideConditions := sourceData.sideConditions }

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toSideConditionedHolomorphicHullDeterminantSource
    |>.qSigned_le_thetaSigned

set_option linter.style.longLine false in
/--
Possible-image holomorphic-hull/log-volume Step (xi) audit.

This is the source-level form of the Corollary 3.12 Step (xi) passage from a
chosen Theorem 3.11 possible image to the record possible-image union, then to
the holomorphic hull and its log-volume bound.  It packages the same raw signed
comparison with the side-condition witnesses used by the source object.
-/
theorem holomorphicHullLogVolume_endpoint
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.output.Certified ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        package.preLedger.certificate.she ∧
      sourceData.toSideConditionedHolomorphicHullDeterminantSource.toHolomorphicHullDeterminantSource.toHullDetSourceConstructor.toThetaPilotHullEndpoint.possible_images.union =
        record.thetaPossibleImages.union ∧
      Region.Subset record.thetaPossibleImages.union
        (sourceData.toSideConditionedHolomorphicHullDeterminantSource.toHolomorphicHullDeterminantSource.toHullDetSourceConstructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost package.preLedger.measure
        (sourceData.toSideConditionedHolomorphicHullDeterminantSource.toHolomorphicHullDeterminantSource.toHullDetSourceConstructor.hullDetData.sourceData.structuredHullDet.applyHull
          package.preLedger.certificate).hull
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
      sourceData.qPilotRegion =
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization := by
  have hhull :=
    sourceData.toSideConditionedHolomorphicHullDeterminantSource
      |>.toHolomorphicHullDeterminantSource
      |>.hullDetSource_endpoint
  exact
    ⟨hhull.1,
      hhull.2.1,
      hhull.2.2.1,
      hhull.2.2.2.1,
      hhull.2.2.2.2.1,
      hhull.2.2.2.2.2,
      sourceData.qPilotRegion_eq_possibleImage,
      sourceData.q_subset_recordUnion,
      sourceData.sideConditions.qPilotPositive,
      sourceData.sideConditions.sourceNormalization⟩

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion =
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.qPilotRegion_eq_possibleImage,
    sourceData.q_subset_recordUnion,
    sourceData.tensorPower_bound,
    sourceData.sideConditions.qPilotPositive,
    sourceData.sideConditions.sourceNormalization,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image side-conditioned Step (xi) holomorphic-hull/determinant source
backed by package hull/determinant obligations.

This refines
`IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource`: the
q-pilot region is still definitionally the chosen Theorem 3.11 possible image,
while the package hull/determinant bridge equality, q-pilot positivity, and
normalization are projected from one `IUTStage1SourceHullDetObligations`
object.
-/
structure IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound

namespace IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem qPilotRegion_eq_possibleImage
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
      recordThetaPossibleImage record sourceData.qChoice :=
  rfl

theorem q_subset_recordUnion
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImageUnion record :=
  qPilotRegion_subset_recordUnion_of_choice
    (record := record)
    sourceData.qChoice sourceData.qPilotRegion (fun _ hx => hx)

def sideConditions
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := sourceData.obligations.qPilotPositive,
    source_normalization := sourceData.obligations.normalization }

theorem hullDetBridge_eq_recordCanonical
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        sourceData.operation sourceData.hullOperation
        sourceData.determinantOperation sourceData.hullData
        (recordThetaPossibleImage record sourceData.qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) sourceData.qChoice
          (recordThetaPossibleImage record sourceData.qChoice)
          (fun _ hx => hx))
        sourceData.determinantSource sourceData.compatibility
        sourceData.measure_eq_hullLogVolume sourceData.tensorPower_bound :=
  sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData.trans
    sourceData.obligationsHullDetData_eq_recordCanonical

noncomputable def toPossibleImageSideConditionedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    hullDetBridge_eq := sourceData.hullDetBridge_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toPossibleImageSideConditionedHolomorphicHullDeterminantSource
    |>.qSigned_le_thetaSigned

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.qPilotRegion_eq_possibleImage,
    sourceData.q_subset_recordUnion,
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData,
    sourceData.tensorPower_bound,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image Step (xi) holomorphic-hull/determinant source pinned to a
Theorem 3.11 hull/determinant constructor.

This refines
`IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource`:
the public source still records the determinant payload and the selected
Theorem 3.11 possible image, but it also carries the source constructor whose
`hullDetData` is identified with the ambient obligations object.  The bridge
equality used by downstream routes is then projected through this constructor
boundary.
-/
structure IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData (recordThetaPossibleImageUnion record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  constructor : IUTStage1Theorem311HullDetSourceConstructor record
  obligations : IUTStage1SourceHullDetObligations package
  constructor_hullDetData_eq_obligations :
    constructor.hullDetData = obligations.hullDetData
  constructorHullDetData_eq_recordCanonical :
    constructor.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound

namespace IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem qPilotRegion_eq_possibleImage
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
      recordThetaPossibleImage record sourceData.qChoice :=
  rfl

theorem q_subset_recordUnion
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImageUnion record :=
  qPilotRegion_subset_recordUnion_of_choice
    (record := record)
    sourceData.qChoice sourceData.qPilotRegion (fun _ hx => hx)

theorem obligationsHullDetData_eq_recordCanonical
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    sourceData.obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        sourceData.operation sourceData.hullOperation
        sourceData.determinantOperation sourceData.hullData
        (recordThetaPossibleImage record sourceData.qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) sourceData.qChoice
          (recordThetaPossibleImage record sourceData.qChoice)
          (fun _ hx => hx))
        sourceData.determinantSource sourceData.compatibility
        sourceData.measure_eq_hullLogVolume sourceData.tensorPower_bound := by
  rw [← sourceData.constructor_hullDetData_eq_obligations]
  exact sourceData.constructorHullDetData_eq_recordCanonical

theorem hullDetBridge_eq_constructor
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      sourceData.constructor.hullDetData.bridgeData := by
  exact
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData.trans
      (congrArg (fun data : IUTStage1SourceHullDetData package => data.bridgeData)
        sourceData.constructor_hullDetData_eq_obligations.symm)

noncomputable def toPossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    IUTStage1PossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toPossibleImageSideConditionedHolomorphicHullDeterminantObligationsBackedSource
    |>.qSigned_le_thetaSigned

set_option linter.style.longLine false in
def SourceEndpoint
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) : Prop :=
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      sourceData.constructor.hullDetData = sourceData.obligations.hullDetData ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.constructor.hullDetData.bridgeData ∧
      sourceData.constructor.hullDetData.bridgeData =
        recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
          (record := record)
          sourceData.operation sourceData.hullOperation
          sourceData.determinantOperation sourceData.hullData
          (recordThetaPossibleImage record sourceData.qChoice)
          (qPilotRegion_subset_recordUnion_of_choice
            (record := record) sourceData.qChoice
            (recordThetaPossibleImage record sourceData.qChoice)
            (fun _ hx => hx))
          sourceData.determinantSource sourceData.compatibility
          sourceData.measure_eq_hullLogVolume sourceData.tensorPower_bound ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource
        (β := β) record) :
    SourceEndpoint sourceData :=
  ⟨sourceData.qPilotRegion_eq_possibleImage,
    sourceData.q_subset_recordUnion,
    sourceData.constructor_hullDetData_eq_obligations,
    sourceData.hullDetBridge_eq_constructor,
    sourceData.constructorHullDetData_eq_recordCanonical,
    sourceData.tensorPower_bound,
    sourceData.constructor.q_pilot_positive,
    sourceData.constructor.normalization,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1PossibleImageConstructorPinnedHolomorphicHullDeterminantObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Choice-linked Step (xi) holomorphic-hull/determinant source.

This is a refinement of `IUTStage1HolomorphicHullDeterminantSource` for the
case where the q-pilot region is linked to a named Theorem 3.11 possible-output
choice.  The containment of the q-pilot region in the full possible-image union
is then derived by union introduction, rather than carried as an independent
field.
-/
structure IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  tensorPower_bound :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        determinantSource compatibility measure_eq_hullLogVolume
        tensorPower_bound
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization

namespace IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

theorem q_subset_recordUnion
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
        record :=
  IUTStage1Theorem311HullDetSourceConstructor.qPilotRegion_subset_recordUnion_of_choice
    (record := record)
    sourceData.qChoice sourceData.qPilotRegion sourceData.q_subset_choice

noncomputable def toHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1HolomorphicHullDeterminantSource (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_recordUnion := sourceData.q_subset_recordUnion,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    q_pilot_positive := sourceData.q_pilot_positive,
    normalization := sourceData.normalization }

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toHolomorphicHullDeterminantSource.qSigned_le_thetaSigned

noncomputable def toUpperRayLogVolume
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1HullDetPilotUpperRayLogVolume :=
  IUTStage1HullDetPilotUpperRayLogVolume.ofHolomorphicHull
    sourceData.hullData sourceData.qPilotRegion
    (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
      record)
    (fun _ hx =>
      sourceData.hullData.region_subset_hull
        (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record)
        (sourceData.q_subset_recordUnion hx))
    sourceData.determinantSource.toDeterminantLogVolume
    (by
      simpa [IUTStage1HullLogVolumeApproximant.canonical] using
        sourceData.compatibility.approximant_eq_projected_normalized)

noncomputable def toQPilotTwoComputationLogVolume
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1QPilotTwoComputationLogVolume :=
  { upperRayData := sourceData.toUpperRayLogVolume,
    inputPrimeStripLogVolume :=
      sourceData.hullData.logVolume sourceData.qPilotRegion,
    outputHullLogVolume :=
      sourceData.hullData.logVolume sourceData.qPilotRegion,
    input_eq_q := rfl,
    output_eq_q := rfl }

theorem upperRay_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.toUpperRayLogVolume.qPilotLogVolume =
        sourceData.hullData.logVolume sourceData.qPilotRegion ∧
      sourceData.toUpperRayLogVolume.thetaHullLogVolume =
        sourceData.hullData.logVolume
          (sourceData.hullData.hullRegion
            (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
              record)) ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume ∈
        sourceData.toUpperRayLogVolume.upperRay ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume <=
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume =
        sourceData.toQPilotTwoComputationLogVolume.outputHullLogVolume :=
  ⟨rfl,
    rfl,
    sourceData.toUpperRayLogVolume.qPilot_mem_upperRay,
    by
      simpa [
        IUTStage1ArithmeticVectorBundleWeightedDeterminantSource.toDeterminantLogVolume]
        using sourceData.toUpperRayLogVolume.qPilotLogVolume_le_determinant,
    sourceData.toQPilotTwoComputationLogVolume.input_eq_output⟩

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume ∈
        sourceData.toUpperRayLogVolume.upperRay ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume <=
        sourceData.determinantSource.determinantLogVolume ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_choice,
    sourceData.q_subset_recordUnion,
    sourceData.tensorPower_bound,
    sourceData.upperRay_endpoint.2.2.1,
    sourceData.upperRay_endpoint.2.2.2.1,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Choice-linked Step (xi) source with exact theta/tensor-power normalization.

This strengthens `IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource` by
replacing the carried tensor-power upper bound with the equality identifying
the pre-ledger `thetaSigned` value with the normalized Ob4 tensor-power
log-volume of the weighted determinant source.  The bound consumed by the
existing hull/determinant constructor is then a projection of this equality.
-/
structure IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  thetaSigned_eq_tensorPowerNormalized :
    package.preLedger.thetaSigned =
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        determinantSource compatibility measure_eq_hullLogVolume
        (le_of_eq thetaSigned_eq_tensorPowerNormalized.symm)
  q_pilot_positive : 0 < -package.preLedger.qSigned
  normalization : package.preLedger.normalization

namespace IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

theorem tensorPower_bound
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        sourceData.determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned :=
  le_of_eq sourceData.thetaSigned_eq_tensorPowerNormalized.symm

theorem determinantLogVolume_eq_thetaSigned
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.determinantSource.determinantLogVolume =
      package.preLedger.thetaSigned := by
  calc
    sourceData.determinantSource.determinantLogVolume =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume := by
        exact
          (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_eq
            sourceData.determinantSource).symm
    _ = package.preLedger.thetaSigned :=
        sourceData.thetaSigned_eq_tensorPowerNormalized.symm

noncomputable def toChoiceLinkedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    tensorPower_bound := sourceData.tensorPower_bound,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    q_pilot_positive := sourceData.q_pilot_positive,
    normalization := sourceData.normalization }

noncomputable def toUpperRayLogVolume
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1HullDetPilotUpperRayLogVolume :=
  sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.toUpperRayLogVolume

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.qSigned_le_thetaSigned

theorem exactTheta_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.thetaSigned =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume <=
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.thetaSigned_eq_tensorPowerNormalized,
    sourceData.tensorPower_bound,
    by
      have hUpper :=
        sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.upperRay_endpoint
      exact
        hUpper.2.2.2.1.trans
          (le_of_eq sourceData.determinantLogVolume_eq_thetaSigned),
    sourceData.qSigned_le_thetaSigned⟩

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      package.preLedger.thetaSigned =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume ∈
        sourceData.toUpperRayLogVolume.upperRay ∧
      sourceData.toUpperRayLogVolume.qPilotLogVolume <=
        package.preLedger.thetaSigned ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_choice,
    sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.q_subset_recordUnion,
    sourceData.thetaSigned_eq_tensorPowerNormalized,
    sourceData.tensorPower_bound,
    sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.upperRay_endpoint.2.2.1,
    sourceData.exactTheta_endpoint.2.2.1,
    sourceData.qSigned_le_thetaSigned⟩

end IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Choice-linked exact-theta Step (xi) source with audited side conditions.

This refines
`IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource` by replacing
the loose q-pilot positivity and normalization proof fields with the existing
Stage 1 side-condition object.  It keeps the Step (xi) hull/determinant payload
unchanged, but makes the sign and normalization hypotheses project from the
same source boundary used for ledger promotion.
-/
structure
    IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  thetaSigned_eq_tensorPowerNormalized :
    package.preLedger.thetaSigned =
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume
  hullDetBridge_eq :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        determinantSource compatibility measure_eq_hullLogVolume
        (le_of_eq thetaSigned_eq_tensorPowerNormalized.symm)
  sideConditions : IUTStage1SourceSideConditions package

namespace
    IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

theorem qPilotPositive
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    0 < -package.preLedger.qSigned :=
  sourceData.sideConditions.qPilotPositive

theorem sourceNormalization
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.normalization :=
  sourceData.sideConditions.sourceNormalization

noncomputable def toExactThetaHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1ChoiceLinkedExactThetaHolomorphicHullDeterminantSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_tensorPowerNormalized :=
      sourceData.thetaSigned_eq_tensorPowerNormalized,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    q_pilot_positive := sourceData.qPilotPositive,
    normalization := sourceData.sourceNormalization }

noncomputable def toChoiceLinkedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    IUTStage1ChoiceLinkedHolomorphicHullDeterminantSource
      (β := β) record :=
  sourceData.toExactThetaHolomorphicHullDeterminantSource
    |>.toChoiceLinkedHolomorphicHullDeterminantSource

theorem tensorPower_bound
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
        sourceData.determinantSource).normalizedLogVolume <=
      package.preLedger.thetaSigned :=
  sourceData.toExactThetaHolomorphicHullDeterminantSource.tensorPower_bound

theorem qSigned_le_thetaSigned
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceData.toExactThetaHolomorphicHullDeterminantSource.qSigned_le_thetaSigned

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      package.preLedger.thetaSigned =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume ∧
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_choice,
    sourceData.toChoiceLinkedHolomorphicHullDeterminantSource.q_subset_recordUnion,
    sourceData.thetaSigned_eq_tensorPowerNormalized,
    sourceData.tensorPower_bound,
    sourceData.qPilotPositive,
    sourceData.sourceNormalization,
    sourceData.qSigned_le_thetaSigned⟩

end
  IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Record-native bounded-family hull/determinant Step (xi) source.

The generic bounded-family source in `IUTStage1SourceCore` is indexed by an
arbitrary family of possible regions.  This record specializes that object to
the possible-image family carried by a Theorem 3.11 multiradial source record.
It is the source-facing Ob5 package: the family union, its canonical hull,
the weighted determinant source, and the normalized tensor-power log-volume are
all tied to the same record-level possible-image union.
-/
structure IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource

namespace IUTStage1RecordBoundedFamilyHullDetLogVolumeSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def possibleRegion
    (_sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    index -> Set (Point target) :=
  recordThetaPossibleImage record

def familyUnion
    (_sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImageUnion record

def familyHull
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    Set (Point target) :=
  sourceData.hullData.hullRegion sourceData.familyUnion

def familyHullLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    Real :=
  sourceData.hullData.logVolume sourceData.familyHull

def familyUnionLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    Real :=
  sourceData.hullData.logVolume sourceData.familyUnion

noncomputable def tensorPower
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    IUTStage1NaiveFrobeniusTensorPowerLogVolume :=
  IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
    sourceData.determinantSource

noncomputable def toBoundedFamilyHullDetLogVolumeSource
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    IUTStage1BoundedFamilyHullDetLogVolumeSource
      (Point target) index β :=
  { hullData := sourceData.hullData,
    possibleRegion := recordThetaPossibleImage record,
    determinantSource := sourceData.determinantSource,
    compatibility := by
      simpa [recordThetaPossibleImageUnion] using sourceData.compatibility }

theorem toBoundedFamily_familyUnion
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.toBoundedFamilyHullDetLogVolumeSource.familyUnion =
      sourceData.familyUnion := by
  rfl

theorem toBoundedFamily_familyHull
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.toBoundedFamilyHullDetLogVolumeSource.familyHull =
      sourceData.familyHull := by
  rfl

theorem toBoundedFamily_familyHullLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.toBoundedFamilyHullDetLogVolumeSource.familyHullLogVolume =
      sourceData.familyHullLogVolume := by
  rfl

theorem toBoundedFamily_familyUnionLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.toBoundedFamilyHullDetLogVolumeSource.familyUnionLogVolume =
      sourceData.familyUnionLogVolume := by
  rfl

theorem familyHullLogVolume_eq_normalized
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.familyHullLogVolume =
      sourceData.determinantSource.normalizedLogVolume := by
  simpa [familyHullLogVolume, familyHull, familyUnion] using
    sourceData.compatibility.approximant_eq_weighted_normalized

theorem familyHullLogVolume_eq_determinant
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.familyHullLogVolume =
      sourceData.determinantSource.determinantLogVolume := by
  rw [sourceData.familyHullLogVolume_eq_normalized,
    sourceData.determinantSource.normalizedLogVolume_eq_determinantLogVolume]

theorem familyUnionLogVolume_le_familyHullLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.familyUnionLogVolume <= sourceData.familyHullLogVolume :=
  sourceData.hullData.logVolume_le_hullLogVolume sourceData.familyUnion

theorem tensorPower_normalizedLogVolume_eq_familyHullLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.tensorPower.normalizedLogVolume =
      sourceData.familyHullLogVolume := by
  calc
    sourceData.tensorPower.normalizedLogVolume =
        sourceData.determinantSource.determinantLogVolume := by
      simpa [tensorPower] using
        IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant_normalizedLogVolume_eq
            sourceData.determinantSource
    _ = sourceData.familyHullLogVolume :=
      sourceData.familyHullLogVolume_eq_determinant.symm

theorem tensorPower_bound_of_theta_eq_familyHullLogVolume
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record)
    {thetaSigned : Real}
    (hθ :
      thetaSigned = sourceData.familyHullLogVolume) :
    sourceData.tensorPower.normalizedLogVolume <= thetaSigned :=
  le_of_eq
    (by
      calc
        sourceData.tensorPower.normalizedLogVolume =
            sourceData.familyHullLogVolume :=
          sourceData.tensorPower_normalizedLogVolume_eq_familyHullLogVolume
        _ = thetaSigned := hθ.symm)

theorem source_endpoint
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) :
    sourceData.familyUnion =
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      sourceData.familyHullLogVolume =
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.familyUnionLogVolume <= sourceData.familyHullLogVolume ∧
      sourceData.tensorPower.normalizedLogVolume =
        sourceData.familyHullLogVolume :=
  ⟨rfl, sourceData.familyHullLogVolume_eq_determinant,
    sourceData.familyUnionLogVolume_le_familyHullLogVolume,
    sourceData.tensorPower_normalizedLogVolume_eq_familyHullLogVolume⟩

theorem boundedFamily_endpoint
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record)
    (i j : index)
    (hnei : (recordThetaPossibleImage record i).Nonempty)
    (hnej : (recordThetaPossibleImage record j).Nonempty) :
    recordThetaPossibleImage record i ⊆ sourceData.familyHull ∧
      recordThetaPossibleImage record j ⊆ sourceData.familyHull ∧
      sourceData.toBoundedFamilyHullDetLogVolumeSource.quotientMap ''
          recordThetaPossibleImage record i =
        sourceData.toBoundedFamilyHullDetLogVolumeSource.quotientMap ''
          recordThetaPossibleImage record j ∧
      sourceData.familyHullLogVolume =
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.familyUnionLogVolume <=
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.tensorPower.normalizedLogVolume =
        sourceData.familyHullLogVolume ∧
      sourceData.tensorPower.tensorPowerLogVolume =
        (sourceData.tensorPower.tensorDegree : Real) *
          sourceData.familyHullLogVolume := by
  simpa [toBoundedFamilyHullDetLogVolumeSource, familyHull,
    familyHullLogVolume, familyUnionLogVolume, tensorPower] using
    sourceData.toBoundedFamilyHullDetLogVolumeSource.endpoint i j hnei hnej

theorem boundedFamily_ob5_endpoint
    (sourceData :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record)
    {A B : Set (Point target)}
    (hneA : A.Nonempty)
    (hneB : B.Nonempty) :
    (sourceData.toBoundedFamilyHullDetLogVolumeSource.quotientMap '' A =
          {IUTStage1UpperSemiSetQuotient.collapsed} ∧
        sourceData.toBoundedFamilyHullDetLogVolumeSource.quotientMap '' B =
          {IUTStage1UpperSemiSetQuotient.collapsed} ↔
      A ⊆ sourceData.familyHull ∧ B ⊆ sourceData.familyHull) ∧
      sourceData.familyHullLogVolume =
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.familyUnionLogVolume <=
        sourceData.determinantSource.determinantLogVolume ∧
      sourceData.tensorPower.normalizedLogVolume =
        sourceData.familyHullLogVolume ∧
      sourceData.tensorPower.tensorPowerLogVolume =
        (sourceData.tensorPower.tensorDegree : Real) *
          sourceData.familyHullLogVolume := by
  simpa [toBoundedFamilyHullDetLogVolumeSource, familyHull,
    familyHullLogVolume, familyUnionLogVolume, tensorPower] using
    sourceData.toBoundedFamilyHullDetLogVolumeSource.ob5_endpoint hneA hneB

end IUTStage1RecordBoundedFamilyHullDetLogVolumeSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Choice-linked exact-theta Step (xi) source whose theta value is backed by the
record-native possible-image family hull.

Compared to
`IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource`, this package no
longer asks for the equality with the normalized tensor-power value directly.
It asks for the source statement that `thetaSigned` is the log-volume of the
record possible-image hull.  The tensor-power equality and bound are then
derived from the Ob5 hull/determinant compatibility.
-/
structure IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaSigned_eq_familyHullLogVolume :
    package.preLedger.thetaSigned =
      familyHullSource.familyHullLogVolume
  hullDetSourceData : IUTStage1SourceHullDetData package
  hullDetSourceData_eq_recordCanonical :
    hullDetSourceData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
            thetaSigned_eq_familyHullLogVolume)
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

theorem thetaSigned_eq_tensorPowerNormalized
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    package.preLedger.thetaSigned =
      sourceData.familyHullSource.tensorPower.normalizedLogVolume := by
  have htensor :
      sourceData.familyHullSource.tensorPower.normalizedLogVolume =
        sourceData.familyHullSource.familyHullLogVolume :=
    sourceData.familyHullSource.tensorPower_normalizedLogVolume_eq_familyHullLogVolume
  calc
    package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume :=
      sourceData.thetaSigned_eq_familyHullLogVolume
    _ = sourceData.familyHullSource.tensorPower.normalizedLogVolume :=
      htensor.symm

theorem tensorPower_bound
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.familyHullSource.tensorPower.normalizedLogVolume <=
      package.preLedger.thetaSigned :=
  sourceData.familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
      sourceData.thetaSigned_eq_familyHullLogVolume

noncomputable def recordCanonicalBridgeData
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
    (record := record)
    sourceData.operation sourceData.hullOperation
    sourceData.determinantOperation sourceData.familyHullSource.hullData
    sourceData.qPilotRegion
    (qPilotRegion_subset_recordUnion_of_choice
      (record := record)
      sourceData.qChoice sourceData.qPilotRegion sourceData.q_subset_choice)
    sourceData.familyHullSource.determinantSource
    sourceData.familyHullSource.compatibility
    sourceData.measure_eq_hullLogVolume
    sourceData.tensorPower_bound

theorem hullDetBridge_eq
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      sourceData.recordCanonicalBridgeData := by
  calc
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData :=
      sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData
    _ = sourceData.recordCanonicalBridgeData :=
      sourceData.hullDetSourceData_eq_recordCanonical

noncomputable def toSideConditionedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.familyHullSource.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.familyHullSource.determinantSource,
    compatibility := sourceData.familyHullSource.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_tensorPowerNormalized :=
      sourceData.thetaSigned_eq_tensorPowerNormalized,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      sourceData.familyHullSource.familyHullLogVolume =
        sourceData.familyHullSource.determinantSource.determinantLogVolume ∧
      sourceData.familyHullSource.tensorPower.normalizedLogVolume =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.recordCanonicalBridgeData ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  by
    have htensor :
        sourceData.familyHullSource.tensorPower.normalizedLogVolume =
          sourceData.familyHullSource.familyHullLogVolume :=
      sourceData.familyHullSource.tensorPower_normalizedLogVolume_eq_familyHullLogVolume
    exact
      ⟨sourceData.q_subset_choice,
        sourceData.toSideConditionedHolomorphicHullDeterminantSource
          |>.toChoiceLinkedHolomorphicHullDeterminantSource |>.q_subset_recordUnion,
        sourceData.thetaSigned_eq_familyHullLogVolume,
        sourceData.familyHullSource.familyHullLogVolume_eq_determinant,
        htensor,
        sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData,
        sourceData.hullDetBridge_eq,
        sourceData.toSideConditionedHolomorphicHullDeterminantSource
          |>.qSigned_le_thetaSigned⟩

end IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image family-hull exact-theta Step (xi) source backed by package
hull/det data.

This refines `IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource`
by fixing the q-pilot region to a chosen Theorem 3.11 possible image.  It keeps
the Ob5-shaped family-hull assertion `thetaSigned = familyHullLogVolume`, while
deriving the q-pilot containment data needed by the existing choice-linked
source internally.
-/
structure IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaSigned_eq_familyHullLogVolume :
    package.preLedger.thetaSigned =
      familyHullSource.familyHullLogVolume
  hullDetSourceData : IUTStage1SourceHullDetData package
  hullDetSourceData_eq_recordCanonical :
    hullDetSourceData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice
          (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
            thetaSigned_eq_familyHullLogVolume)
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem q_subset_choice
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImage record sourceData.qChoice :=
  fun _ hx => hx

noncomputable def toChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_familyHullLogVolume :=
      sourceData.thetaSigned_eq_familyHullLogVolume,
    hullDetSourceData := sourceData.hullDetSourceData,
    hullDetSourceData_eq_recordCanonical :=
      sourceData.hullDetSourceData_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      sourceData.familyHullSource.familyHullLogVolume =
        sourceData.familyHullSource.determinantSource.determinantLogVolume ∧
      sourceData.familyHullSource.tensorPower.normalizedLogVolume =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        (sourceData.toChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
          |>.recordCanonicalBridgeData) ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected := sourceData.toChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
  ⟨rfl,
    projected.source_endpoint.2.1,
    sourceData.thetaSigned_eq_familyHullLogVolume,
    sourceData.familyHullSource.familyHullLogVolume_eq_determinant,
    sourceData.familyHullSource.tensorPower_normalizedLogVolume_eq_familyHullLogVolume,
    sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData,
    projected.hullDetBridge_eq,
    sourceData.sideConditions.q_pilot_positive,
    sourceData.sideConditions.sourceNormalization,
    projected.source_endpoint.2.2.2.2.2.2.2⟩

end IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image family-hull exact-theta Step (xi) source backed by package
hull/determinant obligations.

This refines `IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource`:
the q-pilot region is still definitionally the chosen Theorem 3.11 possible
image, while the package hull/determinant data, q-pilot positivity, and source
normalization are projected from one `IUTStage1SourceHullDetObligations`
object.
-/
structure IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaSigned_eq_familyHullLogVolume :
    package.preLedger.thetaSigned =
      familyHullSource.familyHullLogVolume
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice
          (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
            thetaSigned_eq_familyHullLogVolume)

namespace IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem q_subset_choice
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImage record sourceData.qChoice :=
  fun _ hx => hx

def sideConditions
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := sourceData.obligations.qPilotPositive,
    source_normalization := sourceData.obligations.normalization }

noncomputable def toPossibleImageFamilyHullExactThetaHullDetDataBackedSource
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    IUTStage1PossibleImageFamilyHullExactThetaHullDetDataBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_familyHullLogVolume :=
      sourceData.thetaSigned_eq_familyHullLogVolume,
    hullDetSourceData := sourceData.obligations.hullDetData,
    hullDetSourceData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData.toPossibleImageFamilyHullExactThetaHullDetDataBackedSource
  ⟨rfl,
    projected.source_endpoint.2.1,
    sourceData.thetaSigned_eq_familyHullLogVolume,
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2.2.2.2⟩

end IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Family-hull exact-theta Step (xi) source backed by hull/det obligations.

This refines
`IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource` by taking a
single `IUTStage1SourceHullDetObligations` object.  The package hull/det data,
q-pilot positivity, and normalization are then projected from that obligations
object rather than carried as separate Step (xi) fields.
-/
structure
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaSigned_eq_familyHullLogVolume :
    package.preLedger.thetaSigned =
      familyHullSource.familyHullLogVolume
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
            thetaSigned_eq_familyHullLogVolume)

namespace IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

def sideConditions
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    IUTStage1SourceSideConditions package :=
  { q_pilot_positive := sourceData.obligations.qPilotPositive,
    source_normalization := sourceData.obligations.normalization }

noncomputable def toFamilyHullExactThetaHullDetDataBackedSource
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_familyHullLogVolume :=
      sourceData.thetaSigned_eq_familyHullLogVolume,
    hullDetSourceData := sourceData.obligations.hullDetData,
    hullDetSourceData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.toFamilyHullExactThetaHullDetDataBackedSource.source_endpoint.1,
    sourceData.toFamilyHullExactThetaHullDetDataBackedSource.source_endpoint.2.1,
    sourceData.thetaSigned_eq_familyHullLogVolume,
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    sourceData.toFamilyHullExactThetaHullDetDataBackedSource
      |>.source_endpoint |>.2.2.2.2.2.2.2⟩

end IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Source-facing calibration tying the Hodge--Arakelov theta scalar to the
record-native possible-image family hull.

The previous family-hull Step (xi) source consumed the scalar equality
`thetaSigned = familyHullLogVolume` directly.  This record factors that input
through the Hodge--Arakelov theta-monoid degree: first the package theta scalar
is identified with the theta-monoid degree, then that degree is identified with
the log-volume of the record possible-image hull.
-/
structure IUTStage1HodgeFamilyHullLogVolumeCalibration
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β]
    (familyHullSource :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) where
  thetaSigned_eq_thetaMonoidDegree :
    package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree
  thetaMonoidDegree_eq_familyHullLogVolume :
    sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume

namespace IUTStage1HodgeFamilyHullLogVolumeCalibration

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]
variable {familyHullSource :
  IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
    (β := β) record}

theorem thetaSigned_eq_familyHullLogVolume
    (calibration :
      IUTStage1HodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  calibration.thetaSigned_eq_thetaMonoidDegree.trans
    calibration.thetaMonoidDegree_eq_familyHullLogVolume

theorem thetaSigned_eq_determinantLogVolume
    (calibration :
      IUTStage1HodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned =
      familyHullSource.determinantSource.determinantLogVolume := by
  rw [calibration.thetaSigned_eq_familyHullLogVolume,
    familyHullSource.familyHullLogVolume_eq_determinant]

theorem tensorPower_bound
    (calibration :
      IUTStage1HodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    familyHullSource.tensorPower.normalizedLogVolume <=
      package.preLedger.thetaSigned :=
  familyHullSource.tensorPower_bound_of_theta_eq_familyHullLogVolume
    calibration.thetaSigned_eq_familyHullLogVolume

theorem calibration_endpoint
    (calibration :
      IUTStage1HodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        familyHullSource.determinantSource.determinantLogVolume :=
  ⟨calibration.thetaSigned_eq_thetaMonoidDegree,
    calibration.thetaMonoidDegree_eq_familyHullLogVolume,
    calibration.thetaSigned_eq_familyHullLogVolume,
    calibration.thetaSigned_eq_determinantLogVolume⟩

end IUTStage1HodgeFamilyHullLogVolumeCalibration

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Charted version of the Hodge/family-hull scalar calibration.

This moves the package-theta part of the calibration through the actual
pre-ledger theta chart: the source supplies equality between the transported
theta chart coordinate and the Hodge--Arakelov theta-monoid degree, while
`IUTStage1PreLedgerData.thetaSigned_eq_chartedTheta` recovers the package
`thetaSigned` equality.
-/
structure IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β]
    (familyHullSource :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) where
  chartedTheta_eq_thetaMonoidDegree :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      sourceHA.thetaMonoidDegree
  thetaMonoidDegree_eq_familyHullLogVolume :
    sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume

namespace IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]
variable {familyHullSource :
  IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
    (β := β) record}

theorem thetaSigned_eq_thetaMonoidDegree
    (calibration :
      IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree :=
  package.preLedger.thetaSigned_eq_chartedTheta.symm.trans
    calibration.chartedTheta_eq_thetaMonoidDegree

theorem thetaSigned_eq_familyHullLogVolume
    (calibration :
      IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  calibration.thetaSigned_eq_thetaMonoidDegree.trans
    calibration.thetaMonoidDegree_eq_familyHullLogVolume

theorem chartedTheta_eq_canonicalOneDegree
    (calibration :
      IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) := by
  rw [calibration.chartedTheta_eq_thetaMonoidDegree,
    sourceHA.canonicalOneDegree_eq_thetaMonoidDegree]

def toHodgeFamilyHullLogVolumeCalibration
    (calibration :
      IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    IUTStage1HodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource :=
  { thetaSigned_eq_thetaMonoidDegree :=
      calibration.thetaSigned_eq_thetaMonoidDegree,
    thetaMonoidDegree_eq_familyHullLogVolume :=
      calibration.thetaMonoidDegree_eq_familyHullLogVolume }

theorem calibration_endpoint
    (calibration :
      IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) ∧
      package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  ⟨calibration.chartedTheta_eq_thetaMonoidDegree,
    calibration.chartedTheta_eq_canonicalOneDegree,
    calibration.thetaSigned_eq_thetaMonoidDegree,
    calibration.thetaMonoidDegree_eq_familyHullLogVolume,
    calibration.thetaSigned_eq_familyHullLogVolume⟩

end IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Determinant-factored charted Hodge/family-hull scalar calibration.

This refines `IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration`: the
Hodge--Arakelov theta-monoid degree is calibrated to the normalized determinant
log-volume supplied by the record-native Step (xi) family hull source.  The
family-hull equality is then derived from the existing Ob5
hull/determinant compatibility theorem.
-/
structure IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β]
    (familyHullSource :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) where
  chartedTheta_eq_thetaMonoidDegree :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      sourceHA.thetaMonoidDegree
  thetaMonoidDegree_eq_determinantNormalized :
    sourceHA.thetaMonoidDegree =
      familyHullSource.determinantSource.normalizedLogVolume

namespace IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]
variable {familyHullSource :
  IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
    (β := β) record}

theorem thetaMonoidDegree_eq_familyHullLogVolume
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume := by
  calc
    sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.normalizedLogVolume :=
      calibration.thetaMonoidDegree_eq_determinantNormalized
    _ = familyHullSource.familyHullLogVolume :=
      familyHullSource.familyHullLogVolume_eq_normalized.symm

theorem thetaMonoidDegree_eq_determinantLogVolume
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    sourceHA.thetaMonoidDegree =
      familyHullSource.determinantSource.determinantLogVolume := by
  rw [calibration.thetaMonoidDegree_eq_determinantNormalized,
    familyHullSource.determinantSource.normalizedLogVolume_eq_determinantLogVolume]

theorem thetaSigned_eq_familyHullLogVolume
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  package.preLedger.thetaSigned_eq_chartedTheta.symm.trans
    (calibration.chartedTheta_eq_thetaMonoidDegree.trans
      calibration.thetaMonoidDegree_eq_familyHullLogVolume)

theorem chartedTheta_eq_canonicalOneDegree
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      sourceHA.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) := by
  rw [calibration.chartedTheta_eq_thetaMonoidDegree,
    sourceHA.canonicalOneDegree_eq_thetaMonoidDegree]

def toChartedHodgeFamilyHullLogVolumeCalibration
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource :=
  { chartedTheta_eq_thetaMonoidDegree :=
      calibration.chartedTheta_eq_thetaMonoidDegree,
    thetaMonoidDegree_eq_familyHullLogVolume :=
      calibration.thetaMonoidDegree_eq_familyHullLogVolume }

theorem calibration_endpoint
    (calibration :
      IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.normalizedLogVolume ∧
      familyHullSource.familyHullLogVolume =
        familyHullSource.determinantSource.normalizedLogVolume ∧
      sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume ∧
      sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.determinantLogVolume ∧
      package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  ⟨calibration.chartedTheta_eq_thetaMonoidDegree,
    calibration.thetaMonoidDegree_eq_determinantNormalized,
    familyHullSource.familyHullLogVolume_eq_normalized,
    calibration.thetaMonoidDegree_eq_familyHullLogVolume,
    calibration.thetaMonoidDegree_eq_determinantLogVolume,
    calibration.thetaSigned_eq_familyHullLogVolume⟩

end IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Summand-factored charted Hodge/determinant scalar calibration.

This refines `IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration`:
the Hodge--Arakelov theta-monoid degree is calibrated to the finite sum of the
adjusted localization summands of the weighted determinant source.  Lean then
derives equality with the determinant log-volume and normalized determinant
log-volume from the weighted-determinant source theorems.
-/
structure IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β]
    (familyHullSource :
      IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
        (β := β) record) where
  chartedTheta_eq_thetaMonoidDegree :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
      package.preLedger.thetaBound.thetaPoint).coord =
      sourceHA.thetaMonoidDegree
  thetaMonoidDegree_eq_summandSum :
    sourceHA.thetaMonoidDegree =
      Finset.univ.sum fun index =>
        (familyHullSource.determinantSource.summand index).adjustedLogVolume

namespace IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]
variable {familyHullSource :
  IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
    (β := β) record}

theorem thetaMonoidDegree_eq_determinantLogVolume
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    sourceHA.thetaMonoidDegree =
      familyHullSource.determinantSource.determinantLogVolume := by
  calc
    sourceHA.thetaMonoidDegree =
        Finset.univ.sum fun index =>
          (familyHullSource.determinantSource.summand index).adjustedLogVolume :=
      calibration.thetaMonoidDegree_eq_summandSum
    _ = familyHullSource.determinantSource.determinantLogVolume :=
      familyHullSource.determinantSource.determinantLogVolume_eq_sum.symm

theorem thetaMonoidDegree_eq_determinantNormalized
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    sourceHA.thetaMonoidDegree =
      familyHullSource.determinantSource.normalizedLogVolume := by
  rw [calibration.thetaMonoidDegree_eq_determinantLogVolume,
    familyHullSource.determinantSource.normalizedLogVolume_eq_determinantLogVolume]

theorem thetaMonoidDegree_eq_familyHullLogVolume
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume := by
  calc
    sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.normalizedLogVolume :=
      calibration.thetaMonoidDegree_eq_determinantNormalized
    _ = familyHullSource.familyHullLogVolume :=
      familyHullSource.familyHullLogVolume_eq_normalized.symm

theorem thetaSigned_eq_familyHullLogVolume
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    package.preLedger.thetaSigned = familyHullSource.familyHullLogVolume :=
  package.preLedger.thetaSigned_eq_chartedTheta.symm.trans
    (calibration.chartedTheta_eq_thetaMonoidDegree.trans
      calibration.thetaMonoidDegree_eq_familyHullLogVolume)

def toDeterminantChartedHodgeFamilyHullLogVolumeCalibration
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource :=
  { chartedTheta_eq_thetaMonoidDegree :=
      calibration.chartedTheta_eq_thetaMonoidDegree,
    thetaMonoidDegree_eq_determinantNormalized :=
      calibration.thetaMonoidDegree_eq_determinantNormalized }

theorem calibration_endpoint
    (calibration :
      IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
        record sourceHA familyHullSource) :
    (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        (Finset.univ.sum fun index =>
          (familyHullSource.determinantSource.summand index).adjustedLogVolume) ∧
      sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.determinantLogVolume ∧
      sourceHA.thetaMonoidDegree =
        familyHullSource.determinantSource.normalizedLogVolume ∧
      sourceHA.thetaMonoidDegree = familyHullSource.familyHullLogVolume :=
  ⟨calibration.chartedTheta_eq_thetaMonoidDegree,
    calibration.thetaMonoidDegree_eq_summandSum,
    calibration.thetaMonoidDegree_eq_determinantLogVolume,
    calibration.thetaMonoidDegree_eq_determinantNormalized,
    calibration.thetaMonoidDegree_eq_familyHullLogVolume⟩

end IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Hodge-calibrated version of the obligations-backed family-hull Step (xi)
source.

This record replaces the raw `thetaSigned = familyHullLogVolume` field by a
typed calibration from the Hodge--Arakelov theta-monoid degree to the
record-native possible-image family hull.  It still projects to the existing
obligations-backed source, so downstream finite-divisor endpoints can reuse the
already-audited bridge construction.
-/
structure
    IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaFamilyCalibration :
    IUTStage1HodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          thetaFamilyCalibration)

namespace IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

noncomputable def toFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_familyHullLogVolume :=
      sourceData.thetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

theorem source_endpoint
    (sourceData :
      IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData.toFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨sourceData.q_subset_choice,
    sourceData.thetaFamilyCalibration.thetaSigned_eq_thetaMonoidDegree,
    sourceData.thetaFamilyCalibration.thetaMonoidDegree_eq_familyHullLogVolume,
    sourceData.thetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    projected.source_endpoint.2.2.2.1,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2⟩

end IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image Hodge-calibrated version of the obligations-backed family-hull
Step (xi) source.

This combines two refinements: the q-pilot region is definitionally the chosen
Theorem 3.11 possible image, and the equality
`thetaSigned = familyHullLogVolume` is derived from a Hodge--Arakelov
theta/family-hull calibration rather than supplied as a raw Step (xi) field.
-/
structure
    IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  thetaFamilyCalibration :
    IUTStage1HodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice
          (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          thetaFamilyCalibration)

namespace
  IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem q_subset_choice
    (sourceData :
      IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImage record sourceData.qChoice :=
  fun _ hx => hx

noncomputable def toPossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1PossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_familyHullLogVolume :=
      sourceData.thetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

noncomputable def toHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaFamilyCalibration := sourceData.thetaFamilyCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData.toPossibleImageFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨rfl,
    projected.source_endpoint.2.1,
    sourceData.thetaFamilyCalibration.thetaSigned_eq_thetaMonoidDegree,
    sourceData.thetaFamilyCalibration.thetaMonoidDegree_eq_familyHullLogVolume,
    sourceData.thetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2⟩

end IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Charted Hodge-calibrated version of the obligations-backed family-hull Step
(xi) source.

This strengthens
`IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource`:
the package theta scalar is no longer calibrated directly to the
Hodge--Arakelov theta-monoid degree.  Instead, the source calibrates the
transported theta chart coordinate, and the package scalar equality is derived
from the pre-ledger chart theorem.
-/
structure
    IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  chartedThetaFamilyCalibration :
    IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          chartedThetaFamilyCalibration.toHodgeFamilyHullLogVolumeCalibration)

namespace
  IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

noncomputable def toHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1HodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaFamilyCalibration :=
      sourceData.chartedThetaFamilyCalibration
        |>.toHodgeFamilyHullLogVolumeCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

noncomputable def toFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record :=
  sourceData.toHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    |>.toFamilyHullExactThetaHullDetObligationsBackedSource

theorem source_endpoint
    (sourceData :
      IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData.toHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨sourceData.q_subset_choice,
    sourceData.chartedThetaFamilyCalibration.chartedTheta_eq_thetaMonoidDegree,
    sourceData.chartedThetaFamilyCalibration.thetaSigned_eq_thetaMonoidDegree,
    sourceData.chartedThetaFamilyCalibration.thetaMonoidDegree_eq_familyHullLogVolume,
    sourceData.chartedThetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    projected.source_endpoint.2.2.2.2.1,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2.2⟩

end IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image charted Hodge-calibrated version of the obligations-backed
family-hull Step (xi) source.

This refines
`IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource`:
the q-pilot region is still definitionally the chosen Theorem 3.11 possible
image, and the package theta scalar is derived from the transported pre-ledger
theta chart before comparing with the Hodge--Arakelov theta-monoid degree.
-/
structure
    IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  chartedThetaFamilyCalibration :
    IUTStage1ChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice
          (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          chartedThetaFamilyCalibration.toHodgeFamilyHullLogVolumeCalibration)

namespace
  IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem q_subset_choice
    (sourceData :
      IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImage record sourceData.qChoice :=
  fun _ hx => hx

noncomputable def toPossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1PossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaFamilyCalibration :=
      sourceData.chartedThetaFamilyCalibration
        |>.toHodgeFamilyHullLogVolumeCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

noncomputable def toChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    chartedThetaFamilyCalibration :=
      sourceData.chartedThetaFamilyCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      package.preLedger.thetaSigned = sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData.toPossibleImageHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨rfl,
    projected.source_endpoint.2.1,
    sourceData.chartedThetaFamilyCalibration.chartedTheta_eq_thetaMonoidDegree,
    sourceData.chartedThetaFamilyCalibration.thetaSigned_eq_thetaMonoidDegree,
    sourceData.chartedThetaFamilyCalibration.thetaMonoidDegree_eq_familyHullLogVolume,
    sourceData.chartedThetaFamilyCalibration.thetaSigned_eq_familyHullLogVolume,
    sourceData.obligations.hullDetData.hullDetBridge_eq_bridgeData,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2.2.2⟩

end IUTStage1PossibleImageChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Determinant-factored charted Hodge-calibrated version of the obligations-backed
family-hull Step (xi) source.

This strengthens the charted Hodge-calibrated source by making the remaining
Hodge/family-hull scalar equality pass through the normalized determinant
log-volume of the record-native family hull.
-/
structure
    IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  determinantChartedCalibration :
    IUTStage1DeterminantChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          (determinantChartedCalibration
            |>.toChartedHodgeFamilyHullLogVolumeCalibration
            |>.toHodgeFamilyHullLogVolumeCalibration))

namespace
  IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

noncomputable def toChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    chartedThetaFamilyCalibration :=
      sourceData.determinantChartedCalibration
        |>.toChartedHodgeFamilyHullLogVolumeCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

noncomputable def toFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record :=
  sourceData
    |>.toChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
    |>.toFamilyHullExactThetaHullDetObligationsBackedSource

theorem source_endpoint
    (sourceData :
      IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.determinantSource.normalizedLogVolume ∧
      sourceData.familyHullSource.familyHullLogVolume =
        sourceData.familyHullSource.determinantSource.normalizedLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData
      |>.toChartedHodgeCalibratedFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨sourceData.q_subset_choice,
    sourceData.determinantChartedCalibration.chartedTheta_eq_thetaMonoidDegree,
    sourceData.determinantChartedCalibration
      |>.thetaMonoidDegree_eq_determinantNormalized,
    sourceData.familyHullSource.familyHullLogVolume_eq_normalized,
    sourceData.determinantChartedCalibration.thetaSigned_eq_familyHullLogVolume,
    projected.source_endpoint.2.2.2.2.2.1,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2.2.2⟩

end IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Summand-factored charted Hodge-calibrated version of the obligations-backed
family-hull Step (xi) source.

This strengthens the determinant-factored source by calibrating the
Hodge--Arakelov theta-monoid degree to the finite sum of adjusted localization
summands of the weighted determinant source.
-/
structure
    IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {l : PrimeGeFive} {F : Type w} [Field F]
    {X C : HyperbolicOrbicurveModel F}
    (sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        l X C)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  familyHullSource :
    IUTStage1RecordBoundedFamilyHullDetLogVolumeSource
      (β := β) record
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  measure_eq_hullLogVolume :
    package.preLedger.measure = familyHullSource.hullData.toRegionMeasure
  summandChartedCalibration :
    IUTStage1SummandChartedHodgeFamilyHullLogVolumeCalibration
      record sourceHA familyHullSource
  obligations : IUTStage1SourceHullDetObligations package
  obligationsHullDetData_eq_recordCanonical :
    obligations.hullDetData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation familyHullSource.hullData
        qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        familyHullSource.determinantSource familyHullSource.compatibility
        measure_eq_hullLogVolume
        (IUTStage1HodgeFamilyHullLogVolumeCalibration.tensorPower_bound
          (summandChartedCalibration
            |>.toDeterminantChartedHodgeFamilyHullLogVolumeCalibration
            |>.toChartedHodgeFamilyHullLogVolumeCalibration
            |>.toHodgeFamilyHullLogVolumeCalibration))

namespace
  IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {l : PrimeGeFive} {F : Type w} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable {sourceHA :
  IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
    l X C}
variable {β : Type v} [Fintype β]

noncomputable def toDeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1DeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record sourceHA :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    familyHullSource := sourceData.familyHullSource,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    determinantChartedCalibration :=
      sourceData.summandChartedCalibration
        |>.toDeterminantChartedHodgeFamilyHullLogVolumeCalibration,
    obligations := sourceData.obligations,
    obligationsHullDetData_eq_recordCanonical :=
      sourceData.obligationsHullDetData_eq_recordCanonical }

noncomputable def toFamilyHullExactThetaHullDetObligationsBackedSource
    (sourceData :
      IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetObligationsBackedSource
      (β := β) record :=
  sourceData
    |>.toDeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
    |>.toFamilyHullExactThetaHullDetObligationsBackedSource

theorem source_endpoint
    (sourceData :
      IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
        (β := β) record sourceHA) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      (Transport.map package.preLedger.chartedContainer.chart.thetaToTarget
        package.preLedger.thetaBound.thetaPoint).coord =
        sourceHA.thetaMonoidDegree ∧
      sourceHA.thetaMonoidDegree =
        (Finset.univ.sum fun index =>
          (sourceData.familyHullSource.determinantSource.summand index).adjustedLogVolume) ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.determinantSource.determinantLogVolume ∧
      sourceHA.thetaMonoidDegree =
        sourceData.familyHullSource.determinantSource.normalizedLogVolume ∧
      package.preLedger.thetaSigned =
        sourceData.familyHullSource.familyHullLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.obligations.hullDetData.bridgeData ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected :=
    sourceData
      |>.toDeterminantChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource
  ⟨sourceData.q_subset_choice,
    sourceData.summandChartedCalibration.chartedTheta_eq_thetaMonoidDegree,
    sourceData.summandChartedCalibration.thetaMonoidDegree_eq_summandSum,
    sourceData.summandChartedCalibration.thetaMonoidDegree_eq_determinantLogVolume,
    sourceData.summandChartedCalibration.thetaMonoidDegree_eq_determinantNormalized,
    sourceData.summandChartedCalibration.thetaSigned_eq_familyHullLogVolume,
    projected.source_endpoint.2.2.2.2.2.1,
    sourceData.obligations.qPilotPositive,
    sourceData.obligations.normalization,
    projected.source_endpoint.2.2.2.2.2.2.2.2⟩

end IUTStage1SummandChartedHodgeFamilyHullExactThetaHullDetObligationsBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Choice-linked exact-theta Step (xi) source backed by package hull/det data.

This variant no longer carries the package bridge equality directly.  Instead
it consumes the package's `IUTStage1SourceHullDetData`, whose pre-ledger source
data already stores equality with the named package hull/determinant bridge,
and a compatibility equality identifying that stored bridge data with the
record-canonical Step (xi) hull/tensor-power construction.
-/
structure IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  qPilotRegion : Set (Point target)
  q_subset_choice :
    qPilotRegion ⊆
      IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record qChoice
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  thetaSigned_eq_tensorPowerNormalized :
    package.preLedger.thetaSigned =
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume
  hullDetSourceData : IUTStage1SourceHullDetData package
  hullDetSourceData_eq_recordCanonical :
    hullDetSourceData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData qPilotRegion
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice qPilotRegion q_subset_choice)
        determinantSource compatibility measure_eq_hullLogVolume
        (le_of_eq thetaSigned_eq_tensorPowerNormalized.symm)
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

noncomputable def recordCanonicalBridgeData
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
        (β := β) record) :
    package.preLedger.output.HullDetBridgeData
      package.preLedger.measure package.preLedger.thetaSigned :=
  recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
    (record := record)
    sourceData.operation sourceData.hullOperation
    sourceData.determinantOperation sourceData.hullData
    sourceData.qPilotRegion
    (qPilotRegion_subset_recordUnion_of_choice
      (record := record)
      sourceData.qChoice sourceData.qPilotRegion sourceData.q_subset_choice)
    sourceData.determinantSource sourceData.compatibility
    sourceData.measure_eq_hullLogVolume
    (le_of_eq sourceData.thetaSigned_eq_tensorPowerNormalized.symm)

theorem hullDetBridge_eq
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
        (β := β) record) :
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      sourceData.recordCanonicalBridgeData := by
  calc
    package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData :=
      sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData
    _ = sourceData.recordCanonicalBridgeData :=
      sourceData.hullDetSourceData_eq_recordCanonical

noncomputable def toSideConditionedHolomorphicHullDeterminantSource
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedExactThetaSideConditionedHolomorphicHullDeterminantSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_tensorPowerNormalized :=
      sourceData.thetaSigned_eq_tensorPowerNormalized,
    hullDetBridge_eq := sourceData.hullDetBridge_eq,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      package.preLedger.thetaSigned =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.recordCanonicalBridgeData ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  ⟨sourceData.q_subset_choice,
    sourceData.toSideConditionedHolomorphicHullDeterminantSource
      |>.toChoiceLinkedHolomorphicHullDeterminantSource |>.q_subset_recordUnion,
    sourceData.thetaSigned_eq_tensorPowerNormalized,
    sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData,
    sourceData.hullDetBridge_eq,
    sourceData.toSideConditionedHolomorphicHullDeterminantSource
      |>.qSigned_le_thetaSigned⟩

end IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource

open IUTStage1Theorem311HullDetSourceConstructor in
/--
Possible-image exact-theta Step (xi) source backed by package hull/det data.

This refines `IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource` by fixing
the q-pilot region to the chosen Theorem 3.11 possible image.  The containment
`q \subseteq P_choice` is then the reflexive subset proof, so the exact-theta
data-backed source no longer carries an arbitrary q-region at this boundary.
-/
structure IUTStage1PossibleImageExactThetaHullDetDataBackedSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    (record : IUTStage1Theorem311MultiradialSourceRecord package)
    {β : Type v} [Fintype β] where
  operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId
  hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId
  determinantOperation :
    RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId
  hullData : IUTStage1HolomorphicHullLogVolumeShadow (Point target)
  qChoice : index
  determinantSource :
    IUTStage1ArithmeticVectorBundleWeightedDeterminantSource β
  compatibility :
    IUTStage1HullApproximantWeightedDeterminantCompatibility
      (IUTStage1HullLogVolumeApproximant.canonical
        hullData
          (IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record))
      determinantSource
  measure_eq_hullLogVolume :
    package.preLedger.measure = hullData.toRegionMeasure
  thetaSigned_eq_tensorPowerNormalized :
    package.preLedger.thetaSigned =
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          determinantSource).normalizedLogVolume
  hullDetSourceData : IUTStage1SourceHullDetData package
  hullDetSourceData_eq_recordCanonical :
    hullDetSourceData.bridgeData =
      recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
        (record := record)
        operation hullOperation determinantOperation hullData
        (recordThetaPossibleImage record qChoice)
        (qPilotRegion_subset_recordUnion_of_choice
          (record := record) qChoice
          (recordThetaPossibleImage record qChoice)
          (fun _ hx => hx))
        determinantSource compatibility measure_eq_hullLogVolume
        (le_of_eq thetaSigned_eq_tensorPowerNormalized.symm)
  sideConditions : IUTStage1SourceSideConditions package

namespace IUTStage1PossibleImageExactThetaHullDetDataBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

open IUTStage1Theorem311HullDetSourceConstructor

def qPilotRegion
    (sourceData :
      IUTStage1PossibleImageExactThetaHullDetDataBackedSource
        (β := β) record) :
    Set (Point target) :=
  recordThetaPossibleImage record sourceData.qChoice

theorem q_subset_choice
    (sourceData :
      IUTStage1PossibleImageExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion ⊆
      recordThetaPossibleImage record sourceData.qChoice :=
  fun _ hx => hx

noncomputable def toChoiceLinkedExactThetaHullDetDataBackedSource
    (sourceData :
      IUTStage1PossibleImageExactThetaHullDetDataBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.determinantSource,
    compatibility := sourceData.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_tensorPowerNormalized :=
      sourceData.thetaSigned_eq_tensorPowerNormalized,
    hullDetSourceData := sourceData.hullDetSourceData,
    hullDetSourceData_eq_recordCanonical :=
      sourceData.hullDetSourceData_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

theorem source_endpoint
    (sourceData :
      IUTStage1PossibleImageExactThetaHullDetDataBackedSource
        (β := β) record) :
    sourceData.qPilotRegion =
        recordThetaPossibleImage record sourceData.qChoice ∧
      sourceData.qPilotRegion ⊆
        recordThetaPossibleImageUnion record ∧
      package.preLedger.thetaSigned =
        (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          sourceData.determinantSource).normalizedLogVolume ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.hullDetSourceData.bridgeData ∧
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        (sourceData.toChoiceLinkedExactThetaHullDetDataBackedSource
          |>.recordCanonicalBridgeData) ∧
      0 < -package.preLedger.qSigned ∧
      package.preLedger.normalization ∧
      package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  let projected := sourceData.toChoiceLinkedExactThetaHullDetDataBackedSource
  ⟨rfl,
    projected.source_endpoint.2.1,
    sourceData.thetaSigned_eq_tensorPowerNormalized,
    sourceData.hullDetSourceData.hullDetBridge_eq_bridgeData,
    projected.hullDetBridge_eq,
    sourceData.sideConditions.q_pilot_positive,
    sourceData.sideConditions.sourceNormalization,
    projected.source_endpoint.2.2.2.2.2⟩

end IUTStage1PossibleImageExactThetaHullDetDataBackedSource

namespace IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]

noncomputable def toExactThetaHullDetDataBackedSource
    (sourceData :
      IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource
        (β := β) record) :
    IUTStage1ChoiceLinkedExactThetaHullDetDataBackedSource
      (β := β) record :=
  { operation := sourceData.operation,
    hullOperation := sourceData.hullOperation,
    determinantOperation := sourceData.determinantOperation,
    hullData := sourceData.familyHullSource.hullData,
    qChoice := sourceData.qChoice,
    qPilotRegion := sourceData.qPilotRegion,
    q_subset_choice := sourceData.q_subset_choice,
    determinantSource := sourceData.familyHullSource.determinantSource,
    compatibility := sourceData.familyHullSource.compatibility,
    measure_eq_hullLogVolume := sourceData.measure_eq_hullLogVolume,
    thetaSigned_eq_tensorPowerNormalized :=
      sourceData.thetaSigned_eq_tensorPowerNormalized,
    hullDetSourceData := sourceData.hullDetSourceData,
    hullDetSourceData_eq_recordCanonical :=
      sourceData.hullDetSourceData_eq_recordCanonical,
    sideConditions := sourceData.sideConditions }

end IUTStage1ChoiceLinkedFamilyHullExactThetaHullDetDataBackedSource

end IUTStage1SourcePackage

end Stage1
end Iut
