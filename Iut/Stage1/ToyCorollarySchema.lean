/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.CorollarySchema
import Iut.Stage1.ToyBridge

/-!
Toy specialization of the Stage 1 Corollary 3.12 schema.

This file obtains the signed q-side real value from membership in a chosen
transported upper-ray output, then applies the explicit toy bridge to get the
Corollary-3.12-shaped inequality.
-/

namespace Iut
namespace Stage1
namespace ToyModel

open RealLineCopy

variable {index : Type u}

theorem unitThetaToy_qSigned_le_choiceTargetVolume
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (h : Real) (epsilon : index -> Real) (choice : index)
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    (Transport.map unitQToTheta (qAssignment h)).coord <=
      RegionMeasure.targetVolume measure
        ((thetaToyAlgorithmOutput unitQToTheta h epsilon).comparison choice) := by
  have hcomparison :
      (thetaIndeterminacyComparison unitQToTheta h (epsilon choice)).Holds
        (qAssignment h) := by
    simpa [AlgorithmicOutput.Holds, TransportedRegionFamily.Holds,
      thetaToyAlgorithmOutput, thetaAPTOutput, TransportedRegionFamily.comparison]
      using hholds
  have hle :=
    (thetaIndeterminacy_holds_iff_coord_le_targetVolume measure hnormalized
      unitQToTheta h (epsilon choice)).mp hcomparison
  simpa [thetaToyAlgorithmOutput, thetaAPTOutput, TransportedRegionFamily.comparison]
    using hle

theorem unitThetaToyCorollary312
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (h : Real) {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta (-(2 * h) + epsilonBound))
      (signedPilotLogVolume PilotSide.q
        (Transport.map unitQToTheta (qAssignment h)).coord) :=
  corollary312_from_bridge
    (thetaToyCommonTargetBoundBridge measure hnormalized unitQToTheta h hbound)
    (thetaToyAlgorithmOutput_certified unitQToTheta h epsilon)
    choice
    (unitThetaToy_qSigned_le_choiceTargetVolume measure hnormalized h epsilon choice hholds)

theorem unitThetaToyStructuredCorollary312
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (h : Real) {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta (-(2 * h) + epsilonBound))
      (signedPilotLogVolume PilotSide.q
        (Transport.map unitQToTheta (qAssignment h)).coord) :=
  corollary312_from_structured_bridge
    (thetaToyStructuredCommonTargetBoundBridge measure hnormalized unitQToTheta h hbound)
    (thetaToyStructuredCertificate unitQToTheta h epsilon)
    choice
    (unitThetaToy_qSigned_le_choiceTargetVolume measure hnormalized h epsilon choice hholds)

def unitThetaToyComparisonData
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Corollary312ComparisonData :=
  { thetaSigned := -(2 * h) + epsilonBound,
    qSigned := (Transport.map unitQToTheta (qAssignment h)).coord,
    q_positive := by
      unfold qAssignment unitQToTheta Transport.map point PositiveScale.one
      linarith,
    qSigned_le_thetaSigned :=
      le_trans
        (unitThetaToy_qSigned_le_choiceTargetVolume
          measure hnormalized h epsilon choice hholds)
        ((thetaToyCommonTargetBoundBridge
          measure hnormalized unitQToTheta h hbound).choice_targetVolume_le
            (thetaToyAlgorithmOutput_certified unitQToTheta h epsilon) choice) }

theorem unitThetaToyComparisonData_corollary312
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta (-(2 * h) + epsilonBound))
      (signedPilotLogVolume PilotSide.q
        (Transport.map unitQToTheta (qAssignment h)).coord) :=
  (unitThetaToyComparisonData
    measure hnormalized hh hbound hholds).corollary312

def unitThetaToyStage1Comparison
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Stage1Comparison :=
  (unitThetaToyComparisonData measure hnormalized hh hbound hholds).stage1Comparison

theorem unitThetaToyStage1Comparison_eq_comparisonData
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    unitThetaToyStage1Comparison measure hnormalized hh hbound hholds =
      (unitThetaToyComparisonData
        measure hnormalized hh hbound hholds).stage1Comparison :=
  rfl

def unitThetaToyStructuredStage1Comparison
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    Stage1Comparison :=
  (unitThetaToyComparisonData measure hnormalized hh hbound hholds).stage1Comparison

theorem unitThetaToyStructuredStage1Comparison_eq_comparisonData
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    unitThetaToyStructuredStage1Comparison
        measure hnormalized hh hbound hholds =
      (unitThetaToyComparisonData
        measure hnormalized hh hbound hholds).stage1Comparison :=
  rfl

end ToyModel
end Stage1
end Iut
