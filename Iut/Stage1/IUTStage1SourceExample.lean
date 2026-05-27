/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Source
import Iut.Stage1.IUTStage1DataExample

/-!
Regression examples for the source-facing Stage 1 package.

These examples route the existing toy pre-ledger data through the non-toy
source-facing API. They do not assert that the toy data is genuine IUT data; the
purpose is only to verify that the source-facing package remains usable once
explicit source obligations are supplied.
-/

namespace Iut
namespace Stage1
namespace ToyModel

open RealLineCopy

variable {index : Type u}

def unitThetaToyIUTStage1SourceLabels : IUTStage1SourceLabels :=
  { theorem311ToCorollary312Labels with
    input := unitThetaToyStage1Input,
    multiradialOutput := unitThetaToyMultiradialOutput,
    logVolumeComparison := unitThetaToyLogVolumeComparison }

def unitThetaToyIUTStage1SourcePackage
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    IUTStage1SourcePackage qLine thetaLine index :=
  { labels := unitThetaToyIUTStage1SourceLabels,
    preLedger := unitThetaToyPreLedgerData measure hnormalized hh hbound hholds,
    input_eq := rfl,
    multiradialOutput_eq := rfl,
    logVolumeComparison_eq := rfl }

def unitThetaToyIUTStage1SourceObligations
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    IUTStage1SourceObligations
      (unitThetaToyIUTStage1SourcePackage
        measure hnormalized hh hbound hholds) :=
  let obligations :=
    unitThetaToyPromotionObligations measure hnormalized hh hbound hholds
  { algorithm_certified := obligations.certified,
    she_arrow_matches_certificate := obligations.she_matches_certificate,
    q_pilot_positive := obligations.q_positive,
    normalization := obligations.normalization_proof }

theorem unitThetaToy_source_publicAudit_q_le_theta_example
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    (Transport.map unitQToTheta (qAssignment h)).coord <=
      -(2 * h) + epsilonBound :=
  (unitThetaToyIUTStage1SourcePackage
    measure hnormalized hh hbound hholds).publicAudit_qSigned_le_thetaSigned
      (unitThetaToyIUTStage1SourceObligations
        measure hnormalized hh hbound hholds)

theorem unitThetaToy_source_publicAudit_corollary_example
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
  (unitThetaToyIUTStage1SourcePackage
    measure hnormalized hh hbound hholds).publicAudit_corollary312
      (unitThetaToyIUTStage1SourceObligations
        measure hnormalized hh hbound hholds)

theorem unitThetaToy_source_stage_recovers_corollary_example
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    corollary312_from_stage1_comparison
      ((unitThetaToyIUTStage1SourcePackage
        measure hnormalized hh hbound hholds).promotedProvider
          (unitThetaToyIUTStage1SourceObligations
            measure hnormalized hh hbound hholds)).stage1Comparison =
      ((unitThetaToyIUTStage1SourcePackage
        measure hnormalized hh hbound hholds).promotedProvider
          (unitThetaToyIUTStage1SourceObligations
            measure hnormalized hh hbound hholds)).ledger.corollary312 :=
  (unitThetaToyIUTStage1SourcePackage
    measure hnormalized hh hbound hholds).stage1Comparison_recovers_corollary312
      (unitThetaToyIUTStage1SourceObligations
        measure hnormalized hh hbound hholds)

end ToyModel
end Stage1
end Iut
