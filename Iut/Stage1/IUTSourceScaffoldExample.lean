/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTSourceScaffold
import Iut.Stage1.ToySourceObligations

/-!
Regression examples for the non-toy source-provider scaffold.

The toy ledger is used only as a sample provider. The examples consume the
generic `IUTSourceObligationProvider` API, checking that future non-toy providers
will expose the same public Stage 1 endpoints.
-/

namespace Iut
namespace Stage1
namespace ToyModel

open RealLineCopy

variable {index : Type u}

def unitThetaToyIUTSourceProvider
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    IUTSourceObligationProvider
      (thetaToyAlgorithmOutput unitQToTheta h epsilon)
      measure
      (-(2 * h) + epsilonBound)
      (Transport.map unitQToTheta (qAssignment h)).coord
      (RegionMeasure.NormalizesUpperRays measure) :=
  { ledger := unitThetaToySourceObligationLedger
      measure hnormalized hh hbound hholds }

theorem unitThetaToy_provider_publicAudit_q_le_theta_example
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
  (unitThetaToyIUTSourceProvider
    measure hnormalized hh hbound hholds).publicAudit.1

theorem unitThetaToy_provider_publicAudit_corollary_example
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
  (unitThetaToyIUTSourceProvider
    measure hnormalized hh hbound hholds).publicAudit.2.1

theorem unitThetaToy_provider_stage_recovers_corollary_example
    (measure : RegionMeasure thetaLine)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    {h : Real} (hh : 0 < h)
    {epsilon : index -> Real} {epsilonBound : Real}
    (hbound : ∀ choice : index, epsilon choice <= epsilonBound)
    {choice : index}
    (hholds : (thetaToyAlgorithmOutput unitQToTheta h epsilon).Holds choice
      (qAssignment h)) :
    corollary312_from_stage1_comparison
      (unitThetaToyIUTSourceProvider
        measure hnormalized hh hbound hholds).stage1Comparison =
      (unitThetaToyIUTSourceProvider
        measure hnormalized hh hbound hholds).ledger.corollary312 :=
  (unitThetaToyIUTSourceProvider
    measure hnormalized hh hbound hholds).stage1Comparison_recovers_corollary312

end ToyModel
end Stage1
end Iut
