/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTSourceScaffold

/-!
Named pre-ledger data for future IUT-specific Stage 1 constructions.

This module records the source-specific ingredients that should eventually feed
a `SourceObligationLedger`. It deliberately stops before constructing that
ledger, so missing obligations remain visible.
-/

namespace Iut
namespace Stage1

open RealLineCopy

/-- Inert identifier for the Stage 1 input data, e.g. a base prime-strip package. -/
structure Stage1InputId where
  label : String

/-- Inert identifier for the multiradial output supplied by the Stage 1 algorithm. -/
structure MultiradialOutputId where
  label : String

/-- Inert identifier for the final charted log-volume comparison package. -/
structure LogVolumeComparisonId where
  label : String

/--
Pre-ledger Stage 1 data for a future IUT-specific construction.

The record separates qualitative data, multiradial output labels, charted
q/Theta log-volume data, selected output data, and membership data. It does not
claim that the remaining source obligations needed for a
`SourceObligationLedger` have been discharged.
-/
structure IUTStage1PreLedgerData (source target : Copy) (index : Type u) where
  input : Stage1InputId
  multiradialOutput : MultiradialOutputId
  logVolumeComparison : LogVolumeComparisonId
  output : AlgorithmicOutput source target index
  measure : RegionMeasure target
  thetaSigned : Real
  qSigned : Real
  normalization : Prop
  certificate : QualitativeData.StructuredCertificate output.family
  chartedContainer : output.ChartedCommonContainerData measure thetaSigned
  qValue : output.ChartedQValueData measure chartedContainer.chart qSigned
  thetaBound : output.ChartedThetaBoundData measure chartedContainer.chart thetaSigned
  chosenOutput : output.ChosenOutputData
  targetVolume :
    output.ChartedTargetVolumeData measure chartedContainer.chart chosenOutput.choice
  membership :
    output.ChartedMembershipData measure chartedContainer.chart
      qValue chosenOutput targetVolume

namespace IUTStage1PreLedgerData

variable {source target : Copy} {index : Type u}

def hasStructuredIPL (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredIPL data.output.family :=
  data.certificate.hasStructuredIPL

def hasStructuredSHE (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredSHE data.output.family :=
  data.certificate.hasStructuredSHE

def hasStructuredAPT (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredAPT data.output.family :=
  data.certificate.hasStructuredAPT

theorem thetaChartTrivial (data : IUTStage1PreLedgerData source target index) :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget :=
  data.chartedContainer.thetaTrivial

theorem qSigned_eq_chartedQ (data : IUTStage1PreLedgerData source target index) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned :=
  data.qValue.qSigned_eq

theorem thetaSigned_eq_chartedTheta
    (data : IUTStage1PreLedgerData source target index) :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned :=
  data.thetaBound.thetaSigned_eq

theorem chosenComparisonHoldsQ
    (data : IUTStage1PreLedgerData source target index) :
    data.chosenOutput.comparison.Holds data.qValue.qPoint :=
  data.membership.holds

theorem qSigned_le_targetSigned
    (data : IUTStage1PreLedgerData source target index) :
    data.qSigned <= data.targetVolume.targetSigned :=
  data.membership.q_le_target

theorem targetSigned_eq_choiceTargetVolume
    (data : IUTStage1PreLedgerData source target index) :
    data.targetVolume.targetSigned =
      RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) :=
  data.targetVolume.targetSigned_eq

theorem choiceTargetVolume_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index) :
    RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) <=
      data.thetaSigned :=
  data.chartedContainer.choice_targetVolume_le
    data.certificate data.chosenOutput.choice

theorem targetSigned_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index) :
    data.targetVolume.targetSigned <= data.thetaSigned := by
  rw [data.targetSigned_eq_choiceTargetVolume]
  exact data.choiceTargetVolume_le_thetaSigned

/-- Local audit of pre-ledger data, before the remaining ledger obligations. -/
structure Audit (data : IUTStage1PreLedgerData source target index) : Prop where
  has_structured_ipl : QualitativeData.HasStructuredIPL data.output.family
  has_structured_she : QualitativeData.HasStructuredSHE data.output.family
  has_structured_apt : QualitativeData.HasStructuredAPT data.output.family
  theta_chart_trivial :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned
  theta_charted :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned
  chosen_holds :
    data.chosenOutput.comparison.Holds data.qValue.qPoint
  q_le_target :
    data.qSigned <= data.targetVolume.targetSigned
  target_le_theta :
    data.targetVolume.targetSigned <= data.thetaSigned

theorem audit (data : IUTStage1PreLedgerData source target index) :
    Audit data :=
  { has_structured_ipl := data.hasStructuredIPL,
    has_structured_she := data.hasStructuredSHE,
    has_structured_apt := data.hasStructuredAPT,
    theta_chart_trivial := data.thetaChartTrivial,
    q_charted := data.qSigned_eq_chartedQ,
    theta_charted := data.thetaSigned_eq_chartedTheta,
    chosen_holds := data.chosenComparisonHoldsQ,
    q_le_target := data.qSigned_le_targetSigned,
    target_le_theta := data.targetSigned_le_thetaSigned }

end IUTStage1PreLedgerData

end Stage1
end Iut
