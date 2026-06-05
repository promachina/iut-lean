/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1FrobenioidShift

/-!
Structured endpoint corridor for the Stage 1 IUT source-facing route.

The source-facing core, finite labels, Step (x), Gaussian/Hodge--Arakelov
support, Theorem 3.11 source layer, IUT IV algebra shadows, Step (xi)
hull/determinant/IPL source layer, and realified-Frobenioid/log-Kummer endpoint
audit layer live in earlier Stage 1 modules; this file contains the remaining
structured endpoint audit refinements around IUT III, Corollary 3.12.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

namespace IUTStage1SourcePackage

variable {source target : Copy} {index : Type u}

namespace PlaceAuditedMultiradialThetaHullEndpoint

variable {coric : Type u} {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)}
variable {obligations : IUTStage1SourceHullDetObligations package}

namespace LogVolumeChartAudit

variable {endpoint : package.PlaceAuditedMultiradialThetaHullEndpoint obligations}

namespace FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    cuspClassLocalObject_eq_packetLocalObject := by
      intro audited label
      exact
        (part.localObjectTransport audited).cuspClass_transports_to_packet'
          label,
    zeroLocalObject_eq_packetLocalObject := by
      intro audited
      exact (part.localObjectTransport audited).zero_transports_to_packet' }

def toHodgeDescentInsulatedCuspZeroBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentInsulatedCuspZeroBridgeAudit l :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.toHodgeDescentInsulatedCuspZeroBridgeAudit

theorem localObjectTransport_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectTransport audited).checkpoint_eq_fourthTriangle

def localObjectSquareWeightBoundary
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
      l part.bundle.hodgeTheaterDescentBridgeData
      (part.insulated_route.zeroLocalObject audited)
      (part.insulated_route.cuspClassLocalObject audited)
      audited.choice.local_tensor_state.packetState.localObject :=
  { localObjectTransport := part.localObjectTransport audited }

theorem localObjectSquareWeightBoundary_coordinateEquiv_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.coordinateEquiv ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).coordinateEquiv_missing

theorem localObjectSquareWeightBoundary_squareWeightPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.squareWeightPreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).squareWeightPreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.fullLabelLogVolumePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelLogVolumePreservation_missing

theorem localObjectSquareWeightBoundary_coordinateSquarePreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).coordinateSquarePreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelMapPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelMapPreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelValuePreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelValuePreservation_missing

theorem zeroLocalObject_eq_packetLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.insulated_route.zeroLocalObject audited =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectTransport audited).zero_transports_to_packet'

theorem cuspClassLocalObject_eq_packetLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.cuspClassLocalObject audited label =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectTransport audited).cuspClass_transports_to_packet' label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectTransport audited).zero_eq_cuspClass label

theorem bridgeSource_eq_hodgeTheaterDescentPacketTransport
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    let transport := part.toHodgeDescentPacketTransportAudit
    transport.toHodgeDescentInsulatedCuspZeroBridgeAudit.classified_bridge.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.hodgeTheaterDescentPacketTransport :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.bridgeSource_eq_hodgeTheaterDescentPacketTransport

theorem comparisonSource_eq_hodgeTheaterDescent
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    let transport := part.toHodgeDescentPacketTransportAudit
    let hodgeBridge := transport.toHodgeDescentInsulatedCuspZeroBridgeAudit
    hodgeBridge.toSourcedInsulatedCuspZeroPacketBridgeAudit.comparison_source =
      IUTStage1InsulatedCuspZeroBridgeSource.hodgeTheaterDescentIndeterminacy :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.comparisonSource_eq_hodgeTheaterDescent

end FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toStructuredHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectTransport := fun audited =>
      (part.localObjectOperation audited).toLocalObjectTransportData }

def toHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentPacketTransportAudit l :=
  let structured := part.toStructuredHodgeDescentPacketTransportAudit
  structured.toHodgeDescentPacketTransportAudit

theorem zeroOperation_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).zeroOperation_descent_eq_hodgeData

theorem cuspClassOperation_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).cuspClassOperation_descent_eq_hodgeData
    label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

theorem bridgeSource_eq_hodgeTheaterDescentPacketTransport
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    let structured := part.toStructuredHodgeDescentPacketTransportAudit
    let transport := structured.toHodgeDescentPacketTransportAudit
    transport.toHodgeDescentInsulatedCuspZeroBridgeAudit.classified_bridge.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.hodgeTheaterDescentPacketTransport :=
  let structured := part.toStructuredHodgeDescentPacketTransportAudit
  structured.bridgeSource_eq_hodgeTheaterDescentPacketTransport

end FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toOperatedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      (part.localObjectOperation audited).toCuspZeroLocalObjectOperationData }

def toStructuredHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l :=
  let operated := part.toOperatedHodgeDescentPacketTransportAudit
  operated.toStructuredHodgeDescentPacketTransportAudit

theorem zeroSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput :=
  (part.localObjectOperation audited).zeroSourceRole_eq

theorem cuspClassSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation :=
  (part.localObjectOperation audited).cuspClassSourceRole_eq label

theorem zeroTargetRole_eq_packet
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  (part.localObjectOperation audited).zeroTargetRole_eq_packet

theorem cuspClassTargetRole_eq_packet
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  (part.localObjectOperation audited).cuspClassTargetRole_eq_packet label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toRoleMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      (part.localObjectOperation audited).toRoleMarkedCuspZeroLocalObjectOperationData }

def toOperatedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.toOperatedHodgeDescentPacketTransportAudit

theorem zeroSource_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectOperation audited).zeroSource_checkpoint_eq_fourthTriangle

theorem cuspClassSource_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectOperation audited).cuspClassSource_checkpoint_eq_fourthTriangle
    label

theorem packetTarget_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).packetTarget.descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).packetTarget_descent_eq_hodgeData

theorem zeroSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    ((part.toRoleMarkedHodgeDescentPacketTransportAudit).localObjectOperation
        audited).zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.zeroSourceRole_eq audited

theorem cuspClassSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
    ((roleMarked.localObjectOperation audited).cuspClassOperation label).sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.cuspClassSourceRole_eq audited label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toSourceMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      let operation := part.localObjectOperation audited
      operation.toSourceMarkedCuspZeroLocalObjectOperationData }

def toRoleMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l :=
  let sourceMarked := part.toSourceMarkedHodgeDescentPacketTransportAudit
  sourceMarked.toRoleMarkedHodgeDescentPacketTransportAudit

theorem cuspClassLabel_eq_zmodCoordinate
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        ((part.localObjectOperation audited).cuspClassSource label).coordinate
        ((part.localObjectOperation audited).cuspClassSource label).coordinate_ne_zero :=
  (part.localObjectOperation audited).cuspClassLabel_eq_zmodCoordinate label

theorem cuspClassLabel_eq_negCoordinate
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        (-((part.localObjectOperation audited).cuspClassSource label).coordinate)
        (zmod_neg_ne_zero_of_ne_zero l
          ((part.localObjectOperation audited).cuspClassSource label).coordinate_ne_zero) :=
  (part.localObjectOperation audited).cuspClassLabel_eq_negCoordinate label

theorem cuspClassLabel_eq_canonical_of_coordinate_eq_one
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient)
    (hcoord :
      ((part.localObjectOperation audited).cuspClassSource label).coordinate =
        (1 : ZMod l.value)) :
    label = zmodCanonicalSignLabelQuotient l :=
  (part.localObjectOperation audited).cuspClassLabel_eq_canonical_of_coordinate_eq_one
    label hcoord

def fullLabelLocalObject
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : IUTStage1ZModCuspFullLabel l) :
    IUTStage1FiniteLocalLogVolumeObject kind :=
  (part.localObjectOperation audited).fullLabelLocalObject label

theorem fullLabelLocalObject_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.fullLabelLocalObject audited IUTStage1ZModCuspFullLabel.zero =
      part.insulated_route.zeroLocalObject audited :=
  rfl

theorem fullLabelLocalObject_nonzero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.nonzero label) =
      part.insulated_route.cuspClassLocalObject audited label :=
  rfl

theorem fullLabelLocalObject_transports_to_packet
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : IUTStage1ZModCuspFullLabel l) :
    part.fullLabelLocalObject audited label =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectOperation audited).fullLabelLocalObject_transports_to_packet label

theorem fullLabelLocalObject_fromCoordinate_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (0 : ZMod l.value)) =
      part.insulated_route.zeroLocalObject audited := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  rfl

theorem fullLabelLocalObject_fromCoordinate_nonzero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (j : ZMod l.value) (hj : j ≠ 0) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      part.insulated_route.cuspClassLocalObject audited
        (zmodSignLabelFromCoordinate l j hj) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
  rfl

theorem cuspClassCoordinate_ne_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassSource label).coordinate ≠ 0 :=
  (part.localObjectOperation audited).cuspClassCoordinate_ne_zero label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toZModPacketNormalizedRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaZModPacketNormalizedRouteAudit l :=
  part.toDirectPacketNormalizedLocalObjectRouteAudit.toZModPacketNormalizedRouteAudit

def toConstantZModPacketNormalizedRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaConstantZModPacketNormalizedRouteAudit l :=
  part.toZModPacketNormalizedRouteAudit.toConstantZModPacketNormalizedRouteAudit

theorem thetaSourceAverage_eq_packetNormalized
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.theta_source.thetaSourceAverage audited =
      audited.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  let constantRoute := part.toConstantZModPacketNormalizedRouteAudit
  constantRoute.thetaSourceAverage_eq_packetNormalized audited

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited :=
  let constantRoute := part.toConstantZModPacketNormalizedRouteAudit
  constantRoute.targetSigned_le_thetaSourceAverage audited

def toInsulatedCuspZeroPacketBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaInsulatedCuspZeroPacketBridgeAudit l :=
  { insulated_route :=
      { theta_source := part.theta_source,
        ind12_equality_part := part.ind12_equality_part,
        ind3_upper_part := part.ind3_upper_part,
        theta_images_eq_endpoint := part.theta_images_eq_endpoint,
        cuspClassLocalObject := by
          intro audited _label
          exact audited.choice.local_tensor_state.packetState.localObject,
        cuspClassLogVolume_eq_localObjectFinite :=
          part.cuspClassLogVolume_eq_localObjectFinite,
        zeroLocalObject := by
          intro audited
          exact audited.choice.local_tensor_state.packetState.localObject,
        zeroLogVolume_eq_localObjectFinite :=
          part.zeroLogVolume_eq_localObjectFinite },
    packetLocalObjectEstimate := by
      intro audited
      exact
        (part.directNormalization audited).toLocalObjectContainerEstimateOfCapsuleEstimates
          (part.targetCapsuleEstimates audited),
    packetLocalObjectEstimate_eq_packetLocalObject := by
      intro _audited
      rfl,
    cuspClassLocalObject_eq_packetLocalObject := by
      intro _audited _label
      rfl,
    zeroLocalObject_eq_packetLocalObject := by
      intro _audited
      rfl }

open FLZModCuspLabelThetaClassifiedInsulatedCuspZeroPacketBridgeAudit in
def toClassifiedInsulatedCuspZeroPacketBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaClassifiedInsulatedCuspZeroPacketBridgeAudit l :=
  ofDirectLocalLabelObjectConstruction
    part.toInsulatedCuspZeroPacketBridgeAudit

theorem insulatedPacketBridgeSource_eq_direct
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    part.toClassifiedInsulatedCuspZeroPacketBridgeAudit.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.directLocalLabelObjectConstruction :=
  rfl

end FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit

namespace FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toDirectIdentifiedLocalPacketRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l :=
  { theta_source := part.direct_packet.theta_source,
    ind12_equality_part := part.direct_packet.ind12_equality_part,
    ind3_upper_part := part.direct_packet.ind3_upper_part,
    theta_images_eq_endpoint := part.direct_packet.theta_images_eq_endpoint,
    targetCapsuleEstimates := part.targetCapsuleEstimates,
    directNormalization := part.direct_packet.zeroDirectNormalization,
    cuspClassLogVolume_eq_localObjectFinite := by
      intro audited label
      let estimate := part.direct_packet.cuspClassObjectEstimate audited label
      calc
        (part.direct_packet.theta_source.compatible_average.cuspLogVolume
          audited).cuspClassLogVolume label =
            estimate.localObject.finiteLogVolume :=
          estimate.localLogVolume_eq_object
        _ =
            audited.choice.local_tensor_state.packetState.localObject.finiteLogVolume := by
          rw [part.direct_packet.cuspClassObject_eq_packetLocalObject audited label],
    zeroLogVolume_eq_localObjectFinite := by
      intro audited
      let estimate := part.direct_packet.zeroObjectEstimate audited
      calc
        (part.direct_packet.theta_source.compatible_average.cuspLogVolume
          audited).zeroLogVolume =
            estimate.localObject.finiteLogVolume :=
          estimate.localLogVolume_eq_object
        _ =
            audited.choice.local_tensor_state.packetState.localObject.finiteLogVolume := by
          rw [part.direct_packet.zeroObject_eq_packetLocalObject audited] }

def toDirectCapsuleCuspClassAudit
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaDirectCapsuleCuspClassAudit l :=
  { packet_normalized :=
      part.direct_packet.toClassifiedPacketNormalizedAudit.packet_normalized,
    targetCapsuleEstimates := part.targetCapsuleEstimates }

def toFullClassifiedRouteSummary
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaFullClassifiedRouteSummary l :=
  let packetSummary := part.direct_packet.toClassifiedPacketNormalizedAudit
  let direct := part.toDirectCapsuleCuspClassAudit
  FLZModCuspLabelThetaFullClassifiedRouteSummary.ofDirectCapsule
    packetSummary direct rfl

theorem packetIdentificationSource_eq_direct
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.packetIdentificationSource =
      IUTStage1PacketNormalizedIdentificationSource.directPacketNormalization :=
  rfl

theorem cuspBoundSource_eq_directCapsule
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.cuspBoundSource =
      IUTStage1CuspClassBoundSource.directCapsuleEstimates :=
  rfl

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.direct_packet.theta_source.thetaSourceAverage audited :=
  let identifiedRoute := part.toDirectIdentifiedLocalPacketRouteAudit
  identifiedRoute.targetSigned_le_thetaSourceAverage audited

end FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit

namespace FLZModCuspLabelThetaPacketLocalObjectContainerAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

theorem targetSigned_le_thetaSourceAverage_of_directPacket
    (part : audit.FLZModCuspLabelThetaPacketLocalObjectContainerAudit l)
    (directNormalization :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1DirectPacketNormalizationData
          audited.choice.local_tensor_state.packetState)
    (targetCapsuleEstimates :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1TypedCapsuleFamilyContainerEstimate
          package.preLedger.targetVolume.targetSigned
          audited.choice.local_tensor_state.packetState.capsuleFamily)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited := by
  let directRoute :=
    part.toDirectLocalPacketDirectCapsuleRouteAudit
      directNormalization targetCapsuleEstimates
  exact directRoute.targetSigned_le_thetaSourceAverage audited

end FLZModCuspLabelThetaPacketLocalObjectContainerAudit

namespace FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

theorem targetSigned_le_thetaSourceAverage_of_directPacket
    (part : audit.FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit l)
    (directNormalization :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1DirectPacketNormalizationData
          audited.choice.local_tensor_state.packetState)
    (targetCapsuleEstimates :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1TypedCapsuleFamilyContainerEstimate
          package.preLedger.targetVolume.targetSigned
          audited.choice.local_tensor_state.packetState.capsuleFamily)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.packet_local_object.theta_source.thetaSourceAverage audited :=
  part.packet_local_object.targetSigned_le_thetaSourceAverage_of_directPacket
    directNormalization targetCapsuleEstimates audited

end FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit

namespace FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toInd2TransportedCuspClassAudit
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaInd2TransportedCuspClassAudit l :=
  { packet_normalized :=
      part.ind2_packet.toClassifiedPacketNormalizedAudit.packet_normalized,
    sourceAudited := part.ind2_packet.sourceAudited,
    ind2_step := part.ind2_packet.ind2_step,
    sourceCapsuleEstimates := part.sourceCapsuleEstimates }

def toFullClassifiedRouteSummary
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaFullClassifiedRouteSummary l :=
  let packetSummary := part.ind2_packet.toClassifiedPacketNormalizedAudit
  let transported := part.toInd2TransportedCuspClassAudit
  FLZModCuspLabelThetaFullClassifiedRouteSummary.ofInd2Transport
    packetSummary transported rfl

theorem packetIdentificationSource_eq_ind2Transported
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.packetIdentificationSource =
      IUTStage1PacketNormalizedIdentificationSource.ind2TransportedPacketNormalization :=
  rfl

theorem cuspBoundSource_eq_ind2Transported
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.cuspBoundSource =
      IUTStage1CuspClassBoundSource.ind2TransportedCapsuleEstimates :=
  rfl

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.ind2_packet.theta_source.thetaSourceAverage audited :=
  let transported := part.toInd2TransportedCuspClassAudit
  transported.targetSigned_le_thetaAverage audited

end FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit

namespace FLZModCuspLabelThetaContainerBoundAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def comparisonLevel
    (_part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.hullLogVolume

theorem comparisonLevel_eq_hullLogVolume
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel =
      IUTStage1SquareComparisonLevel.hullLogVolume :=
  rfl

theorem comparisonLevel_ne_pointwiseRepresentative
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_aggregateRepresentative
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.aggregateRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem comparisonLevel_ne_structuredSHEFactored
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    part.comparisonLevel ≠ obligations.comparisonLevel := by
  rw [part.comparisonLevel_eq_hullLogVolume,
    obligations.comparisonLevel_eq_pointwiseRepresentative]
  exact IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_squareWeightedAverage
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (averagePart : audit.FLZModCuspLabelCompatibleAveragedInd12Audit l) :
    part.comparisonLevel ≠
      averagePart.squareWeightedAverageComparisonLevel := by
  rw [part.comparisonLevel_eq_hullLogVolume,
    averagePart.squareWeightedAverageComparisonLevel_eq_aggregate]
  exact IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem boundSource_not_ind3Only
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.bound_source ≠ IUTStage1TargetAverageBoundSource.ind3UpperSemiOnly :=
  part.bound_source_not_ind3_only

theorem targetSigned_le_thetaAverage'
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited :=
  part.targetSigned_le_thetaAverage audited

theorem ind3TargetSigned_le_thetaSigned
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  part.ind3_upper_part.targetSigned_le_thetaSigned

def toTargetAverageReductionAudit
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    audit.FLZModCuspLabelTargetAverageReductionAudit l :=
  { theta_source := part.theta_source,
    ind12_equality_part := part.ind12_equality_part,
    targetSigned_le_thetaAverage := part.targetSigned_le_thetaAverage }

theorem qSigned_le_thetaSourceAverage
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.qSigned <= part.theta_source.thetaSourceAverage audited :=
  part.toTargetAverageReductionAudit.qSigned_le_thetaSourceAverage audited

theorem qSigned_le_thetaSigned_via_average
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  part.toTargetAverageReductionAudit.toQThetaComparisonAudit_qSigned_le_thetaSigned
    audited

theorem targetSigned_le_thetaSigned_via_average
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <= package.preLedger.thetaSigned :=
  part.toTargetAverageReductionAudit.targetSigned_le_thetaSigned_via_average
    audited

end FLZModCuspLabelThetaContainerBoundAudit

end LogVolumeChartAudit

end PlaceAuditedMultiradialThetaHullEndpoint

theorem auditOfParts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    Audit package (package.obligationsFromParts subclaims sideConditions) :=
  package.audit (package.obligationsFromParts subclaims sideConditions)

theorem auditOfHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Audit package (package.obligationsFromHypotheses subclaims hypotheses) :=
  package.audit (package.obligationsFromHypotheses subclaims hypotheses)

theorem auditOfStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    Audit package
      (package.obligationsFromStructuredInputs inputs sideConditions) :=
  package.audit
    (package.obligationsFromStructuredInputs inputs sideConditions)

theorem auditOfStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Audit package
      (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  package.audit
    (package.obligationsFromStructuredHypotheses inputs hypotheses)

theorem sideConditionAuditOfHypotheses
    (package : IUTStage1SourcePackage source target index)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    IUTStage1SourceSideConditionHypotheses.Audit hypotheses :=
  hypotheses.audit

/--
Combined audit for the hypothesis-based package route.

The record keeps the side-condition-hypothesis audit separate from the source
package audit while making both available to downstream consumers.
-/
structure HypothesisRouteAudit
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Prop where
  side_condition_audit :
    IUTStage1SourceSideConditionHypotheses.Audit hypotheses
  source_audit :
    Audit package (package.obligationsFromHypotheses subclaims hypotheses)

theorem hypothesisRouteAudit
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    HypothesisRouteAudit package subclaims hypotheses :=
  { side_condition_audit :=
      package.sideConditionAuditOfHypotheses hypotheses,
    source_audit := package.auditOfHypotheses subclaims hypotheses }

namespace HypothesisRouteAudit

variable {package : IUTStage1SourcePackage source target index}
variable {subclaims : IUTStage1Theorem311Subclaims package}
variable {hypotheses : IUTStage1SourceSideConditionHypotheses package}

theorem sideConditionAudit
    (audit : HypothesisRouteAudit package subclaims hypotheses) :
    IUTStage1SourceSideConditionHypotheses.Audit hypotheses :=
  audit.side_condition_audit

theorem sourceAudit
    (audit : HypothesisRouteAudit package subclaims hypotheses) :
    Audit package (package.obligationsFromHypotheses subclaims hypotheses) :=
  audit.source_audit

theorem qPilotLogVolumePositive
    (audit : HypothesisRouteAudit package subclaims hypotheses) :
    0 < -package.preLedger.qSigned :=
  audit.sideConditionAudit.qPilotLogVolumePositive

theorem qSignedLeThetaSigned
    (audit : HypothesisRouteAudit package subclaims hypotheses) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  audit.sourceAudit.qSigned_le_thetaSigned

end HypothesisRouteAudit

/--
Structured-input analogue of `HypothesisRouteAudit`.

The side-condition audit remains separate from the source-package audit; the
only difference is that the Theorem 3.11 data is supplied via structured inputs.
-/
structure StructuredHypothesisRouteAudit
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Prop where
  side_condition_audit :
    IUTStage1SourceSideConditionHypotheses.Audit hypotheses
  source_audit :
    Audit package
      (package.obligationsFromStructuredHypotheses inputs hypotheses)

theorem structuredHypothesisRouteAudit
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    StructuredHypothesisRouteAudit package inputs hypotheses :=
  { side_condition_audit :=
      package.sideConditionAuditOfHypotheses hypotheses,
    source_audit := package.auditOfStructuredHypotheses inputs hypotheses }

namespace StructuredHypothesisRouteAudit

variable {package : IUTStage1SourcePackage source target index}
variable {inputs : IUTStage1Theorem311StructuredInputs package}
variable {hypotheses : IUTStage1SourceSideConditionHypotheses package}

theorem sideConditionAudit
    (audit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    IUTStage1SourceSideConditionHypotheses.Audit hypotheses :=
  audit.side_condition_audit

theorem sourceAudit
    (audit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    Audit package
      (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  audit.source_audit

theorem qPilotLogVolumePositive
    (audit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    0 < -package.preLedger.qSigned :=
  audit.sideConditionAudit.qPilotLogVolumePositive

theorem qSignedLeThetaSigned
    (audit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  audit.sourceAudit.qSigned_le_thetaSigned

theorem auditedPublicEndpoint
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
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
                  inputs hypotheses)).ledger.qSigned_le_thetaSigned)) =
        package.publicAuditOfStructuredHypotheses inputs hypotheses :=
  ⟨routeAudit.sourceAudit, Subsingleton.elim _ _⟩

end StructuredHypothesisRouteAudit

theorem hypothesisRouteAudit_sideConditionAudit_eq
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.hypothesisRouteAudit subclaims hypotheses).sideConditionAudit =
      package.sideConditionAuditOfHypotheses hypotheses :=
  rfl

theorem hypothesisRouteAudit_sourceAudit_eq
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.hypothesisRouteAudit subclaims hypotheses).sourceAudit =
      package.auditOfHypotheses subclaims hypotheses :=
  rfl

theorem auditOfHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditOfHypotheses subclaims hypotheses =
      package.auditOfParts subclaims hypotheses.toSideConditions :=
  rfl

theorem auditOfStructuredInputs_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.auditOfStructuredInputs inputs sideConditions =
      package.auditOfParts inputs.theorem311Subclaims sideConditions :=
  rfl

theorem auditOfStructuredHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditOfStructuredHypotheses inputs hypotheses =
      package.auditOfStructuredInputs inputs hypotheses.toSideConditions :=
  rfl

theorem auditOfStructuredHypotheses_eq_hypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditOfStructuredHypotheses inputs hypotheses =
      package.auditOfHypotheses inputs.theorem311Subclaims hypotheses :=
  rfl

theorem structuredHypothesisRouteAudit_sideConditionAudit_eq
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredHypothesisRouteAudit
      inputs hypotheses).sideConditionAudit =
      package.sideConditionAuditOfHypotheses hypotheses :=
  rfl

theorem structuredHypothesisRouteAudit_sourceAudit_eq
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredHypothesisRouteAudit inputs hypotheses).sourceAudit =
      package.auditOfStructuredHypotheses inputs hypotheses :=
  rfl

theorem structuredHypothesisRouteAudit_sourceAudit_eq_hypothesisRoute
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredHypothesisRouteAudit inputs hypotheses).sourceAudit =
      (package.hypothesisRouteAudit
        inputs.theorem311Subclaims hypotheses).sourceAudit :=
  rfl

theorem auditedPublicEndpoint
    (package : IUTStage1SourcePackage source target index)
    (obligations : IUTStage1SourceObligations package) :
    ∃ sourceAudit : Audit package obligations,
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
        package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
          Corollary312Inequality
            (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
            (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
          (corollary312_from_stage1_comparison
              (package.promotedProvider obligations).stage1Comparison =
            corollary312_of_signed_le
              (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned)) =
        package.publicAudit obligations :=
  ⟨package.audit obligations, Subsingleton.elim _ _⟩

namespace ComparisonDataEndpoint

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceObligations package}

theorem auditedPublicEndpoint
    (_endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
        package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
          Corollary312Inequality
            (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
            (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
          (corollary312_from_stage1_comparison
              (package.promotedProvider obligations).stage1Comparison =
            corollary312_of_signed_le
              (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned)) =
        package.publicAudit obligations :=
  package.auditedPublicEndpoint obligations

end ComparisonDataEndpoint

theorem auditedPublicEndpointOfGap
    (package : IUTStage1SourcePackage source target index)
    (gap : IUTStage1SourceObligationGap package) :
    ∃ sourceAudit : Audit package gap.toSourceObligations,
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
        package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
          Corollary312Inequality
            (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
            (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
          (corollary312_from_stage1_comparison
              (package.promotedProvider gap.toSourceObligations).stage1Comparison =
            corollary312_of_signed_le
              (package.promotedProvider
                gap.toSourceObligations).ledger.qSigned_le_thetaSigned)) =
        package.publicAudit gap.toSourceObligations :=
  package.auditedPublicEndpoint gap.toSourceObligations

theorem auditedPublicEndpointOfParts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    ∃ sourceAudit :
        Audit package (package.obligationsFromParts subclaims sideConditions),
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
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
                  subclaims sideConditions)).ledger.qSigned_le_thetaSigned)) =
        package.publicAuditOfParts subclaims sideConditions :=
  package.auditedPublicEndpoint
    (package.obligationsFromParts subclaims sideConditions)

theorem auditedPublicEndpointOfHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package (package.obligationsFromHypotheses subclaims hypotheses),
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
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
                  subclaims hypotheses)).ledger.qSigned_le_thetaSigned)) =
        package.publicAuditOfHypotheses subclaims hypotheses :=
  package.auditedPublicEndpoint
    (package.obligationsFromHypotheses subclaims hypotheses)

theorem auditedPublicEndpointOfHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedPublicEndpointOfHypotheses subclaims hypotheses =
      package.auditedPublicEndpointOfParts
        subclaims hypotheses.toSideConditions :=
  Subsingleton.elim _ _

theorem auditedPublicEndpointOfStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredInputs inputs sideConditions),
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
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
                  inputs sideConditions)).ledger.qSigned_le_thetaSigned)) =
        package.publicAuditOfStructuredInputs inputs sideConditions :=
  package.auditedPublicEndpoint
    (package.obligationsFromStructuredInputs inputs sideConditions)

theorem auditedPublicEndpointOfStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      (⟨sourceAudit.qSigned_le_thetaSigned,
          sourceAudit.corollary312,
          sourceAudit.stage_recovers_qSigned_le_thetaSigned⟩ :
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
                  inputs hypotheses)).ledger.qSigned_le_thetaSigned)) =
        package.publicAuditOfStructuredHypotheses inputs hypotheses :=
  package.auditedPublicEndpoint
    (package.obligationsFromStructuredHypotheses inputs hypotheses)

theorem auditedPublicEndpointOfStructuredInputs_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.auditedPublicEndpointOfStructuredInputs
        inputs sideConditions =
      package.auditedPublicEndpointOfParts
        inputs.theorem311Subclaims sideConditions :=
  Subsingleton.elim _ _

theorem auditedPublicEndpointOfStructuredHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedPublicEndpointOfStructuredHypotheses
        inputs hypotheses =
      package.auditedPublicEndpointOfStructuredInputs
        inputs hypotheses.toSideConditions :=
  Subsingleton.elim _ _

theorem auditedPublicEndpointOfStructuredHypotheses_eq_hypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedPublicEndpointOfStructuredHypotheses
        inputs hypotheses =
      package.auditedPublicEndpointOfHypotheses
        inputs.theorem311Subclaims hypotheses :=
  Subsingleton.elim _ _

theorem auditedComparisonDataEndpointOfGap
    (package : IUTStage1SourcePackage source target index)
    (gap : IUTStage1SourceObligationGap package) :
    package.ComparisonDataEndpoint gap.toSourceObligations :=
  package.auditedComparisonDataEndpoint gap.toSourceObligations

theorem auditedComparisonDataEndpointOfParts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.ComparisonDataEndpoint
      (package.obligationsFromParts subclaims sideConditions) :=
  package.auditedComparisonDataEndpoint
    (package.obligationsFromParts subclaims sideConditions)

theorem auditedComparisonDataEndpointOfHypotheses
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.ComparisonDataEndpoint
      (package.obligationsFromHypotheses subclaims hypotheses) :=
  package.auditedComparisonDataEndpoint
    (package.obligationsFromHypotheses subclaims hypotheses)

theorem auditedComparisonDataEndpointOfHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (subclaims : IUTStage1Theorem311Subclaims package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedComparisonDataEndpointOfHypotheses subclaims hypotheses =
      package.auditedComparisonDataEndpointOfParts
        subclaims hypotheses.toSideConditions :=
  Subsingleton.elim _ _

theorem auditedComparisonDataEndpointOfStructuredInputs
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.ComparisonDataEndpoint
      (package.obligationsFromStructuredInputs inputs sideConditions) :=
  package.auditedComparisonDataEndpoint
    (package.obligationsFromStructuredInputs inputs sideConditions)

theorem auditedComparisonDataEndpointOfStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.ComparisonDataEndpoint
      (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  package.auditedComparisonDataEndpoint
    (package.obligationsFromStructuredHypotheses inputs hypotheses)

theorem auditedComparisonDataEndpointOfStructuredInputs_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (sideConditions : IUTStage1SourceSideConditions package) :
    package.auditedComparisonDataEndpointOfStructuredInputs
        inputs sideConditions =
      package.auditedComparisonDataEndpointOfParts
        inputs.theorem311Subclaims sideConditions :=
  Subsingleton.elim _ _

theorem auditedComparisonDataEndpointOfStructuredHypotheses_eq_parts
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedComparisonDataEndpointOfStructuredHypotheses
        inputs hypotheses =
      package.auditedComparisonDataEndpointOfStructuredInputs
        inputs hypotheses.toSideConditions :=
  Subsingleton.elim _ _

theorem auditedComparisonDataEndpointOfStructuredHypotheses_eq_hypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    package.auditedComparisonDataEndpointOfStructuredHypotheses
        inputs hypotheses =
      package.auditedComparisonDataEndpointOfHypotheses
        inputs.theorem311Subclaims hypotheses :=
  Subsingleton.elim _ _

namespace Audit

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceObligations package}

theorem inputMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.input = package.labels.input :=
  sourceAudit.input_matches_labels

theorem multiradialOutputMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.multiradialOutput = package.labels.multiradialOutput :=
  sourceAudit.multiradialOutput_matches_labels

theorem logVolumeComparisonMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.logVolumeComparison = package.labels.logVolumeComparison :=
  sourceAudit.logVolumeComparison_matches_labels

theorem thetaPilotMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.thetaPilot = package.labels.thetaPilot :=
  sourceAudit.thetaPilot_matches_labels

theorem qPilotMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.qPilot = package.labels.qPilot :=
  sourceAudit.qPilot_matches_labels

theorem logKummerMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.logKummer = package.labels.logKummer :=
  sourceAudit.logKummer_matches_labels

theorem indeterminaciesMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.indeterminacies = package.labels.indeterminacies :=
  sourceAudit.indeterminacies_matches_labels

theorem qPilotLogVolumeMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.qPilotLogVolume = package.labels.qPilotLogVolume :=
  sourceAudit.qPilotLogVolume_matches_labels

theorem sourceNormalizationMatchesLabels
    (sourceAudit : Audit package obligations) :
    package.sourceNormalizationLabel = package.labels.sourceNormalization :=
  sourceAudit.sourceNormalization_matches_labels

theorem algorithmCertified
    (sourceAudit : Audit package obligations) :
    package.preLedger.output.Certified :=
  sourceAudit.algorithm_certified

theorem sheArrowMatchesCertificate
    (sourceAudit : Audit package obligations) :
    package.preLedger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      package.preLedger.certificate.she :=
  sourceAudit.she_arrow_matches_certificate

theorem qPilotPositive
    (sourceAudit : Audit package obligations) :
    0 < -package.preLedger.qSigned :=
  sourceAudit.q_pilot_positive

theorem sourceNormalization
    (sourceAudit : Audit package obligations) :
    package.preLedger.normalization :=
  sourceAudit.normalization

theorem promotedProviderLedger
    (sourceAudit : Audit package obligations) :
    (package.promotedProvider obligations).ledger =
      package.promotedLedger obligations :=
  sourceAudit.promoted_provider_ledger

def comparisonPayloadInputs
    (_sourceAudit : Audit package obligations) :
    package.preLedger.ComparisonPayloadInputs :=
  package.comparisonPayloadInputs

theorem comparisonPayloadInputsEqPackage
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonPayloadInputs =
      package.comparisonPayloadInputs :=
  Subsingleton.elim _ _

theorem comparisonPayloadInputsQSignedLeThetaSigned
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonPayloadInputs.qSignedLeThetaSigned =
      package.comparisonPayloadInputs.qSignedLeThetaSigned :=
  Subsingleton.elim _ _

theorem comparisonPayloadInputsEqPreLedgerAudit
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonPayloadInputs =
      package.preLedger.audit.comparisonPayloadInputs :=
  Subsingleton.elim _ _

def comparisonData
    (_sourceAudit : Audit package obligations) :
    Corollary312ComparisonData :=
  package.comparisonData obligations

theorem comparisonDataEqPackage
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonData = package.comparisonData obligations :=
  rfl

theorem comparisonDataFromPayloadInputsEqComparisonData
    (sourceAudit : Audit package obligations) :
    package.comparisonDataFromPayloadInputs obligations =
      sourceAudit.comparisonData :=
  package.comparisonDataFromPayloadInputs_eq_comparisonData obligations

theorem comparisonDataFromPayloadInputsStage1ComparisonEq
    (sourceAudit : Audit package obligations) :
    (package.comparisonDataFromPayloadInputs obligations).stage1Comparison =
      sourceAudit.comparisonData.stage1Comparison :=
  package.comparisonDataFromPayloadInputs_stage1Comparison_eq obligations

theorem comparisonDataStage1Comparison
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonData.stage1Comparison =
      (package.promotedProvider obligations).stage1Comparison :=
  package.comparisonData_stage1Comparison_eq obligations

theorem comparisonDataCorollary312
    (sourceAudit : Audit package obligations) :
    sourceAudit.comparisonData.corollary312 =
      (package.promotedProvider obligations).corollary312 :=
  package.comparisonData_corollary312_eq obligations

theorem qSignedLeThetaSigned
    (sourceAudit : Audit package obligations) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  sourceAudit.qSigned_le_thetaSigned

theorem corollary312Endpoint
    (sourceAudit : Audit package obligations) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
      (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) :=
  sourceAudit.corollary312

theorem stageRecoversQSignedLeThetaSigned
    (sourceAudit : Audit package obligations) :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      corollary312_of_signed_le
        (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned :=
  sourceAudit.stage_recovers_qSigned_le_thetaSigned

theorem stageRecoversCorollary312
    (sourceAudit : Audit package obligations) :
    corollary312_from_stage1_comparison
        (package.promotedProvider obligations).stage1Comparison =
      (package.promotedProvider obligations).ledger.corollary312 :=
  sourceAudit.stage_recovers_corollary312

/-- Compact summary of the audited route from source payload inputs to endpoint data. -/
structure PayloadRouteSummary
    (sourceAudit : Audit package obligations) : Prop where
  payload_inputs_eq_package :
    sourceAudit.comparisonPayloadInputs =
      package.comparisonPayloadInputs
  payload_data_eq_comparison_data :
    package.comparisonDataFromPayloadInputs obligations =
      sourceAudit.comparisonData
  comparison_data_eq_package :
    sourceAudit.comparisonData = package.comparisonData obligations
  stage1Comparison_eq_provider :
    sourceAudit.comparisonData.stage1Comparison =
      (package.promotedProvider obligations).stage1Comparison
  corollary312_eq_provider :
    sourceAudit.comparisonData.corollary312 =
      (package.promotedProvider obligations).corollary312
  comparison_data_recovers :
    corollary312_from_stage1_comparison
        sourceAudit.comparisonData.stage1Comparison =
      corollary312_of_signed_le
        sourceAudit.comparisonData.qSigned_le_thetaSigned

theorem payloadRouteSummary
    (sourceAudit : Audit package obligations) :
    PayloadRouteSummary sourceAudit :=
  { payload_inputs_eq_package :=
      sourceAudit.comparisonPayloadInputsEqPackage,
    payload_data_eq_comparison_data :=
      sourceAudit.comparisonDataFromPayloadInputsEqComparisonData,
    comparison_data_eq_package :=
      sourceAudit.comparisonDataEqPackage,
    stage1Comparison_eq_provider :=
      sourceAudit.comparisonDataStage1Comparison,
    corollary312_eq_provider :=
      sourceAudit.comparisonDataCorollary312,
    comparison_data_recovers :=
      sourceAudit.comparisonData.publicAudit_stage1Comparison_recovers }

theorem publicAuditEq
    (sourceAudit : Audit package obligations) :
    (⟨sourceAudit.qSignedLeThetaSigned,
        sourceAudit.corollary312Endpoint,
        sourceAudit.stageRecoversQSignedLeThetaSigned⟩ :
      package.preLedger.qSigned <= package.preLedger.thetaSigned ∧
        Corollary312Inequality
          (signedPilotLogVolume PilotSide.theta package.preLedger.thetaSigned)
          (signedPilotLogVolume PilotSide.q package.preLedger.qSigned) ∧
        (corollary312_from_stage1_comparison
            (package.promotedProvider obligations).stage1Comparison =
          corollary312_of_signed_le
            (package.promotedProvider obligations).ledger.qSigned_le_thetaSigned)) =
      package.publicAudit obligations :=
  Subsingleton.elim _ _

end Audit

namespace ComparisonDataEndpoint

variable {package : IUTStage1SourcePackage source target index}
variable {obligations : IUTStage1SourceObligations package}

theorem payloadRouteSummaryExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      Audit.PayloadRouteSummary sourceAudit := by
  rcases endpoint with ⟨sourceAudit, _data, _hdata, _hle, _hcorollary, _hrecovers⟩
  exact ⟨sourceAudit, sourceAudit.payloadRouteSummary⟩

theorem payloadRouteSummaryAndPublicAudit
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      Audit.PayloadRouteSummary sourceAudit ∧
        endpoint.publicAudit = package.publicAudit obligations := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary, endpoint.publicAudit_eq_package_publicAudit⟩

theorem payloadInputsEqPackageExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      sourceAudit.comparisonPayloadInputs =
        package.comparisonPayloadInputs := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.payload_inputs_eq_package⟩

theorem payloadDataEqComparisonDataExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      package.comparisonDataFromPayloadInputs obligations =
        sourceAudit.comparisonData := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.payload_data_eq_comparison_data⟩

theorem comparisonDataEqPackageExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      sourceAudit.comparisonData =
        package.comparisonData obligations := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.comparison_data_eq_package⟩

theorem stage1ComparisonEqProviderExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      sourceAudit.comparisonData.stage1Comparison =
        (package.promotedProvider obligations).stage1Comparison := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.stage1Comparison_eq_provider⟩

theorem corollary312EqProviderExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      sourceAudit.comparisonData.corollary312 =
        (package.promotedProvider obligations).corollary312 := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.corollary312_eq_provider⟩

theorem comparisonDataRecoversExists
    (endpoint : package.ComparisonDataEndpoint obligations) :
    ∃ sourceAudit : Audit package obligations,
      corollary312_from_stage1_comparison
          sourceAudit.comparisonData.stage1Comparison =
        corollary312_of_signed_le
          sourceAudit.comparisonData.qSigned_le_thetaSigned := by
  rcases endpoint.payloadRouteSummaryExists with ⟨sourceAudit, summary⟩
  exact ⟨sourceAudit, summary.comparison_data_recovers⟩

end ComparisonDataEndpoint

namespace StructuredHypothesisRouteAudit

variable {package : IUTStage1SourcePackage source target index}
variable {inputs : IUTStage1Theorem311StructuredInputs package}
variable {hypotheses : IUTStage1SourceSideConditionHypotheses package}

theorem payloadRouteSummary
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    Audit.PayloadRouteSummary routeAudit.sourceAudit :=
  routeAudit.sourceAudit.payloadRouteSummary

theorem comparisonDataEndpointPayloadRouteSummary
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      Audit.PayloadRouteSummary sourceAudit ∧
        (package.auditedComparisonDataEndpointOfStructuredHypotheses
          inputs hypotheses).publicAudit =
          package.publicAuditOfStructuredHypotheses inputs hypotheses := by
  let endpoint :=
    package.auditedComparisonDataEndpointOfStructuredHypotheses
      inputs hypotheses
  have hpublic :
      endpoint.publicAudit =
        package.publicAudit
          (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
    endpoint.publicAudit_eq_package_publicAudit
  exact ⟨routeAudit.sourceAudit, routeAudit.payloadRouteSummary, by
    simpa [IUTStage1SourcePackage.publicAuditOfStructuredHypotheses] using
      hpublic⟩

theorem payloadInputsEqPackage
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    routeAudit.sourceAudit.comparisonPayloadInputs =
      package.comparisonPayloadInputs :=
  routeAudit.payloadRouteSummary.payload_inputs_eq_package

theorem payloadDataEqComparisonData
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    package.comparisonDataFromPayloadInputs
        (package.obligationsFromStructuredHypotheses inputs hypotheses) =
      routeAudit.sourceAudit.comparisonData :=
  routeAudit.payloadRouteSummary.payload_data_eq_comparison_data

theorem comparisonDataEqPackage
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    routeAudit.sourceAudit.comparisonData =
      package.comparisonData
        (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  routeAudit.payloadRouteSummary.comparison_data_eq_package

theorem stage1ComparisonEqProvider
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    routeAudit.sourceAudit.comparisonData.stage1Comparison =
      (package.promotedProvider
        (package.obligationsFromStructuredHypotheses
          inputs hypotheses)).stage1Comparison :=
  routeAudit.payloadRouteSummary.stage1Comparison_eq_provider

theorem corollary312EqProvider
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    routeAudit.sourceAudit.comparisonData.corollary312 =
      (package.promotedProvider
        (package.obligationsFromStructuredHypotheses
          inputs hypotheses)).corollary312 :=
  routeAudit.payloadRouteSummary.corollary312_eq_provider

theorem comparisonDataRecovers
    (routeAudit : StructuredHypothesisRouteAudit package inputs hypotheses) :
    corollary312_from_stage1_comparison
        routeAudit.sourceAudit.comparisonData.stage1Comparison =
      corollary312_of_signed_le
        routeAudit.sourceAudit.comparisonData.qSigned_le_thetaSigned :=
  routeAudit.payloadRouteSummary.comparison_data_recovers

end StructuredHypothesisRouteAudit

theorem structuredEndpointPayloadInputsEqPackageExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      sourceAudit.comparisonPayloadInputs =
        package.comparisonPayloadInputs :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).payloadInputsEqPackageExists

theorem structuredEndpointPayloadDataEqComparisonDataExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      package.comparisonDataFromPayloadInputs
          (package.obligationsFromStructuredHypotheses inputs hypotheses) =
        sourceAudit.comparisonData :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).payloadDataEqComparisonDataExists

theorem structuredEndpointComparisonDataEqPackageExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      sourceAudit.comparisonData =
        package.comparisonData
          (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).comparisonDataEqPackageExists

theorem structuredEndpointStage1ComparisonEqProviderExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      sourceAudit.comparisonData.stage1Comparison =
        (package.promotedProvider
          (package.obligationsFromStructuredHypotheses
            inputs hypotheses)).stage1Comparison :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).stage1ComparisonEqProviderExists

theorem structuredEndpointCorollary312EqProviderExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      sourceAudit.comparisonData.corollary312 =
        (package.promotedProvider
          (package.obligationsFromStructuredHypotheses
            inputs hypotheses)).corollary312 :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).corollary312EqProviderExists

theorem structuredEndpointComparisonDataRecoversExists
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    ∃ sourceAudit :
        Audit package
          (package.obligationsFromStructuredHypotheses inputs hypotheses),
      corollary312_from_stage1_comparison
          sourceAudit.comparisonData.stage1Comparison =
        corollary312_of_signed_le
          sourceAudit.comparisonData.qSigned_le_thetaSigned :=
  (package.auditedComparisonDataEndpointOfStructuredHypotheses
    inputs hypotheses).comparisonDataRecoversExists

/--
Compact audit summary for the structured comparison-data endpoint.

The summary keeps one source audit witness while also recording that the
structured endpoint has the same public audit as the structured-hypothesis
route.
-/
structure StructuredEndpointAuditSummary
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    Prop where
  source_audit :
    Audit package
      (package.obligationsFromStructuredHypotheses inputs hypotheses)
  payload_route_summary :
    Audit.PayloadRouteSummary source_audit
  endpoint_public_audit_eq :
    (package.auditedComparisonDataEndpointOfStructuredHypotheses
      inputs hypotheses).publicAudit =
      package.publicAuditOfStructuredHypotheses inputs hypotheses

theorem structuredEndpointAuditSummary
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    StructuredEndpointAuditSummary package inputs hypotheses :=
  let routeAudit := package.structuredHypothesisRouteAudit inputs hypotheses
  { source_audit := routeAudit.sourceAudit,
    payload_route_summary := routeAudit.payloadRouteSummary,
    endpoint_public_audit_eq := by
      let endpoint :=
        package.auditedComparisonDataEndpointOfStructuredHypotheses
          inputs hypotheses
      have hpublic :
          endpoint.publicAudit =
            package.publicAudit
              (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
        endpoint.publicAudit_eq_package_publicAudit
      simpa [IUTStage1SourcePackage.publicAuditOfStructuredHypotheses] using
        hpublic }

theorem structuredEndpointAuditSummary_sourceAudit_eq_routeAudit
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredEndpointAuditSummary inputs hypotheses).source_audit =
      (package.structuredHypothesisRouteAudit inputs hypotheses).sourceAudit :=
  rfl

theorem structuredEndpointAuditSummary_sourceAudit_eq_auditOfStructuredHypotheses
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredEndpointAuditSummary inputs hypotheses).source_audit =
      package.auditOfStructuredHypotheses inputs hypotheses :=
  rfl

theorem structuredEndpointAuditSummary_payloadRouteSummary_eq_routeAudit
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredEndpointAuditSummary
      inputs hypotheses).payload_route_summary =
      (package.structuredHypothesisRouteAudit
        inputs hypotheses).payloadRouteSummary :=
  rfl

theorem structuredEndpointAuditSummary_publicAuditEq_eq_routeAudit
    (package : IUTStage1SourcePackage source target index)
    (inputs : IUTStage1Theorem311StructuredInputs package)
    (hypotheses : IUTStage1SourceSideConditionHypotheses package) :
    (package.structuredEndpointAuditSummary
      inputs hypotheses).endpoint_public_audit_eq =
      (package.structuredHypothesisRouteAudit
        inputs hypotheses).comparisonDataEndpointPayloadRouteSummary.choose_spec.2 :=
  Subsingleton.elim _ _

namespace StructuredEndpointAuditSummary

variable {package : IUTStage1SourcePackage source target index}
variable {inputs : IUTStage1Theorem311StructuredInputs package}
variable {hypotheses : IUTStage1SourceSideConditionHypotheses package}

theorem sourceAudit
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    Audit package
      (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  summary.source_audit

theorem payloadRouteSummary
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    Audit.PayloadRouteSummary summary.sourceAudit :=
  summary.payload_route_summary

theorem endpointPublicAuditEq
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    (package.auditedComparisonDataEndpointOfStructuredHypotheses
      inputs hypotheses).publicAudit =
      package.publicAuditOfStructuredHypotheses inputs hypotheses :=
  summary.endpoint_public_audit_eq

theorem payloadDataEqComparisonData
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    package.comparisonDataFromPayloadInputs
        (package.obligationsFromStructuredHypotheses inputs hypotheses) =
      summary.sourceAudit.comparisonData :=
  summary.payloadRouteSummary.payload_data_eq_comparison_data

theorem comparisonDataEqPackage
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    summary.sourceAudit.comparisonData =
      package.comparisonData
        (package.obligationsFromStructuredHypotheses inputs hypotheses) :=
  summary.payloadRouteSummary.comparison_data_eq_package

theorem comparisonDataRecovers
    (summary : StructuredEndpointAuditSummary package inputs hypotheses) :
    corollary312_from_stage1_comparison
        summary.sourceAudit.comparisonData.stage1Comparison =
      corollary312_of_signed_le
        summary.sourceAudit.comparisonData.qSigned_le_thetaSigned :=
  summary.payloadRouteSummary.comparison_data_recovers

end StructuredEndpointAuditSummary

end IUTStage1SourcePackage

end Stage1
end Iut
