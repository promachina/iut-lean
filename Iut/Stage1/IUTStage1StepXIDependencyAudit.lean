/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1StepXI

/-!
CI-facing dependency audit for the Step (xi) localized `C_Theta` boundary.

The declarations below intentionally do not reprove the long Step (xi) routes.
They pin the latest localized boundary audits to stable short names and record
their expected projection fields.  If the preferred public route loses one of
these constructor-built handoffs, this module stops compiling.
-/

namespace Iut
namespace Stage1
namespace IUTStage1StepXIDependencyAudit

set_option linter.style.longLine false


/-- Localized Step (xi) `C_Theta` boundary layers currently audited. -/
inductive LocalizedCThetaBoundaryLayer where
  | genericHaarModulus
  | intrinsicHaarModulus
  | unitBallHaarCharacter
  | residueUnitBallHaarCharacter
  | residueInverseBasePrime
  deriving DecidableEq, Repr

/-- Normalized structure-sheaf and additive-Haar variants of each boundary. -/
inductive LocalizedCThetaBoundaryNormalization where
  | structureSheafNormalized
  | additiveHaar
  deriving DecidableEq, Repr

/--
Textual inventory entry for the checked localized `C_Theta` boundary.

The `auditTypeName`, `constructorName`, and `routeEqualityField` fields mirror
the actual aliases below; the aliases are the compile-time dependency check.
-/
structure LocalizedCThetaBoundaryEntry where
  layer : LocalizedCThetaBoundaryLayer
  normalization : LocalizedCThetaBoundaryNormalization
  auditTypeName : String
  constructorName : String
  routeEqualityField : String
  deriving Repr

/-- Human-readable inventory of the ten constructor-built localized boundaries. -/
def localizedCThetaBoundaryInventory : List LocalizedCThetaBoundaryEntry :=
  [ { layer := .genericHaarModulus,
      normalization := .structureSheafNormalized,
      auditTypeName := "genericStructureSheafNormalizedAuditType",
      constructorName := "genericStructureSheafNormalizedAudit",
      routeEqualityField := "route_eq_arithmetic_residual_route" },
    { layer := .genericHaarModulus,
      normalization := .additiveHaar,
      auditTypeName := "genericAdditiveHaarAuditType",
      constructorName := "genericAdditiveHaarAudit",
      routeEqualityField := "route_eq_obligation_route" },
    { layer := .intrinsicHaarModulus,
      normalization := .structureSheafNormalized,
      auditTypeName := "intrinsicStructureSheafNormalizedAuditType",
      constructorName := "intrinsicStructureSheafNormalizedAudit",
      routeEqualityField := "route_eq_projected_localized_route" },
    { layer := .intrinsicHaarModulus,
      normalization := .additiveHaar,
      auditTypeName := "intrinsicAdditiveHaarAuditType",
      constructorName := "intrinsicAdditiveHaarAudit",
      routeEqualityField := "route_eq_projected_localized_route" },
    { layer := .unitBallHaarCharacter,
      normalization := .structureSheafNormalized,
      auditTypeName := "unitBallStructureSheafNormalizedAuditType",
      constructorName := "unitBallStructureSheafNormalizedAudit",
      routeEqualityField := "route_eq_projected_localized_route" },
    { layer := .unitBallHaarCharacter,
      normalization := .additiveHaar,
      auditTypeName := "unitBallAdditiveHaarAuditType",
      constructorName := "unitBallAdditiveHaarAudit",
      routeEqualityField := "route_eq_projected_localized_route" },
    { layer := .residueUnitBallHaarCharacter,
      normalization := .structureSheafNormalized,
      auditTypeName := "residueUnitBallStructureSheafNormalizedAuditType",
      constructorName := "residueUnitBallStructureSheafNormalizedAudit",
      routeEqualityField := "route_eq_projected_unit_ball_localized_route" },
    { layer := .residueUnitBallHaarCharacter,
      normalization := .additiveHaar,
      auditTypeName := "residueUnitBallAdditiveHaarAuditType",
      constructorName := "residueUnitBallAdditiveHaarAudit",
      routeEqualityField := "route_eq_projected_unit_ball_localized_route" },
    { layer := .residueInverseBasePrime,
      normalization := .structureSheafNormalized,
      auditTypeName := "inverseBasePrimeStructureSheafNormalizedAuditType",
      constructorName := "inverseBasePrimeStructureSheafNormalizedAudit",
      routeEqualityField := "route_eq_projected_localized_route" },
    { layer := .residueInverseBasePrime,
      normalization := .additiveHaar,
      auditTypeName := "inverseBasePrimeAdditiveHaarAuditType",
      constructorName := "inverseBasePrimeAdditiveHaarAudit",
      routeEqualityField := "route_eq_projected_localized_route" } ]

/-- Number of audited localized constructor-built `C_Theta` boundaries. -/
def localizedCThetaBoundaryInventory_count : Nat :=
  localizedCThetaBoundaryInventory.length

theorem localizedCThetaBoundaryInventory_count_eq :
    localizedCThetaBoundaryInventory_count = 10 :=
  rfl

/-- Public Step (xi) hull-construction boundaries currently audited. -/
inductive PublicStepXIHullConstructionBoundary where
  | coordinateScalarImageConstructedTrace
  | realLineCoordinateScalarImageConstructedTrace
  | valuationUnitBallNonzeroScalarSelected
  deriving DecidableEq, Repr

/--
Textual inventory entry for public Step (xi) hull construction boundaries.

The first two entries are full constructed-paper-trace routes whose principal
hull source is constructed from coordinate scalar-image data.  The valuation
entry is the selected-parameter exact-`Xi` layer below the full principal
source.
-/
structure PublicStepXIHullConstructionEntry where
  boundary : PublicStepXIHullConstructionBoundary
  auditTypeName : String
  constructorName : String
  keyField : String
  deriving Repr

/-- Human-readable inventory of constructor-built public Step (xi) hull boundaries. -/
def publicStepXIHullConstructionInventory :
    List PublicStepXIHullConstructionEntry :=
  [ { boundary := .coordinateScalarImageConstructedTrace,
      auditTypeName :=
        "PreferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit",
      constructorName :=
        "preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit",
      keyField := "coordinate_hull_route" },
    { boundary := .realLineCoordinateScalarImageConstructedTrace,
      auditTypeName :=
        "PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit",
      constructorName :=
        "preferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit",
      keyField := "real_line_coordinate_hull_route" },
    { boundary := .valuationUnitBallNonzeroScalarSelected,
      auditTypeName :=
        "ValuationUnitBallNonzeroScalarStepXIPublicAudit",
      constructorName := "valuationUnitBallNonzeroScalarStepXIPublicAudit",
      keyField := "transported_public_exact_xi_source" } ]

/-- Number of audited public Step (xi) hull-construction boundaries. -/
def publicStepXIHullConstructionInventory_count : Nat :=
  publicStepXIHullConstructionInventory.length

theorem publicStepXIHullConstructionInventory_count_eq :
    publicStepXIHullConstructionInventory_count = 3 :=
  rfl

def genericStructureSheafNormalizedAuditType : String :=
  "HaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def genericStructureSheafNormalizedAudit : String :=
  "haarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def genericStructureSheafNormalizedRouteEquality : String :=
  "route_eq_arithmetic_residual_route"

def genericAdditiveHaarAuditType : String :=
  "HaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def genericAdditiveHaarAudit : String :=
  "haarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def genericAdditiveHaarRouteEquality : String :=
  "route_eq_obligation_route"

def intrinsicStructureSheafNormalizedAuditType : String :=
  "IntrinsicHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def intrinsicStructureSheafNormalizedAudit : String :=
  "intrinsicHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def intrinsicStructureSheafNormalizedRouteEquality : String :=
  "route_eq_projected_localized_route"

def intrinsicAdditiveHaarAuditType : String :=
  "IntrinsicHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def intrinsicAdditiveHaarAudit : String :=
  "intrinsicHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def intrinsicAdditiveHaarRouteEquality : String :=
  "route_eq_projected_localized_route"

def unitBallStructureSheafNormalizedAuditType : String :=
  "UnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def unitBallStructureSheafNormalizedAudit : String :=
  "unitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def unitBallStructureSheafNormalizedRouteEquality : String :=
  "route_eq_projected_localized_route"

def unitBallAdditiveHaarAuditType : String :=
  "UnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def unitBallAdditiveHaarAudit : String :=
  "unitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def unitBallAdditiveHaarRouteEquality : String :=
  "route_eq_projected_localized_route"

def residueUnitBallStructureSheafNormalizedAuditType : String :=
  "ResidueModuleUnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaProjectedBoundaryAudit"

def residueUnitBallStructureSheafNormalizedAudit : String :=
  "residueModuleUnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaProjectedBoundaryAudit"

def residueUnitBallStructureSheafNormalizedRouteEquality : String :=
  "route_eq_projected_unit_ball_localized_route"

def residueUnitBallAdditiveHaarAuditType : String :=
  "ResidueModuleUnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaProjectedBoundaryAudit"

def residueUnitBallAdditiveHaarAudit : String :=
  "residueModuleUnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaProjectedBoundaryAudit"

def residueUnitBallAdditiveHaarRouteEquality : String :=
  "route_eq_projected_unit_ball_localized_route"

def inverseBasePrimeStructureSheafNormalizedAuditType : String :=
  "ResidueModuleInverseBasePrimeHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def inverseBasePrimeStructureSheafNormalizedAudit : String :=
  "residueModuleInverseBasePrimeHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def inverseBasePrimeStructureSheafNormalizedRouteEquality : String :=
  "route_eq_projected_localized_route"

def inverseBasePrimeAdditiveHaarAuditType : String :=
  "ResidueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def inverseBasePrimeAdditiveHaarAudit : String :=
  "residueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit"

def inverseBasePrimeAdditiveHaarRouteEquality : String :=
  "route_eq_projected_localized_route"

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.haarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_arithmetic_residual_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.haarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_obligation_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IntrinsicHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.intrinsicHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IntrinsicHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IntrinsicHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.intrinsicHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IntrinsicHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.UnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.unitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.UnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.UnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.unitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.UnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleUnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaProjectedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.residueModuleUnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaProjectedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleUnitBallHaarCharacterStructureSheafNormalizedConstructorBuiltLocalizedCThetaProjectedBoundaryAudit.route_eq_projected_unit_ball_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleUnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaProjectedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.residueModuleUnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaProjectedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleUnitBallHaarCharacterAdditiveHaarConstructorBuiltLocalizedCThetaProjectedBoundaryAudit.route_eq_projected_unit_ball_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleInverseBasePrimeHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.residueModuleInverseBasePrimeHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleInverseBasePrimeHaarModulusStructureSheafNormalizedConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.residueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ResidueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructorBuiltLocalizedCThetaFullBoundaryAudit.route_eq_projected_localized_route

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.transportedCoordinateScalarImageLocalizedThetaEqFamilyHullPaperTrace
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceStepXIPaperSourceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.coordinate_hull_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.constructed_paper_trace

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.transportedRealLineCoordinateScalarImageLocalizedThetaEqFamilyHullPaperTrace
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceStepXIPaperSourceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.real_line_coordinate_hull_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.constructed_paper_trace

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ValuationUnitBallNonzeroScalarStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.valuationUnitBallNonzeroScalarStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ValuationUnitBallNonzeroScalarStepXIPublicAudit.selected_hull_eq_valuation_cell_union
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ValuationUnitBallNonzeroScalarStepXIPublicAudit.adjusted_family_hull_eq_normalized_determinant
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ValuationUnitBallNonzeroScalarStepXIPublicAudit.transported_public_exact_xi_source

end IUTStage1StepXIDependencyAudit
end Stage1
end Iut
