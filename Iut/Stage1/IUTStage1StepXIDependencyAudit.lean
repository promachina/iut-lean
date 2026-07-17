/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1StepXI.AdditiveHaarBridge

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

/--
Classification for the canonical Stage 1 public boundary.

`sourceObligation` marks mathematics that still has to be constructed from the
IUT papers before the 3.11-to-3.12 corridor is closed.  `interfaceOnly` marks
typed bookkeeping that selects an operation or index surface but is not itself
a mathematical comparison theorem.
-/
inductive CanonicalStage1BoundaryStatus where
  | constructed
  | derived
  | interfaceOnly
  | sourceObligation
  deriving DecidableEq, Repr

/--
One public input or lower field used by the canonical audited Stage 1 route.

The strings are deliberately human-readable: the compile-time checks below pin
the actual declarations, while this manifest states the trust-boundary role,
source-paper location, and consuming endpoint in one place.
-/
structure CanonicalStage1RemainingAssumption where
  name : String
  status : CanonicalStage1BoundaryStatus
  paperSource : String
  consumerDeclaration : String
  note : String
  deriving Repr

/-- Short name for the current canonical public 3.11-to-3.12 Stage 1 route. -/
def canonicalStage1RouteName : String :=
  "same-index q-normalized local-arithmetic-degree route with derived scale-synchronized source"

/--
Current canonical Stage 1 remaining-assumption manifest.

New public endpoints should reduce this list, refine one of its source
obligations to a constructed/derived item, or be kept private.  Adding a public
wrapper that leaves this manifest unchanged is not progress toward the active
paper-level corridor goal.
-/
def canonicalStage1RemainingAssumptions :
    List CanonicalStage1RemainingAssumption :=
  [ { name := "packet",
      status := .sourceObligation,
      paperSource := "IUT III, Theorem 3.11; IUT I-II initial theta/Hodge-theater setup",
      consumerDeclaration :=
        "preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit",
      note :=
        "Concrete primitive Theorem 3.11 packet is still supplied rather than constructed from initial theta data." },
    { name := "sourceWithSymmetry",
      status := .sourceObligation,
      paperSource := "IUT III, Theorem 3.11 multiradial representation and Ind2 transport",
      consumerDeclaration :=
        "preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit",
      note :=
        "Symmetry-label/fiber transport data remains a source-level theorem to derive from the log-theta procession." },
    { name := "compactOpenRealizedExactSource",
      status := .sourceObligation,
      paperSource := "IUT III, Remark 3.11.3 and Step (x) log-Kummer correspondence",
      consumerDeclaration :=
        "compactOpenLogKummerMapSourceOfRealizedExactPrincipalProduct",
      note :=
        "The compact-open realized exactness/log-Kummer image layer is still a public source input." },
    { name := "hodgeEvaluation",
      status := .sourceObligation,
      paperSource := "IUT II Hodge-Arakelov theta evaluation; IUT III, Theorem 3.11",
      consumerDeclaration :=
        "PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource",
      note :=
        "Hodge evaluation is typed, but the paper-level construction from initial theta data is not yet internal." },
    { name := "localArithmeticHandoff",
      status := .sourceObligation,
      paperSource := "IUT III, Step (xi); Remark 3.9.5; Ob7",
      consumerDeclaration :=
        "PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource",
      note :=
        "Finite-extension restriction, norm-square Ob7, and local arithmetic handoff remain exposed at this boundary." },
    { name := "operation/hullOperation/determinantOperation",
      status := .interfaceOnly,
      paperSource := "IUT III, Remark 3.9.5 operation choices",
      consumerDeclaration :=
        "primitiveThetaRegionCurrentProductHullPrincipalHDDSource",
      note :=
        "Operation identifiers select the hull/determinant interface; they are not comparison assumptions by themselves." },
    { name := "pointwiseDeterminantFormulaSource",
      status := .sourceObligation,
      paperSource := "IUT III, Remark 3.9.5 determinant and measure/summand calibration",
      consumerDeclaration :=
        "PrincipalPointwiseValuationBallMeasureDeterminantFormulaSource",
      note :=
        "Pointwise determinant calibration is still supplied as a source package." },
    { name := "sideConditions",
      status := .sourceObligation,
      paperSource := "IUT III, Corollary 3.12 sign and normalization hypotheses",
      consumerDeclaration :=
        "IUTStage1SourceSideConditions",
      note :=
        "q-positivity, normalization, and side-condition facts are reconstructed into the route but not yet derived from paper data." },
    { name := "weighted determinant component synchronization",
      status := .sourceObligation,
      paperSource := "IUT III, Remark 3.9.5 Ob3/Ob4 determinant bridge",
      consumerDeclaration :=
        "ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource",
      note :=
        "The canonical route is now the q-normalized local-arithmetic-degree constituent endpoint.  The summand, anchor, and positive tensor-power identifications remain source obligations; Lean reconstructs the scale-synchronized determinant source from them." },
    { name := "thetaSigned_eq_projectedPrincipalProductLocalizedAdjustedSum_mul_absLogQ",
      status := .sourceObligation,
      paperSource := "IUT III, Corollary 3.12 theta/log-volume comparison",
      consumerDeclaration :=
        "ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toScaleSynchronizedLocalAnalyticSource",
      note :=
        "The public source now carries the q-normalized theta/log-volume identity.  Lean derives canonical C_Theta-scale synchronization from this identity and q-pilot positivity, so the raw canonical-scale equality is no longer a canonical public field." },
    { name := "theorem110ValuationBallFormulaGapSource",
      status := .sourceObligation,
      paperSource := "IUT IV, Theorem 1.10 valuation-ball arithmetic divisor estimates",
      consumerDeclaration :=
        "IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource",
      note :=
        "The local upper-bound ledger is typed but still supplied as an IUT IV source object." },
    { name := "localArithmeticDegreeResidualSource",
      status := .sourceObligation,
      paperSource := "IUT IV local arithmetic-degree identity and Haar residual lower bound",
      consumerDeclaration :=
        "IUTStage1IUTIVLocalArithmeticDegreeResidualSource",
      note :=
        "The canonical route no longer requires the stronger case-bounded residual source.  Case-bounded, local-analytic case, processional arithmetic-gap, and p-adic Haar routes are constructors into this residual package.  The p-adic unit-ball Step XI synchronization route now projects directly to this package through preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSourceToLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit.  The synchronization itself has a formula-matching constructor from StepXI = a(D+C) and prime-error = p-adic index + main; the AdditiveHaarBridge now projects the additive-Haar, p-adic prime-error, arithmetic-degree calibrated, formula-gap matched, arithmetic-divisor-backed local-degree, constructed Theorem 3.11 local-term, and valuation-ball arithmetic-degree formula-matching tower into that canonical constructor.  The Step XI arithmetic-degree equality is therefore audited as a consequence of determinant-weight and adjusted raw-log-volume calibration.  The additive-Haar split can be constructed from a local analytic arithmetic-divisor evaluation source plus the p-adic equality E_v = delta_v + M_v; the valuation-ball p-adic defect/main source now builds that equality into the prime-error term, and it is itself constructible from the arithmetic-degree-controlled local arithmetic source by combining E_v = localIUTIVDefect_v + M_v with localIUTIVDefect_v = delta_v.  The resulting source projects to the valuation-ball formula-gap matched prime-error source and reads finite sums, nonnegativity, formula-gap data, and arithmetic-divisor calibration from the valuation-ball local-estimate package.  The remaining IUT IV obligation is deriving the arithmetic-degree-controlled local arithmetic source from the full local-estimate construction." } ]

/-- Number of manifest entries in the canonical Stage 1 remaining boundary. -/
def canonicalStage1RemainingAssumptions_count : Nat :=
  canonicalStage1RemainingAssumptions.length

theorem canonicalStage1RemainingAssumptions_count_eq :
    canonicalStage1RemainingAssumptions_count = 12 :=
  rfl

/-- Source obligations still present in the canonical manifest. -/
def canonicalStage1SourceObligationNames : List String :=
  canonicalStage1RemainingAssumptions.filterMap fun entry =>
    if entry.status = .sourceObligation then some entry.name else none

/-- The canonical route currently exposes eleven source-obligation entries. -/
theorem canonicalStage1SourceObligationNames_count_eq :
    canonicalStage1SourceObligationNames.length = 11 :=
  rfl

/-- The canonical route has exactly one interface-only entry. -/
theorem canonicalStage1RemainingAssumptions_interfaceOnly_count_eq :
    (canonicalStage1RemainingAssumptions.filter
      (fun entry => entry.status = .interfaceOnly)).length = 1 :=
  rfl

/--
One-place diagnostic model for the p-adic finite source boundary.

The canonical route now reads the local weighted Step~(xi) scale from the
finite-extension restriction-calibrated handoff.  This toy model records the
failure mode of the weakened boundary that allowed a detached p-adic finite
source to supply its own scale: the handoff-derived theta identity can hold
while the detached identity is false.
-/
structure DetachedPadicFiniteToyCountermodel where
  qSigned : Real
  thetaSigned : Real
  derivedScale : Real
  detachedScale : Real
  qSigned_eq_neg_one : qSigned = -1
  thetaSigned_eq_derivedScale_mul_absLogQ :
    thetaSigned = derivedScale * (-qSigned)
  derivedScale_eq_zero : derivedScale = 0
  detachedScale_eq_one : detachedScale = 1

/--
The detached p-adic finite source law is not a harmless weakening of the
canonical route: even in a one-place model it can contradict the theta identity
forced by the local arithmetic handoff-derived source.
-/
theorem DetachedPadicFiniteToyCountermodel.not_detached_theta_identity
    (toy : DetachedPadicFiniteToyCountermodel) :
    ¬ toy.thetaSigned = toy.detachedScale * (-toy.qSigned) := by
  intro hdetached
  have htheta_zero : toy.thetaSigned = 0 := by
    rw [toy.thetaSigned_eq_derivedScale_mul_absLogQ, toy.derivedScale_eq_zero,
      zero_mul]
  have htheta_one : toy.thetaSigned = 1 := by
    rw [hdetached, toy.detachedScale_eq_one, toy.qSigned_eq_neg_one]
    norm_num
  rw [htheta_zero] at htheta_one
  norm_num at htheta_one

/-- Concrete one-place countermodel for the detached p-adic finite source law. -/
def detachedPadicFiniteToyCountermodel :
    DetachedPadicFiniteToyCountermodel :=
  { qSigned := -1,
    thetaSigned := 0,
    derivedScale := 0,
    detachedScale := 1,
    qSigned_eq_neg_one := by norm_num,
    thetaSigned_eq_derivedScale_mul_absLogQ := by norm_num,
    derivedScale_eq_zero := by norm_num,
    detachedScale_eq_one := by norm_num }

theorem detachedPadicFiniteToyCountermodel_not_detached_theta_identity :
    ¬ detachedPadicFiniteToyCountermodel.thetaSigned =
      detachedPadicFiniteToyCountermodel.detachedScale *
        (-detachedPadicFiniteToyCountermodel.qSigned) :=
  detachedPadicFiniteToyCountermodel.not_detached_theta_identity

/--
One-place diagnostic for the signed \(C_\Theta\) lower-bound schema.

The new p-adic unit-ball lower-bound projection ultimately uses
`IUTStage1Corollary312SignedCThetaBound`, whose ordered-real proof needs both
q-positivity and the signed comparison `qSigned <= thetaSigned`.  This toy model
keeps q-positivity and the IUT IV-style upper bound
`thetaSigned <= C_Theta * (-qSigned)`, but deletes `qSigned <= thetaSigned`.
Then \(C_\Theta < -1\) is possible.
-/
structure SignedCThetaWithoutQThetaToyCountermodel where
  qSigned : Real
  thetaSigned : Real
  cTheta : Real
  q_positive : 0 < -qSigned
  thetaSigned_le_cTheta_absLogQ : thetaSigned <= cTheta * (-qSigned)
  not_qSigned_le_thetaSigned : ¬ qSigned <= thetaSigned
  cTheta_lt_neg_one : cTheta < (-1 : Real)

theorem SignedCThetaWithoutQThetaToyCountermodel.not_cTheta_ge_neg_one
    (toy : SignedCThetaWithoutQThetaToyCountermodel) :
    ¬ (-1 : Real) <= toy.cTheta :=
  not_le_of_gt toy.cTheta_lt_neg_one

/--
Concrete countermodel: `q=-1`, `theta=-2`, and `C_Theta=-2`.

The upper bound is an equality and the q-pilot sign is correct, but the missing
`qSigned <= thetaSigned` comparison is false, and the lower bound
\(-1\le C_\Theta\) fails.
-/
def signedCThetaWithoutQThetaToyCountermodel :
    SignedCThetaWithoutQThetaToyCountermodel :=
  { qSigned := -1,
    thetaSigned := -2,
    cTheta := -2,
    q_positive := by norm_num,
    thetaSigned_le_cTheta_absLogQ := by norm_num,
    not_qSigned_le_thetaSigned := by norm_num,
    cTheta_lt_neg_one := by norm_num }

theorem signedCThetaWithoutQThetaToyCountermodel_not_cTheta_ge_neg_one :
    ¬ (-1 : Real) <= signedCThetaWithoutQThetaToyCountermodel.cTheta :=
  signedCThetaWithoutQThetaToyCountermodel.not_cTheta_ge_neg_one

/--
One-place diagnostic for the local-analytic case-source boundary.

The scale-synchronized local-analytic case-source route uses the ordinary local
case upper bound together with the distinguished \(+1\) gap.  This toy model
keeps the ordinary distinguished local comparison but deletes the \(+1\) gap.
Then the residual lower bound needed by the formula-gap case residual source is
false.
-/
structure LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel where
  distinguishedStepXI : Real
  distinguishedProcessionBound : Real
  localStepXI_le_distinguishedProcessionBound :
    distinguishedStepXI <= distinguishedProcessionBound
  not_distinguished_stepXI_plus_one_le_distinguishedProcessionBound :
    ¬ distinguishedStepXI + 1 <= distinguishedProcessionBound
  distinguished_residual_lt_one :
    distinguishedProcessionBound - distinguishedStepXI < 1

theorem LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel.not_residual_ge_one
    (toy : LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel) :
    ¬ (1 : Real) <= toy.distinguishedProcessionBound - toy.distinguishedStepXI :=
  not_le_of_gt toy.distinguished_residual_lt_one

/--
Concrete countermodel: the local Step~(xi) value and distinguished procession
bound are both \(0\).  The weak local upper bound holds, but the distinguished
\(+1\) gap and the residual lower bound both fail.
-/
def localAnalyticCaseWithoutDistinguishedGapToyCountermodel :
    LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel :=
  { distinguishedStepXI := 0,
    distinguishedProcessionBound := 0,
    localStepXI_le_distinguishedProcessionBound := by norm_num,
    not_distinguished_stepXI_plus_one_le_distinguishedProcessionBound := by
      norm_num,
    distinguished_residual_lt_one := by norm_num }

theorem localAnalyticCaseWithoutDistinguishedGapToyCountermodel_not_residual_ge_one :
    ¬ (1 : Real) <=
      localAnalyticCaseWithoutDistinguishedGapToyCountermodel.distinguishedProcessionBound -
        localAnalyticCaseWithoutDistinguishedGapToyCountermodel.distinguishedStepXI :=
  localAnalyticCaseWithoutDistinguishedGapToyCountermodel.not_residual_ge_one

/--
One-place diagnostic for the canonical local-arithmetic-degree boundary.

After the canonical route is lowered from the case-bounded IUT~IV source to the
local arithmetic-degree residual source, the essential remaining numerical law
is the residual lower bound.  This toy model keeps the local arithmetic-degree
identity but reverses the lower bound; the \(C_\Theta\)-style one-unit residual
needed by the endpoint is then unavailable.
-/
structure LocalArithmeticDegreeWithoutResidualLowerToyCountermodel where
  localArithmeticUpper : Real
  localStepXI : Real
  localMainLog : Real
  localHaarDefect : Real
  local_identity :
    localArithmeticUpper = localStepXI + localHaarDefect + localMainLog
  residual_lt_one : localHaarDefect < 1

theorem LocalArithmeticDegreeWithoutResidualLowerToyCountermodel.not_residual_ge_one
    (toy : LocalArithmeticDegreeWithoutResidualLowerToyCountermodel) :
    ¬ (1 : Real) <= toy.localHaarDefect :=
  not_le_of_gt toy.residual_lt_one

/--
Concrete local-degree countermodel with zero Haar residual.  The arithmetic
identity holds, but the residual lower bound required by the canonical endpoint
fails.
-/
def localArithmeticDegreeWithoutResidualLowerToyCountermodel :
    LocalArithmeticDegreeWithoutResidualLowerToyCountermodel :=
  { localArithmeticUpper := 0,
    localStepXI := 0,
    localMainLog := 0,
    localHaarDefect := 0,
    local_identity := by norm_num,
    residual_lt_one := by norm_num }

theorem localArithmeticDegreeWithoutResidualLowerToyCountermodel_not_residual_ge_one :
    ¬ (1 : Real) <=
      localArithmeticDegreeWithoutResidualLowerToyCountermodel.localHaarDefect :=
  localArithmeticDegreeWithoutResidualLowerToyCountermodel.not_residual_ge_one

/--
One-place diagnostic for the p-adic unit-ball Haar-index lowering.

The p-adic route removes the residual lower bound only because the local
residual is identified with the unit-ball dilation index
`p_v^[K_v : Q_p]`, whose normalized-place contribution is at least `1`.
If that lower p-adic index law is weakened to an arbitrary synchronized
"index", the Step~(xi) identity can still hold while the one-unit residual
needed by the canonical endpoint fails.
-/
structure PadicUnitBallWithoutNormalizedIndexToyCountermodel where
  localArithmeticUpper : Real
  localStepXI : Real
  localMainLog : Real
  localPadicIndex : Real
  localStepXI_plus_padicIndex_eq_arithmeticUpper_minus_main :
    localStepXI + localPadicIndex = localArithmeticUpper - localMainLog
  local_defined_residual_eq_padicIndex :
    localArithmeticUpper - localStepXI - localMainLog = localPadicIndex
  padicIndex_lt_one : localPadicIndex < 1

theorem PadicUnitBallWithoutNormalizedIndexToyCountermodel.not_residual_ge_one
    (toy : PadicUnitBallWithoutNormalizedIndexToyCountermodel) :
    ¬ (1 : Real) <= toy.localArithmeticUpper - toy.localStepXI - toy.localMainLog := by
  rw [toy.local_defined_residual_eq_padicIndex]
  exact not_le_of_gt toy.padicIndex_lt_one

/--
Concrete p-adic-index countermodel with zero synchronized index.  The local
Step~(xi) synchronization and residual/index identity hold, but the missing
normalized-place index lower law makes the endpoint residual lower bound false.
-/
def padicUnitBallWithoutNormalizedIndexToyCountermodel :
    PadicUnitBallWithoutNormalizedIndexToyCountermodel :=
  { localArithmeticUpper := 0,
    localStepXI := 0,
    localMainLog := 0,
    localPadicIndex := 0,
    localStepXI_plus_padicIndex_eq_arithmeticUpper_minus_main := by norm_num,
    local_defined_residual_eq_padicIndex := by norm_num,
    padicIndex_lt_one := by norm_num }

theorem padicUnitBallWithoutNormalizedIndexToyCountermodel_not_residual_ge_one :
    ¬ (1 : Real) <=
      padicUnitBallWithoutNormalizedIndexToyCountermodel.localArithmeticUpper -
        padicUnitBallWithoutNormalizedIndexToyCountermodel.localStepXI -
        padicUnitBallWithoutNormalizedIndexToyCountermodel.localMainLog :=
  padicUnitBallWithoutNormalizedIndexToyCountermodel.not_residual_ge_one

/--
One-place diagnostic for the valuation-ball p-adic defect/main lowering.

The arithmetic-degree-controlled source gives the prime-error identity in the
form `E_v = localIUTIVDefect_v + M_v`.  The constructor lowered in
`AdditiveHaar` converts this to the p-adic split
`E_v = delta_v + M_v` only by using the IUT~IV arithmetic-defect
identification `localIUTIVDefect_v = delta_v`.  If that identification is
weakened away, the defect/main identity can hold while the p-adic split fails.
-/
structure PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel where
  localPrimeError : Real
  localIUTIVDefect : Real
  localPadicHaarDefect : Real
  localMainLog : Real
  prime_eq_iutIVDefect_main :
    localPrimeError = localIUTIVDefect + localMainLog
  iutIVDefect_ne_padicHaarDefect :
    localIUTIVDefect ≠ localPadicHaarDefect
  not_prime_eq_padicHaarDefect_main :
    ¬ localPrimeError = localPadicHaarDefect + localMainLog

theorem PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.not_padic_defect_main_split
    (toy : PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel) :
    ¬ toy.localPrimeError = toy.localPadicHaarDefect + toy.localMainLog :=
  toy.not_prime_eq_padicHaarDefect_main

/--
Concrete countermodel: the prime error, IUT~IV arithmetic defect, and main term
are all zero, while the p-adic Haar defect is one.  The
`E_v = localIUTIVDefect_v + M_v` identity holds, but the p-adic split
`E_v = delta_v + M_v` is false.
-/
def padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel :
    PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel :=
  { localPrimeError := 0,
    localIUTIVDefect := 0,
    localPadicHaarDefect := 1,
    localMainLog := 0,
    prime_eq_iutIVDefect_main := by norm_num,
    iutIVDefect_ne_padicHaarDefect := by norm_num,
    not_prime_eq_padicHaarDefect_main := by norm_num }

theorem padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel_not_padic_defect_main_split :
    ¬ padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.localPrimeError =
      padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.localPadicHaarDefect +
        padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.localMainLog :=
  padicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel
    |>.not_padic_defect_main_split

#guard_msgs (drop info) in
#check LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel.not_residual_ge_one
#guard_msgs (drop info) in
#print axioms LocalAnalyticCaseWithoutDistinguishedGapToyCountermodel.not_residual_ge_one

#guard_msgs (drop info) in
#check LocalArithmeticDegreeWithoutResidualLowerToyCountermodel.not_residual_ge_one
#guard_msgs (drop info) in
#print axioms LocalArithmeticDegreeWithoutResidualLowerToyCountermodel.not_residual_ge_one

#guard_msgs (drop info) in
#check PadicUnitBallWithoutNormalizedIndexToyCountermodel.not_residual_ge_one
#guard_msgs (drop info) in
#print axioms PadicUnitBallWithoutNormalizedIndexToyCountermodel.not_residual_ge_one

#guard_msgs (drop info) in
#check PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.not_padic_defect_main_split
#guard_msgs (drop info) in
#print axioms PadicDefectMainWithoutArithmeticDefectIdentificationToyCountermodel.not_padic_defect_main_split

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.toLocalArithmeticDegreeResidualSource

#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.ofStructuredInputsWithSHEAndSideConditions
#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.ofStructuredInputsWithSHEAndSideConditions_sheAlignment
#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.ofStructuredInputsWithSHEAndSideConditions_commonContainerCompatibility
#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.ofStructuredInputsWithSHEAndSideConditions_toSourceObligations_eq_structured
#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.StructuredInputsWithSHEAndSideConditionsAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311StructuredInputsWithSHE.reindex
#guard_msgs (drop info) in
#check IUTStage1Theorem311StructuredInputsWithSHE.reindex_bundle_eq
#guard_msgs (drop info) in
#check IUTStage1Theorem311StructuredInputsWithSHE.reindex_algorithm_output_certified
#guard_msgs (drop info) in
#check IUTStage1SourceObligationGap.structuredInputsWithSHEAndSideConditionsAudit
#guard_msgs (drop info) in
#check RealLineCopy.AlgorithmicOutput.SHEArrowData.ofStructuredSHETransportContext
#guard_msgs (drop info) in
#check RealLineCopy.AlgorithmicOutput.CommonContainerData.ofStructuredSHETransportContext
#guard_msgs (drop info) in
#check IUTStage1PreLedgerData.ConstructedQualitativeCommonContainerData.sheArrowMatchesCertificate
#guard_msgs (drop info) in
#check IUTStage1PreLedgerData.ConstructedLedgerPromotionObligations.toSourceObligationLedger
#guard_msgs (drop info) in
#check IUTStage1PreLedgerData.ConstructedLedgerPromotionObligations.toSourceObligationProvider_publicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ConstructedQualitativeInputsWithSHE.constructedCommonContainerData
#guard_msgs (drop info) in
#check IUTStage1Theorem311ConstructedQualitativeInputsWithSHE.constructedLedgerPromotionObligations
#guard_msgs (drop info) in
#check IUTStage1Theorem311ConstructedQualitativeInputsWithSHE.constructedLedgerPromotion_publicAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.constructedQualitativeSHEPublicAuditStatement
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.constructedQualitativeSHEPublicAuditStatement_proof
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.ConstructedQualitativeStructuredSHERouteSummary.constructedPromotionPublicAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.constructedLedgerPromotionObligations
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.constructedLedgerPromotionObligations_publicAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.constructedLedgerPromotionObligationsOfTransportGuard
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.constructedLedgerPromotionObligationsOfTransportGuard_publicAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.ConstructedTransportGuardedPromotionAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.constructedTransportGuardedPromotionAudit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311ConstructedQualitativeSource
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311ConstructedQualitativeSource.toConstructedQualitativeInputs
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311ConstructedQualitativeSource.Audit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311ConstructedQualitativeSource.audit
#guard_msgs (drop info) in
#check IUTStage1TransportIPLConstructionSourceCopy
#guard_msgs (drop info) in
#check IUTStage1TransportSHEContextSourceCopy
#guard_msgs (drop info) in
#check IUTStage1TransportAPTConstructionSourceCopy
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSource
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSource.toPrimitiveQualitativeSource
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSource.audit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor.qualitativeSource
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor.toPrimitiveConstructor
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor.primitiveConstructor_qualitativeSource_eq
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor.Audit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311BridgeCertificateSourceConstructor.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311TargetRegionClassFormulaSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311TargetRegionClassFormulaSource.toPackageTargetRegionLatticeFormulaSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311TargetRegionClassFormulaSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StepXLogKummerComponentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StepXLogKummerComponentSource.toStepXVerticalLogKummerFiniteDivisorPackage
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StepXLogKummerComponentSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.ofConstructedQualitativeCertificateData
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.theorem311BridgePackage
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.bridge_certificate_eq
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.structuredSHE
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.hodgeTheaterSHEAlignment
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.ConstructedQualitativeBridgeNoCollapseAudit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlignedBridgeComponentSource.constructedQualitativeBridgeNoCollapseAudit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedQualitativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedQualitativeBridgeAlignmentSource.bridgeComponentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedQualitativeBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedQualitativeBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedCommonContainerBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedCommonContainerBridgeAlignmentSource.toConstructedQualitativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedCommonContainerBridgeAlignmentSource.ofConstructedQualitativeInputsWithSHE
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedCommonContainerBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311ConstructedCommonContainerBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CanonicalPrimeStripBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CanonicalPrimeStripBridgeAlignmentSource.toConstructedCommonContainerBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CanonicalPrimeStripBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CanonicalPrimeStripBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CodomainCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CodomainCanonicalBridgeAlignmentSource.toCanonicalPrimeStripBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CodomainCanonicalBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311CodomainCanonicalBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotCanonicalBridgeAlignmentSource.toCodomainCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotCanonicalBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotCanonicalBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotClassBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotClassBridgeAlignmentSource.toQPilotCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotClassBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotClassBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ThetaPilotComponentRepresentativeKernel
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotComponentRepresentativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotComponentRepresentativeBridgeAlignmentSource.toQPilotClassBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotComponentRepresentativeBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311QPilotComponentRepresentativeBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineQPilotComponentBridgeAlignmentSource.toQPilotComponentRepresentativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineQPilotComponentBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineQPilotComponentBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource.toSourceSpineQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource.toSourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource.toSourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1PreLedgerData.reindex
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.reindex
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.generatedPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.generatedPackage_chosenOutput_eq_selected
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.generatedPackage_output_comparison_eq_concrete_projection
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.generatedPackage_selected_comparison_eq_concrete_chosen
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.generatedPackage_signed_data_eq_concrete
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ComponentKernelGeneratedFullLabelPackageReindexSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.selectedGeneratedQChoice_projects_to_chosenOutput
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.toComponentKernelGeneratedFullLabelPackageReindexSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.generatedPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.generatedPackage_chosenOutput_eq_selected
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.generatedPackage_selected_comparison_eq_concrete_chosen
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.generatedPackage_signed_data_eq_concrete
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedLabelPackageReindexAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.selectedLabelSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.selectedLabelSource_sourceSpine_selectedQChoice_eq_packet
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.sourceSpine_selectedQChoice_eq_chosenOutput
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.toSourceSpineSelectedLabelPackageReindexAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.generatedPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketSelectedLabelPackageReindexAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.packet
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.packet_selectedQChoice_eq_chosenOutput
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.componentKernelSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.toPrimitivePacketSelectedLabelPackageReindexAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.generatedPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.generatedStructuredBundle
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.generatedStructuredBundle_context_eq_reindex
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.generatedPackage_targetRegions_eq_generatedFullLabelChoiceImages
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.generatedThetaPossibleImages
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.withGeneratedThetaPossibleImages
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.withGeneratedThetaPossibleImages_images_eq_generated
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputPrimitivePacketReindexAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.generatedPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.generatedSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.thetaClassImages
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.selectedGeneratedQChoice
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.generatedCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputGeneratedFullLabelQuotientCorridorSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.recordGenerated
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.record_images_eq_generated
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.toChosenOutputGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.generatedCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedGeneratedFullLabelQuotientCorridorSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.recordBase
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.recordGenerated
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.recordGenerated_bundle_eq_generatedBundle
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.toConstructedGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.generatedCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputStructuredGeneratedFullLabelQuotientCorridorSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.generatedBundle
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.generatedBundle_context_eq_reindex
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.toStructuredGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.generatedCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputReindexedStructuredGeneratedFullLabelQuotientCorridorSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.concreteBundle
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.generatedBundle
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.generatedBundle_context_eq_reindex
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.toReindexedStructuredGeneratedFullLabelQuotientCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.generatedCorridorSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311ChosenOutputConstructedQualitativeGeneratedFullLabelQuotientCorridorSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311SourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.toSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketComponentKernelOneSidedSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketComponentKernelOneSidedSHECodomainSelectedLabelQPilotBridgeAlignmentSource.toPrimitivePacketOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketComponentKernelOneSidedSHECodomainSelectedLabelQPilotBridgeAlignmentSource.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitivePacketComponentKernelOneSidedSHECodomainSelectedLabelQPilotBridgeAlignmentSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredFlagOutput
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredOutputFlagCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredOutputFlagCalibrationSource.outputHasIPL_of_structured
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredOutputFlagCalibrationSource.outputHasSHE_of_structured
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredOutputFlagCalibrationSource.outputHasAPT_of_structured
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311StructuredOutputFlagCalibrationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.structuredIPL
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.structuredSHE
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.structuredAPT
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.certified
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311AlgorithmicOutputComponentSource.ofOutputFlagCalibration
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource.theorem311Subclaims
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource.ofOutputFlagCalibration
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource.OutputFlagCalibrationAudit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311SubclaimComponentSource.outputFlagCalibrationAudit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofConstructedQualitativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofConstructedCommonContainerBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofCanonicalPrimeStripBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofCodomainCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofQPilotCanonicalBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofQPilotClassBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofQPilotComponentRepresentativeBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineQPilotComponentBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineGeneratedFullLabelQPilotComponentBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineGeneratedQChoiceQPilotComponentBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineSelectedLabelQPilotComponentBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineComponentRepresentativeSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource_subclaimAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineOneSidedComponentSelectedLabelQPilotBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineSelectedOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource_selectedQChoice_eq_source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.ofSourceSpineDataOneSidedComponentSHECodomainSelectedLabelQPilotBridgeAlignmentOutputFlagCalibrationSource_subclaimAudit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.sourceData
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.targetRegionFormulaSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.targetRegionClassFormulaSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.stepXLogKummerPackage
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.stepXLogKummerPackage_endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.qualitativeSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.theorem311BridgePackage
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.theorem311BridgePackage_hodgeSHEIPLAPTBridgeConstructed
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.bridge_noCollapse_audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.theorem311Subclaims
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.algorithmicOutputComponentSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.theorem311Subclaims_hodgeTheaterSHEAlignment
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.bridgeCertificateSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.bridgeCertificateSource_audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.bridgeCertificateConstructor
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.bridgeCertificateConstructor_audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.primitiveConstructor_qualitativeSource_eq_bridgeCertificate
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.primitiveConstructor
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.verticalLogKummerPacketAlignedOneSidedSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.verticalLogKummerPacketAlignedOneSidedSource_audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.verticalLogKummerPacketAlignedOneSidedSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.PacketAlignedFiberTransportOneSidedComparisonAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.packetAlignedFiberTransportOneSidedComparisonAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.ofPossibleImageWitnessSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.fiberInd2ActionPacketTransportSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.Audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.audit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource.thetaRegionPrincipalSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource.principalHullSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource.PrincipalValuationBallThetaRegionAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1ConcreteTheorem311PrimitiveSourcePacket.WithSymmetryLabelTransport.PrincipalValuationBallThetaRegionSource.audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.Audit
#guard_msgs (drop info) in
#check IUTStage1ConcreteTheorem311PrimitiveSourcePacket.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketTheorem311PrimitiveConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.thetaRegionPrincipalValuationBallRecordBoundedFamilyHullSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ThetaRegionPrincipalValuationBallMeasureSummandCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ThetaRegionPrincipalValuationBallMeasureSummandCalibrationSource.toMeasureCalibration
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ThetaRegionPrincipalValuationBallMeasureSummandCalibrationSource.toSummandChartedCalibration
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ThetaRegionPrincipalValuationBallMeasureSummandCalibrationSource.Endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ThetaRegionPrincipalValuationBallMeasureSummandCalibrationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXILocalTermCThetaSource.LocalTermIUTIVCThetaHandoffAudit.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXILocalTermCThetaSource.LocalTermIUTIVCThetaHandoffAudit.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource.toNormSquareDirectSummandLocalizedAdjustedCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource.Endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource.no_unitBallNormSquareHandoff
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelThetaRegionPrincipalHullConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelThetaRegionPrincipalHullConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.concretePacketThetaRegionSourceOfFiberBacked
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelFiberBackedThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelFiberBackedThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.concretePacketThetaRegionSourceOfThetaRegionDefinedPrincipalValuationBall
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelThetaRegionDefinedPrincipalValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelThetaRegionDefinedPrincipalValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.concretePacketThetaRegionSourceOfPrincipalPointwiseValuationBall
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationConstructedHDDLocalizedRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureSummandCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureSummandFormulaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureSummandFormulaSource.toPointwiseCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureSummandFormulaSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureDeterminantFormulaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureDeterminantFormulaSource.toPointwiseFormulaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallMeasureDeterminantFormulaSource.determinantCalibrationEndpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationConstructedHDDLocalizedRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallRestrictionCalibratedNormSquareOb7Source
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallRestrictionCalibratedNormSquareOb7Source.ofLocalArithmeticHandoffSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallRestrictionCalibratedNormSquareOb7Source.no_unitBallNormSquareHandoff
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeRestrictionAdditiveHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeRestrictionAdditiveHaarSource.toResidueRestrictionAdditiveHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeRestrictionAdditiveHaarSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.toInverseBasePrimeRestrictionAdditiveHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndConstructedGaussianHodgeSummand
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndConstructedGaussianHodgeLocalizedAdjusted
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndSquareDirectSummandConstructedGaussianHodge
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndNormSquareDirectSummandConstructedGaussianHodge
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndCompactOpenNormSquareDirectSummandConstructedGaussianHodge
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallInverseBasePrimeSummandProjectedAdditiveHaarSource.ofResidueModuleInverseBasePrimeValuationCoverAndAdditiveHaarCompactOpenNormSquareDirectSummandConstructedGaussianHodge
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallLocalizedStepXILocalTermCThetaSource.toLocalizedCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallLocalizedStepXILocalTermCThetaSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltFinitePlaceLocalGlobalCThetaSource.Endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltFinitePlaceLocalGlobalCThetaSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXILocalTermCThetaSource.LocalTermIUTIVCThetaHandoffAudit.finite_place_local_global_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallInverseBasePrimeRestrictionAdditiveHaarLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallIUTIVArithmeticDivisorLocalizedStepXISource.toLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallIUTIVArithmeticDivisorLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallStepXISynchronizationSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.local_defined_residual_eq_padic_index
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.residual_total_haar_defect_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.toIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.toTheorem110ValuationBallIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.toLocalizedCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXIDeterminantScaleSynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXIDeterminantScaleSynchronizationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSourceSynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaProductHandoffLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeRestrictionAdditiveHaarTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverHodgeSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverHodgeSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverLocalizedAdjustedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverLocalizedAdjustedConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverCompactOpenNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverCompactOpenNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandSynchronizedConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandPointwiseTheorem110FormulaGapMatchedIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaPointwiseRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaProductHandoffLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaRestrictionCalibratedLocalArithmeticPointwiseTheorem110FormulaGapMatchedIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalEstimatePointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalEstimatePointwiseResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.PadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.PadicNormalizedProcessionalEstimateSource.toProcessionalEstimatePointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofPadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofPadicNormalizedProcessionalEstimateSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofTheorem110ValuationBallLocalAnalyticProcessionalEstimatePadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofTheorem110ValuationBallLocalAnalyticPadicNormalizedProcessionalEstimateStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticSynchronizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticSynchronizedPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312PrimitiveTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDSourceGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalValuationThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelThetaRegionPrincipalHullConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelThetaRegionPrincipalHullConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelFiberBackedThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelFiberBackedThetaRegionConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelThetaRegionDefinedPrincipalValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelThetaRegionDefinedPrincipalValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallConstructedHDDLocalizedCalibrationRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationConstructedHDDLocalizedRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationConstructedHDDLocalizedRestrictionDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticConstructedHDDLocalizedDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallInverseBasePrimeRestrictionAdditiveHaarLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.iutIVLocalAnalyticCThetaSourceDataOfValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.iutIVTheorem110CThetaSourceDataOfValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketPossibleImageWitnessSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaLocalArithmeticConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaProductHandoffLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionRestrictionCalibratedNormSquareOb7HandoffSource.no_unitBallNormSquareHandoff
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallRestrictionCalibratedNormSquareOb7Source.no_unitBallNormSquareHandoff
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeRestrictionAdditiveHaarTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeSummandProjectedAdditiveHaarConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverHodgeSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverHodgeSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverLocalizedAdjustedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverLocalizedAdjustedConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverCompactOpenNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverCompactOpenNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandSynchronizedConstructedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaInverseBasePrimeValuationCoverAdditiveHaarCompactOpenNormSquareDirectSummandPointwiseTheorem110FormulaGapMatchedIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaPointwiseRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaProductHandoffLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaRestrictionCalibratedLocalArithmeticTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelCompactOpenLogKummerMapHodgeFormulaRestrictionCalibratedLocalArithmeticPointwiseTheorem110FormulaGapMatchedIUTIVLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticSynchronizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticSynchronizedPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor.record
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor.transportGuard
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor.synchronizedTransportGuard
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor.Audit
#guard_msgs (drop info) in
#check IUTStage1PrimitiveTheorem311SourceConstructor.audit

/-- Public Step (xi) hull-construction boundaries currently audited. -/
inductive PublicStepXIHullConstructionBoundary where
  | coordinateScalarImageConstructedTrace
  | realLineCoordinateScalarImageConstructedTrace
  | coordinateScalarImageExactImageValuationSelected
  | coordinateScalarImageValuationSelected
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
        "preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit_fromAdditiveHaarPayload",
      keyField := "coordinate_hull_route" },
    { boundary := .realLineCoordinateScalarImageConstructedTrace,
      auditTypeName :=
        "PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit",
      constructorName :=
        "preferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit_fromAdditiveHaarPayload",
      keyField := "real_line_coordinate_hull_route" },
    { boundary := .coordinateScalarImageExactImageValuationSelected,
      auditTypeName := "CoordinateScalarImageExactImageStepXIPublicAudit",
      constructorName := "coordinateScalarImageExactImageStepXIPublicAudit",
      keyField := "transported_public_exact_xi_source" },
    { boundary := .coordinateScalarImageValuationSelected,
      auditTypeName := "CoordinateScalarImageStepXIPublicAudit",
      constructorName := "coordinateScalarImageStepXIPublicAudit",
      keyField := "transported_public_exact_xi_source" },
    { boundary := .valuationUnitBallNonzeroScalarSelected,
      auditTypeName :=
        "ValuationUnitBallNonzeroScalarStepXIPublicAudit",
      constructorName := "valuationUnitBallNonzeroScalarStepXIPublicAudit",
      keyField := "transported_public_exact_xi_source" } ]

/-- Number of audited public Step (xi) hull-construction boundaries. -/
def publicStepXIHullConstructionInventory_count : Nat :=
  publicStepXIHullConstructionInventory.length

theorem publicStepXIHullConstructionInventory_count_eq :
    publicStepXIHullConstructionInventory_count = 5 :=
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
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusAdditiveHaarConstructedGaussianHodgeLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltFinitePlaceLocalGlobalCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit_ofAdditiveHaarConstructedSourceConstructorBuiltFinitePlaceLocalGlobalCThetaSourceDirect
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusAdditiveHaarConstructedGaussianHodgeLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.additiveHaarArithmeticDegreePadicRemainingPayloadAudit_ofAdditiveHaarConstructedSourceConstructorBuiltLocalizedStepXILocalTermCThetaSourceDirect
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeProjectedAdditiveHaarLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltFinitePlaceLocalGlobalCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeProjectedAdditiveHaarLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeSummandProjectedAdditiveHaarLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltFinitePlaceLocalGlobalCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeSummandProjectedAdditiveHaarLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusRestrictionAdditiveHaarConstructedGaussianHodgeLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeRestrictionAdditiveHaarConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusConstructedGaussianHodgeSummandRestrictionAdditiveHaarConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusAdditiveHaarConstructedGaussianHodgeLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionResidueModuleInverseBasePrimeHaarModulusAdditiveHaarStructureSheafNormalizedConstructedGaussianHodgeLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
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
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredConcreteLocalizedStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredConcreteLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPrincipalProductLocalizedStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPrincipalProductLocalizedCoverThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPrincipalProductLocalizedCoverCanonicalThetaStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredTransportedScalarParameterPrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredTransportedRepresentableScalarParameterPrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredTransportedLocallyRepresentableScalarParameterPrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredTransportedCoordinateScalarImagePrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredTransportedRealLineCoordinateScalarImagePrincipalProductLocalizedThetaEqFamilyHullStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductLocalizedCoverConstructedPaperTraceStepXIPaperSourceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductLocalizedCoverConstructedPaperTraceStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductLocalizedCoverCanonicalThetaConstructedPaperTraceStepXIPaperSourceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductLocalizedCoverCanonicalThetaConstructedPaperTraceStepXIPaperSourceRouteAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.transportedCoordinateScalarImageLocalizedThetaEqFamilyHullPaperTrace
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceStepXIPaperSourceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit_fromAdditiveHaarPayload
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
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit_fromAdditiveHaarPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.real_line_coordinate_hull_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicTransportedRealLineCoordinateScalarImageConstructedPaperTraceRouteBoundaryAudit.constructed_paper_trace

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.coordinateScalarImageStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit.coordinate_scalar_landing
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit.coordinate_scalar_preimage
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit.selected_hull_eq_valuation_cell_union
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit.adjusted_family_hull_eq_normalized_determinant
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageStepXIPublicAudit.transported_public_exact_xi_source

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.coordinateScalarImageExactImageStepXIPublicAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit.local_coordinate_exact_image
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit.coordinate_source_constructed_from_exact_image
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit.exact_image_landing_law
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit.exact_image_preimage_law
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.CoordinateScalarImageExactImageStepXIPublicAudit.transported_public_exact_xi_source

#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageThetaRegionScalarParameter
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageThetaRegionScalarParameter.ofChoice
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.coordinateThetaRegion
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.coordinateThetaRegion_ofChoice_eq_targetRegion
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource.ofExactImageDirectProductHullSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource.ofExactImageDirectProductHullSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource.toScalarParameterDirectProductHullSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource.selectedParameterRegion_eq_choiceTargetRegion
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionScalarImageSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionRealizedLocalImageSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionRealizedLocalImageSource.coordinateThetaRegion_eq_scalarImage
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionRealizedLocalImageSource.toCoordinateThetaRegionScalarImageSource
#guard_msgs (drop info) in
#check IUTStage1ConcreteHodgeTheaterLogThetaChoice.ThetaPilotClassPossibleImageSource.PackageTargetRegionLatticeFormulaSource.CoordinateThetaRegionRealizedLocalImageSource.endpoint

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.ConcreteHodgeTheaterLogThetaQuotientThetaPilotSource.ConcreteValuationBallThetaClassFiberTransportThetaRegionDefinedPrincipalValuationBallCompactOpenRealizedExactSource.thetaRegion_toSet_eq_realization_image_compactOpenSubset
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.ConcreteHodgeTheaterLogThetaQuotientThetaPilotSource.ConcreteValuationBallThetaClassFiberTransportThetaRegionDefinedPrincipalValuationBallCompactOpenRealizedExactSource.toCompactOpenLogKummerMapPossibleRegionSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.ConcreteHodgeTheaterLogThetaQuotientThetaPilotSource.ConcreteValuationBallThetaClassFiberTransportThetaRegionDefinedPrincipalValuationBallCompactOpenRealizedExactSource.compactOpenLogKummerMapPossibleRegionEndpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.ofCompactOpenRealizedExactSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.ofCompactOpenRealizedExactSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSourceFromSideConditions
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSourceFromSideConditions_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSourceFromHullDetDataAndSideConditions
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource.toConstructedHolomorphicHullDeterminantSourceOfCompactOpenRealizedExactHodgeCalibratedSourceFromHullDetDataAndSideConditions_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource.toHullDetSourceConstructor
#guard_msgs (drop info) in
#print axioms IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource.toHullDetSourceConstructor
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource.toHullDetObligations
#guard_msgs (drop info) in
#print axioms IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource.toHullDetObligations

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEq
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEq_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofRemark395HullSystemOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEq
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofRemark395ProductHullSystemOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEq
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofRemark395ProductHullSystemOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEq_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofRemark395ProductHullSystemOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEqFromObligations
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ofRemark395ProductHullSystemOb3Ob4AdjustedDeterminantSourceFromFamilyHullLogVolumeThetaEqFromObligations_endpoint

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.hodgeCanonicalDegree_eq_localPrime
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.toResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.boundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedConstructedStepXIRoute_fromConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence.route_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence.product_formula_ob7_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence.derived_tensor_power_bound
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence.determinant_prime_strip_global
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence.ob7_prime_strip_source_target
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicStepXIPaperSourceRouteAuditProductFormulaOb7DeterminantCalibratedEvidence

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.constructedGaussianHodgeSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.toDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.constructedGaussianHodgeSquareWeightToDirectSummandRawPositiveBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource.normalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.constructedGaussianHodgeNormalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource.rawPositiveNormalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.constructedGaussianHodgeRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.StepXIPaperDerivedHullDeterminantSource.StepXIThetaLGPLocalizedDiagonalDirectSummandConstructedGaussianHodgeEvaluationDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedRestrictionAnchoredOb7ConstructionSource.directSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductInverseDilationValuationCoverConstructedSourceCoreConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedDirectSummandHodgeFamilyHullCalibratedSource.constructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeSquareWeightDerivedDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousInverseDilationConstructedGaussianHodgeSquareWeightDerivedDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusInverseDilationConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusInverseDilationConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousHaarModulusAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicHaarModulusAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicHaarModulusAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicUnitBallHaarCharacterAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicUnitBallHaarCharacterAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductNonvacuousPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarConstructedGaussianHodgeDirectSummandRawPositiveNormalizedSummandSquareWeightLocalizedAdjustedHodgeSummandExpansionConstructedStepXIRouteBoundaryAudit

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteNormSquareDirectSummandLocalizedAdjustedCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteNormSquareDirectSummandLocalizedAdjustedCalibrationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteNormSquareDirectSummandLocalizedAdjustedCalibrationSource.normSquareDirectSummandLocalizedAdjustedBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.projectedPrincipalProductPadicFiniteSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.toNormSquareDirectSummandLocalizedAdjustedCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.NormSquareRestrictionCalibratedProjectionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.normSquareRestrictionCalibratedProjectionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteNormSquareDirectSummandLocalizedAdjustedCalibrationSource.positiveSummandNorm_eq_zero
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteNormSquareDirectSummandLocalizedAdjustedCalibrationSource.unitBallNormSquareNonzeroContradiction
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.toInverseDilationValuationCoverConstructedSourceCoreLocalizedAdjustedCalibrationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.ResidueModuleRestrictionInverseDilationStrictSelectedAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteExtensionIntrinsicResidueModuleUnitBallHaarCharacterAdditiveHaarStructureSheafNormalizedRestrictionCalibratedSource.residueModuleRestrictionInverseDilationStrictSelectedAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7BoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteMeasureModelFamilyHullIndexedLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteDirectProductMeasureModelLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCoreTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCoreCalibratedLocalRingChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCoreValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCorePrincipalValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCorePrincipalHullAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCoreHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteSourceCoreValuationCoverTransportedCalibrationHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteValuationCoverConstructedSourceCoreHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteExtensionBackedValuationCoverConstructedSourceCoreHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteExtensionIntrinsicValuationCoverConstructedSourceCoreHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalProductPadicFiniteExtensionIntrinsicValuationCoverConstructedSourceCoreHullFormationPossibleRegionAlignedValuationBallChartedTensorMeasureDirectProductLocalizedAdjustedNormSquareDirectSummandRestrictionHodgeFamilyHullCalibratedConstructedPaperTraceStepXIPaperSourceRouteAuditDiagonalPadicFiniteExtensionUnitBallCompactOpenNormSquareDirectSummandConstructedGaussianHodgeEvaluationLocalizedAdjustedRestrictionAnchoredOb7FromAdditiveHaarRemainingPayload
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312NormSquareRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312Route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HardenedIntrinsicPadicNormSquarePreferredRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.hardenedIntrinsicPadicNormSquarePreferredRouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.HardenedIntrinsicPadicNormSquareFromAdditivePayloadRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.hardenedIntrinsicPadicNormSquareFromAdditivePayloadRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RouteBoundaryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312SurfaceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312SurfaceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketRestrictionCalibratedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketRestrictionCalibratedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketRestrictionCalibratedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketRestrictionCalibratedLocalizedCThetaStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketRestrictionCalibratedLocalizedCThetaStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketRestrictionCalibratedLocalizedCThetaStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketPointwiseLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketPointwiseLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketPointwiseLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketIUTIVArithmeticDivisorLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketIUTIVArithmeticDivisorLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketIUTIVArithmeticDivisorLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketSynchronizedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketSynchronizedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketSynchronizedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketSynchronizedArithmeticRealizedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketSynchronizedArithmeticRealizedTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketFormulaGapSynchronizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaGapSynchronizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaGapSynchronizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaGapSynchronizedArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaGapSynchronizedArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourceFormulaGapMatched
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourceFormulaGapMatched
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110CompatibilitySource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110CompatibilitySource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110CompatibilitySource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110CompatibilitySource.toPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110CompatibilitySource.toPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.toCompatibilitySource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.toCompatibilitySource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.toLocalizedCThetaSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.toLocalizedCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallIUTIVLocalizedStepXISource.LocalizedLocalTermTheorem110ArithmeticRealizationSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermCompatibleTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermCompatibleTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketFormulaRealizedLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedLocalizedLocalTermArithmeticRealizedTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketFormulaRealizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketFormulaRealizedSynchronizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedSynchronizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedSynchronizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcretePacketFormulaRealizedConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedNormSquareLocalizedDeterminantLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedNormSquareLocalizedDeterminantLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedPadicFiniteExtensionLocalizedDeterminantLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedPadicFiniteExtensionLocalizedDeterminantLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenRestrictionCalibratedPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenRestrictionCalibratedPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffPointwiseTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffSynchronizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffSynchronizedLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketFormulaRealizedCompactOpenProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactProductHandoffConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedConstructedSynchronizationLocalArithmeticDegreeTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteLocalizedDeterminantLocalAnalyticTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteLocalizedDeterminantLocalAnalyticTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteLocalizedDeterminantLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteLocalizedDeterminantLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedSynchronizedPadicFiniteLocalizedDeterminantLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedSynchronizedPadicFiniteLocalizedDeterminantLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedSynchronizedPadicFiniteLocalizedDeterminantFormulaGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedSynchronizedPadicFiniteLocalizedDeterminantFormulaGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactRestrictionCalibratedPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenRealizedExactFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLocalChartFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLocalChartFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallFormulaGapCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallFormulaGapCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallFormulaGapCaseBoundedResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallFormulaGapCaseBoundedResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseBoundedResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseBoundedResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticCaseBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticCaseBoundedPointwiseResidualSource.toFormulaGapCaseBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticCaseBoundedPointwiseResidualSource.toFormulaGapCaseBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticCaseBoundedPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticCaseBoundedPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseSourceResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticCaseSourceResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerGraphFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerGraphFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogShellImageFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogShellImageFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenPossibleRegionExactFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenPossibleRegionExactFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerImageFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerImageFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerCorrespondenceFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerCorrespondenceFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerMapFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitFormulaCompactOpenLogKummerMapFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapFormulaSourceLocalArithmeticHandoffPadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteFormulaGapResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.toConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.toConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.toFormulaGapResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.toFormulaGapResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalAnalyticResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalAnalyticResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toPadicFiniteSynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toPadicFiniteSynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.canonicalCThetaScale_eq_padicFiniteLocalizedStepXISum
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.canonicalCThetaScale_eq_padicFiniteLocalizedStepXISum
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteLocalizedHullVectorBundleDecompositionSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.canonicalCThetaScale_eq_principalProductLocalizedStepXISum
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.canonicalCThetaScale_eq_principalProductLocalizedStepXISum
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toSignedCThetaBound
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.toSignedCThetaBound
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteQNormalizedLocalizedLocalAnalyticResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.toLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.qNormalizedEndpoint_fromScaleSynchronization
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.qNormalizedEndpoint_fromScaleSynchronization
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.qNormalizedDichotomy_fromScaleSynchronization
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.qNormalizedDichotomy_fromScaleSynchronization
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalizedLocalAnalyticResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalizedLocalAnalyticResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenLogKummerMapLocalArithmeticSourcePrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticSourcePrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticSourcePrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffPrincipalProductFormulaGapResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffPrincipalProductFormulaGapResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.toQNormalizedProjectedPrincipalProductSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.toQNormalizedProjectedPrincipalProductSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.goalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.goalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.SameIndexPublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.SameIndexPublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalAnalyticSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toQNormalizedProjectedPrincipalProductSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toQNormalizedProjectedPrincipalProductSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofWeightedDeterminantLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfWeightedDeterminantLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one_fromScaleSynchronization
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one_fromScaleSynchronization
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSourceScaleSynchronizedLocalAnalyticCThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSourceScaleSynchronizedLocalAnalyticCThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedFormulaGapSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toFormulaGapResidualHaarSourceOfCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toFormulaGapResidualHaarSourceOfCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.formulaGapEndpoint_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.formulaGapEndpoint_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapCaseBoundedResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionBoundSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionBoundSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionComparisonSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionComparisonSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.toScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedFormulaGapSourceOfLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.dichotomy_ofLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantScaleSynchronizedLocalAnalyticSource.cTheta_ge_neg_one_ofLocalAnalyticProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantScaleSynchronizedLocalAnalyticProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.residual_total_haar_defect_ge_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.residual_total_haar_defect_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.arithmeticUpperTerm_eq_stepXI_haar_main_sum
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.arithmeticUpperTerm_eq_stepXI_haar_main_sum
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.mainLogTerm_eq_sum
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.mainLogTerm_eq_sum
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.localStepXIHaar_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.localStepXIHaar_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.toLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.toLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeDefinedResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.total_defined_residual_ge_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.total_defined_residual_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.toDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.toDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseDefinedResidualLowerSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlaceHaarDefectLowerBoundSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlaceHaarDefectLowerBoundSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.localHaarNormalizationDefect_nonneg
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.localHaarNormalizationDefect_nonneg
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.normalizedPlace_defect_ge_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.normalizedPlace_defect_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.local_defined_residual_eq_haar_defect
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.local_defined_residual_eq_haar_defect
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.toPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.toPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePointwiseHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource.toPointwiseHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource.toPointwiseHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.localStepXIPadicHaarIndex_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.localStepXIPadicHaarIndex_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.toDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.toDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.toLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.toLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfLocalArithmeticDegreeResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfLocalArithmeticDegreeResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfDefinedResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfDefinedResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_localArithmeticDegree
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_localArithmeticDegree
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_localArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_localArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_definedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.residual_total_haar_defect_ge_one_of_definedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedFormulaGapSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toFormulaGapSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toFormulaGapSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.goalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.goalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedPointwiseDefinedResidualSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.toPointwiseDefinedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.toPointwiseDefinedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofSourceObligationGap
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofSourceObligationGap
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofSourceObligationGap
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofSourceObligationGap
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorSideConditions
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorSideConditions
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorSideConditions
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorSideConditions
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorHullDetObligations
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorHullDetObligations
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorHullDetObligations
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorHullDetObligations
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorConstructedHullDetSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorConstructedHullDetSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorConstructedHullDetSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorConstructedHullDetSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorPrincipalHDDSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorPrincipalHDDSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorInternalPrincipalHDDSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofPrimitiveConstructorInternalPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorInternalPrincipalHDDSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofPrimitiveConstructorInternalPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfFormulaGapCaseBoundedResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfFormulaGapCaseBoundedResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofLocalAnalyticIUTIVSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofLocalAnalyticIUTIVSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfLocalAnalyticIUTIVCaseBoundedResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfLocalAnalyticIUTIVCaseBoundedResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceOfLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.dichotomy_ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofFormulaGapSourceCaseBoundedResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.cTheta_ge_neg_one_ofLocalAnalyticIUTIVSourceLocalAnalyticCaseSourceResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexFormulaGapCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexFormulaGapCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexFormulaGapCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexFormulaGapCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexLocalAnalyticIUTIVLocalAnalyticCaseSourceResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toLocalArithmeticDegreeSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toLocalArithmeticDegreeSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toFormulaGapSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toFormulaGapSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.goalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.goalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedDefinedResidualSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toFormulaGapSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toFormulaGapSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toSameIndexQNormalizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.preferredPublicRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.goalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.goalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.publicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedLocalArithmeticDegreeSource.toScaleSynchronizedLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceToScaleSynchronizedLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceToScaleSynchronizedLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalArithmeticDegreeSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceToScaleSynchronizedLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceToScaleSynchronizedLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedPointwiseDefinedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSourceObligationGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSourceObligationGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSourceObligationGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceSourceObligationGapLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorHullDetObligationsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorHullDetObligationsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorHullDetObligationsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorHullDetObligationsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorConstructedHullDetSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorConstructedHullDetSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorConstructedHullDetSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorConstructedHullDetSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourcePrimitiveConstructorInternalPrincipalHDDSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.toLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConcretePacketProjectedPrincipalProductSameIndexWeightedDeterminantQNormalizedCaseBoundedResidualSource.toLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceToLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedCaseBoundedResidualSourceToLocalAnalyticSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffSameIndexProjectedPrincipalProductWeightedDeterminantQNormalizedLocalAnalyticSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidencePublicBoundaryInputInventoryAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.determinantSource_eq_principalProductLocalizedStepXI
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.determinantSource_eq_principalProductLocalizedStepXI
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.thetaSigned_le_iutiv_cTheta_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteAdjustedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.weightedDeterminantSource_eq_principalProductLocalizedStepXI
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.weightedDeterminantSource_eq_principalProductLocalizedStepXI
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedLocalizedLocalAnalyticResidualHaarSourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.goalEvidence_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.goalEvidence_ofLocalArithmeticDegreeResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceOfLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSourceCThetaGeNegOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312CThetaGeNegOneGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfLocalArithmeticDegreeResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfLocalArithmeticDegreeResidualSourceSideHypothesesLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfLocalArithmeticDegreeResidualSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfLocalArithmeticDegreeResidualSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfCaseBoundedResidualSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcretePacketExplicitDeterminantFormulaCompactOpenRealizedExactLocalArithmeticHandoffProjectedPrincipalProductWeightedDeterminantQNormalizedFormulaGapConstituentSourceOfCaseBoundedResidualSourceSideConditionsLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localHaarNormalizationDefect
#guard_msgs (drop info) in
#check IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource.toLocalCaseFormulaSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource.toLocalCaseFormulaSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localStepXIHaar_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localStepXIHaar_eq_arithmeticDegreePrimeMinusMain
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.total_haar_defect_ge_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.total_haar_defect_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localizedCThetaSourceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.localizedCThetaSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.toConstructorBuiltLocalizedStepXILocalTermCThetaSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.localizedCThetaSourceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteFormulaGapResidualHaarSource.localizedCThetaSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXILocalTermCThetaSource.LocalTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXILocalTermCThetaSource.localTermIUTIVCThetaHandoffAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaRouteAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaGoalEvidenceAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructorBuiltLocalizedCThetaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.iutIVLocalAnalyticCThetaSourceDataOfValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.iutIVTheorem110CThetaSourceDataOfValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#check IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource.ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedGoalEvidenceAudit.inverse_dilation_strict_selected
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedRouteAudit.restriction_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedRouteAudit.inverse_dilation_strict_selected
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteAudit.constructor_sourced_step_xi_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteFromObligations
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteFromObligationsAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteFromObligationsAudit.constructor_sourced_step_xi_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullLocalizedCThetaRouteFromObligationsAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.source_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.CanonicalHDDCommonContainer.withHDDHullDetBridge
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.CanonicalHDDCommonContainer.withHDDHullDetBridge_hullDetBridge
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.CanonicalHDDCommonContainer.transferRecord
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.CanonicalHDDCommonContainer.TransferredRecordAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.CanonicalHDDCommonContainer.transferredRecordAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.canonicalHDDPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.canonicalHDDPackage_hullDetBridge_eq_recordCanonical
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.canonicalHDDRecord
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.toCanonicalHDDConstructorBuiltSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.CanonicalHDDTransferredRecordAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.canonicalHDDTransferredRecordAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.DefinitionalHDDPackageAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDCommonContainerSource.definitionalHDDPackageAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource.canonicalHDDPackage
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource.canonicalHDDRecord
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource.toCanonicalHDDConstructorBuiltSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource.DirectCanonicalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullCanonicalHDDDirectCommonContainerSource.directCanonicalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullCanonicalHDDLocalizedCThetaRouteAudit.canonical_hdd_source_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.direct_canonical_hdd_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.GeneratedFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.GeneratedFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.GeneratedFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.toChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.toConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.toStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.toReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.toConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.generatedHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.Audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDSource.audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312GeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312GeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312GeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedRecordChosenOutputGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312StructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ReindexedStructuredGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedQualitativeGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.direct_canonical_hdd_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.restriction_calibrated_short_route_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.restriction_calibrated_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.generated_full_label_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit.direct_restriction_route_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedGeneratedFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedConstructedQualitativePrincipalProductHullOb3Ob5MeasureHodgeGapGeneratedChosenOutputFullLabelProductHullDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeCanonicalHDDDirectCommonContainerSource.toDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeCanonicalHDDDirectCommonContainerSource.Ob3Ob5AdjustedLogVolumeDirectHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeCanonicalHDDDirectCommonContainerSource.ob3ob5AdjustedLogVolumeDirectHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeDirectCanonicalHDDLocalizedCThetaRouteAudit.ob3ob5_adjusted_log_volume_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.toAdjustedLogVolumeDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.toDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.ofStructuredInputsWithSHEAndSideConditions
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.GapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.gapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.StructuredSHEGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeGapCanonicalHDDDirectCommonContainerSource.structuredSHEGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeGapDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.gap_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.thetaSigned_eq_ob3ob5FamilyHullLogVolume
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.toGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.toDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.HodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.hodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeHodgeGapCanonicalHDDDirectCommonContainerSource.structuredSHEHodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeHodgeGapDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.hodge_gap_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.measure_eq_ob3ob5HullLogVolume
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.toHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.toDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.MeasureHodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.measureHodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.structuredSHEMeasureHodgeGapCanonicalHDDDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.measure_hodge_gap_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.productHullOb3Ob5AdjustedDeterminantLogVolumeSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.ob3ob5_hullOperator_eq_productHull
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.toMeasureHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.ProductHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.productHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.structuredSHEProductHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.product_hull_constructed_ob3ob5_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.productHullSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.productHullSource_eq_principal
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.toProductHullConstructedOb3Ob5Source
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.PrincipalProductHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.principalProductHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource.structuredSHEPrincipalProductHullConstructedOb3Ob5MeasureHodgeGapDirectSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedPrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedPrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedPrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.principal_product_hull_direct_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312RestrictionCalibratedPrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit.restriction_calibrated_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312RestrictionCalibratedPrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapDirectCanonicalHDDLocalizedCThetaRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullGoalEvidenceAudit.restriction_calibrated_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedQualitativeCurrentProductHullGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedQualitativeCurrentProductHullGoalEvidenceAudit.constructed_qualitative_principal_route_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedQualitativeCurrentProductHullGoalEvidenceAudit.current_product_hull_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedQualitativeCurrentProductHullGoalEvidenceAudit.restriction_calibrated_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedQualitativeCurrentProductHullGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.current_product_hull_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.signed_ctheta_bound
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.formula_current_product_hull_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.signed_ctheta_bound
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit.dichotomy
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticHodgeFormulaTheorem110ValuationBallLocalAnalyticGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticConstructedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticConstructedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticSynchronizedConstructedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticSynchronizedConstructedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticSynchronizedFormulaGapMatchedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticSynchronizedFormulaGapMatchedTheorem110HodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticPointwiseTheorem110FormulaGapMatchedRouteInputHodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullLocalArithmeticPointwiseTheorem110FormulaGapMatchedRouteInputHodgeFormulaGoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.current_product_hull_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.constructor_built_step_xi_boundary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.norm_square_restriction_projection_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.projected_norm_square_ob7_boundary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit.projected_ob7_restriction_source_calibrated
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312CurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.structuredSHECurrentProductHullPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.structured_she_principal_product_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.current_norm_square_ob7_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.constructor_built_step_xi_boundary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit.source_gap_eq_structured_she
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312StructuredSHECurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.thetaRegionCurrentProductHullPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructedThetaRegionCurrentProductHullPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedThetaRegionCurrentProductHullPrincipalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedThetaRegionCurrentProductHullPrincipalHDDSourceAudit.transport_guard_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedThetaRegionCurrentProductHullPrincipalHDDSourceAudit.constructed_route_summary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructedThetaRegionCurrentProductHullPrincipalHDDSourceAudit.source_gap_eq_constructed_she
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructedThetaRegionCurrentProductHullPrincipalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.primitiveThetaRegionCurrentProductHullPrincipalHDDSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrimitiveThetaRegionCurrentProductHullPrincipalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrimitiveThetaRegionCurrentProductHullPrincipalHDDSourceAudit.primitive_constructor_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrimitiveThetaRegionCurrentProductHullPrincipalHDDSourceAudit.constructed_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrimitiveThetaRegionCurrentProductHullPrincipalHDDSourceAudit.source_gap_eq_primitive_constructed_she
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.primitiveThetaRegionCurrentProductHullPrincipalHDDSourceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.theta_region_source_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.current_norm_square_ob7_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.constructor_built_step_xi_boundary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_handoff_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.principal_hull_source_eq_theta_region
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.constructed_theta_region_source_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.theta_region_current_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.current_norm_square_ob7_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.constructor_built_step_xi_boundary
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.localized_ctheta_audit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit.source_gap_eq_constructed_she
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullNormSquareOb7GoalEvidenceAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullRoute
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullRouteAudit.route_eq_restriction_calibrated_route
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PreferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullRouteAudit.restriction_calibrated_goal_evidence
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedThetaRegionCurrentProductHullRouteAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312PrimitiveTheorem311ConstructedThetaRegionGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketTheorem311ConstructedThetaRegionGoalCompletionAudit

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESummandChartedHodgeSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESummandChartedHodgeSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.IUTStage1PreLedgerHolomorphicHullMeasureCalibration
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.IUTStage1PreLedgerHolomorphicHullMeasureCalibration.measure_eq_hullLogVolume
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESummandChartedHodgeMeasureCalibratedSource
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.principalProductHullConstructedOb3Ob5SourceOfThetaRegionDefinedPrincipalValuationBallStructuredSHESummandChartedHodgeMeasureCalibratedSource_endpoint

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

#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltLocalizedStepXIDeterminantScaleSynchronizationSource.thetaSigned_eq_localizedAdjustedSum_mul_absLogQ
#guard_msgs (drop info) in
#check IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.ConstructorBuiltPadicFiniteLocalizedStepXIDeterminantScaleSynchronizationSource.thetaSigned_eq_padicFiniteLocalizedAdjustedSum_mul_absLogQ
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPadicFiniteLocalizedLocalAnalyticResidualHaarSource.qNormalizedEndpoint_fromScaleSynchronization
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.toQNormalizedLocalizedLocalAnalyticResidualHaarSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.qNormalizedEndpoint_fromScaleSynchronization
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteLocalizedLocalAnalyticResidualHaarSource.qNormalizedDichotomy_fromScaleSynchronization

#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource.toLocalAnalyticCaseBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource.toLocalAnalyticCaseBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionBoundPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionBoundResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionBoundResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionBoundResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionBoundResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionBoundResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource.toLocalAnalyticProcessionBoundPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource.toLocalAnalyticProcessionBoundPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionComparisonPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionComparisonResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionComparisonResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionComparisonResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionComparisonResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionComparisonResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.processionNormalized_le_projectedProcessionUpperBound
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.processionNormalized_le_projectedProcessionUpperBound
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.toLocalAnalyticProcessionComparisonPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.toLocalAnalyticProcessionComparisonPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalEstimatePointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalEstimateResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalEstimateResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalEstimateResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalEstimateResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalEstimateResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.toGapBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.toGapBoundedPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.toPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.toPointwiseDefinedResidualLowerSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalArithmeticGapPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalArithmeticGapResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalArithmeticGapResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalArithmeticGapResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalArithmeticGapResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalArithmeticGapResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.distinguished_processionNormalized_plus_one_le_arithmeticMinusMain
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.distinguished_processionNormalized_plus_one_le_arithmeticMinusMain
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.toProcessionalArithmeticGapPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.toProcessionalArithmeticGapPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPointwiseResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPointwiseResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPointwiseResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPointwiseResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource.toProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource.toProcessionalPointwiseResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalHaarDefectResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.toProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.toProcessionalHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.toProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.toProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.constructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConstructorBuiltLocalizedStepXILocalTermCThetaSourceOfValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.ofPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.ofPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.ofPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.ofPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.localArithmeticUpperContribution_eq_stepXI_padicIndex_main
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.localArithmeticUpperContribution_eq_stepXI_padicIndex_main
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.toPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.toPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSourceToPadicUnitBallStepXISynchronizationSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSourceToPadicUnitBallStepXISynchronizationSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.toCorePadicUnitBallHaarIndexDefectSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource.toCorePadicUnitBallHaarIndexDefectSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource.ofProcessionalPadicUnitBallHaarDefectResidualSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSourceOfPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSourceOfPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSourceToLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSourceToLocalArithmeticDegreeResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.local_defined_residual_eq_padic_index
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.local_defined_residual_eq_padic_index
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.residual_total_haar_defect_ge_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallStepXISynchronizationSource.residual_total_haar_defect_ge_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSourceOfProcessionalPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSourceOfProcessionalPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourceProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.PadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.PadicNormalizedProcessionalCaseSource.toProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.PadicNormalizedProcessionalCaseSource.toProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.PadicNormalizedProcessionalCaseSource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.PadicNormalizedProcessionalCaseSource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource_endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSource.ofPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource_endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicIUTStage1IUTIVTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallHaarDefectResidualSourceOfPadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofTheorem110ValuationBallLocalAnalyticProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofLocalizedStepXILocalTermCThetaSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourceProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourceProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallIUTIVLocalizedStepXISourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceProcessionalPadicUnitBallStepXISynchronizationSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceProcessionalPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourceProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicUnitBallHaarDefectResidualSourcePadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceOfPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceOfPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISource.cTheta_ge_neg_one
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.cTheta_ge_neg_one_ofValuationBallLocalAnalyticSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.cTheta_ge_neg_one_ofValuationBallLocalAnalyticSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallHaarDefectResidualSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwisePadicUnitBallIUTIVLocalizedStepXISourceValuationBallLocalAnalyticPadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwisePadicUnitBallIUTIVLocalizedStepXISourceValuationBallLocalAnalyticPadicNormalizedProcessionalCaseSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallStepXISynchronizationSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallStepXISynchronizationSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceLocalDefinedResidualEqPadicIndexLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceLocalDefinedResidualEqPadicIndexLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceResidualTotalHaarDefectGeOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceResidualTotalHaarDefectGeOneLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallHaarDefectResidualSourceLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallHaarDefectResidualSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceToPadicUnitBallHaarDefectResidualSourceEndpointLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceOfPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicPrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISourceOfPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseLocalUpperTheorem110ValuationBallIUTIVLocalizedStepXI311312ConstructorAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.ofPointwiseTheorem110ValuationBallLocalAnalyticIUTIVLocalizedStepXISourcePadicNormalizedProcessionalEstimateSource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.toPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalPointwiseValuationBallProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXISource.endpoint
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticSynchronizedProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticLocalizedLocalTermProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110ProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticProcessionalPadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110ProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110ProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110PadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110PadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAudit
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110PadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110PadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110ProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110ProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicNormalizedProcessionalEstimatePadicUnitBallIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticProcessionalPadicUnitBallHaarDefectResidualIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalEstimateIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwiseTheorem110LocalAnalyticPadicUnitBallHaarDefectResidualPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#check IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias
#guard_msgs (drop info) in
#print axioms IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.preferredPublicConcreteStepXI311312ConcretePacketWithSymmetryLabelPrincipalPointwiseValuationBallCalibrationLocalArithmeticPointwisePadicUnitBallValuationBallLocalAnalyticPadicNormalizedProcessionalCaseIUTIVArithmeticDivisorLocalizedStepXIConstructedHDDDataGoalCompletionAuditAlias

#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.localPrimeErrorContribution
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.localPrimeErrorContribution_eq_padicHaarDefect_main
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.localPrimeErrorContribution_eq_padicHaarDefect_main
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.primeErrorSplitAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.primeErrorSplitAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.toPrimeErrorPadicDefectMainSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.primeErrorProjectionAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.primeErrorProjectionAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.ofAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.additiveHaarEvaluationSourceAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainLocalAnalyticArithmeticDivisorSource.additiveHaarEvaluationSourceAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.valuationBallFormulaGapPrimeErrorAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.valuationBallFormulaGapPrimeErrorAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.ofArithmeticDegreeControlledLocalArithmeticSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.arithmeticDegreeControlledSourceAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.arithmeticDegreeControlledSourceAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.ofFormulaGapMatchedArithmeticDegreePadicComparisonSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.formulaGapMatchedComparisonSourceAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.formulaGapMatchedComparisonSourceAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.ofFormulaGapMatchedArithmeticDegreePadicLocalDegreeFormulaSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.formulaGapMatchedLocalDegreeFormulaSourceAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110PadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource.formulaGapMatchedLocalDegreeFormulaSourceAudit
#guard_msgs (drop info) in
#check Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toPadicDefectMainValuationBallLocalAnalyticArithmeticDivisorSource
#guard_msgs (drop info) in
#check Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.RecordOb3Ob5ArithmeticDivisorBackedComponentSource.recordOb3Ob5PadicDefectMainProjectionAudit
#guard_msgs (drop info) in
#print axioms Experiments.ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource.RecordOb3Ob5ArithmeticDivisorBackedComponentSource.recordOb3Ob5PadicDefectMainProjectionAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.toArithmeticDegreePadicPrimeErrorFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.constructedPrimeErrorArithmeticDegreeAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.constructedPrimeErrorArithmeticDegreeAudit
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
#guard_msgs (drop info) in
#check Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.constructedPrimeErrorFormulaGapAudit
#guard_msgs (drop info) in
#print axioms Experiments.IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.constructedPrimeErrorFormulaGapAudit

end IUTStage1StepXIDependencyAudit
end Stage1
end Iut
