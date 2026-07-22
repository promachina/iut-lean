/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/

/-!
# M1-M3 primary-source ledger

This file is the machine-readable review surface for the M1-M3 reconstruction.
The direct sources are the published IUT I-III papers. The ledger also includes
the transitive source definitions that they invoke, beginning with Etale Theta
Section 2. Exact local artifacts are stored in `docs/papers/`.

`partialImplementation` means that a declaration captures some genuine source
data but not the whole clause. `toyModel` means that the declaration is useful
for testing later formal interfaces but cannot discharge the paper clause.
-/

namespace Iut.SourceTrace

/-- The paper containing a source clause. -/
inductive PaperVolume
  | frobenioidsI
  | frobenioidsII
  | iutI
  | iutII
  | iutIII
  | etaleTheta
  | absoluteAnabelianIII
  deriving DecidableEq, Repr

/-- Honest implementation status of a paper clause. -/
inductive ClauseStatus
  | sourceFaithful
  | partialImplementation
  | toyModel
  | unformalized
  deriving DecidableEq, Repr

/-- Traceability data from one paper clause to the current Lean surface. -/
structure PaperClause where
  id : String
  volume : PaperVolume
  source : String
  leanDeclarations : List String
  status : ClauseStatus
  gap : String
  deriving Repr

/-- An exact primary-source artifact used by the clause audit. -/
structure PaperSourceDocument where
  volume : PaperVolume
  repositoryPath : String
  sha256 : String
  deriving Repr

/-- Exact local copies of the direct and transitive primary sources used for this audit. -/
def m1m3SourceDocuments : List PaperSourceDocument :=
  [ { volume := .frobenioidsI,
      repositoryPath := "docs/papers/mochizuki-frobenioids-i.pdf",
      sha256 := "8e5ac14e3aadb457ee4edde81a325b64b060cefb14712d70cf2ca66b373aaf53" },
    { volume := .frobenioidsII,
      repositoryPath := "docs/papers/mochizuki-frobenioids-ii.pdf",
      sha256 := "0185e64c4107123a20d2fd72f6e5a5ff8e5c1356d3caee69b7d5700e291ac0a9" },
    { volume := .iutI,
      repositoryPath := "docs/papers/mochizuki-iut-i.pdf",
      sha256 := "7360e3ed27c235b5497a0743d3ed1646fbb97688547d16b7c784fc7f127f1f03" },
    { volume := .iutII,
      repositoryPath := "docs/papers/mochizuki-iut-ii.pdf",
      sha256 := "180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c" },
    { volume := .iutIII,
      repositoryPath := "docs/papers/mochizuki-iut-iii.pdf",
      sha256 := "9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9" },
    { volume := .etaleTheta,
      repositoryPath := "docs/papers/mochizuki-etale-theta-frobenioid.pdf",
      sha256 := "42c5d9180c69bc9fa6596ce1a11662494315954ed74301060bf1819f955a7406" },
    { volume := .absoluteAnabelianIII,
      repositoryPath := "docs/papers/mochizuki-absolute-anabelian-topics-iii.pdf",
      sha256 := "e8115df30a86dea26e2ebf60cb333558ff28fe3e4d57017a80421787b53421a9" } ]

theorem m1m3SourceDocuments_count : m1m3SourceDocuments.length = 7 :=
  rfl

private def clause
    (id : String) (volume : PaperVolume) (source : String)
    (leanDeclarations : List String) (status : ClauseStatus) (gap : String) :
    PaperClause :=
  { id, volume, source, leanDeclarations, status, gap }

/--
Clause-level ledger for every paper item cited directly by the M1-M3 scope.

Subclauses are split when their mathematical content or current Lean status is
different. Prerequisites cited transitively by these clauses are added as their
definitions enter the implementation dependency closure.
-/
def m1m3PaperLedger : List PaperClause :=
  [ clause "FrdI.1.1(i-ii)" .frobenioidsI
      "Frobenioids I, Definition 1.1(i)-(ii)"
      ["DivisorialAddMonoid", "DivisorialMonoidOn",
        "DivisorialMonoidOn.functor"] .partialImplementation
      "Sharpness, integrality, saturation in the Grothendieck group, contravariant pullback, characteristic injectivity, and the FSM-isomorphism contract are explicit. The general characteristic quotient of a pre-divisorial non-sharp monoid and the source definition of FSM morphisms remain open.",
    clause "FrdI.1.1(iii-iv)" .frobenioidsI
      "Frobenioids I, Definition 1.1(iii)-(iv)"
      ["ElementaryFrobenioidHom", "ElementaryFrobenioid",
        "ElementaryFrobenioid.base", "PreFrobenioid",
        "PreFrobenioidPresentation", "FrobenioidPresentation",
        "PreFrobenioid.divisor_comp",
        "PreFrobenioid.frobeniusDegree_comp"] .partialImplementation
      "The elementary Frobenioid is an actual category with the paper's base/divisor/positive-degree arrows and composition law, and a pre-Frobenioid is an actual functor to it. FrobenioidPresentation packages connectedness, total epimorphicity, and Definition 1.3. The general pre-divisorial characteristic quotient and formal source definition of FSM remain open.",
    clause "FrdI.1.2" .frobenioidsI
      "Frobenioids I, Definition 1.2"
      ["PreFrobenioid.IsLinear", "PreFrobenioid.IsIsometric",
        "PreFrobenioid.IsBaseIso", "PreFrobenioid.IsPreStep",
        "PreFrobenioid.PullbackComparisonTarget",
        "PreFrobenioid.IsPullback",
        "PreFrobenioid.IsCoAngular",
        "PreFrobenioid.IsLBInvertible",
        "PreFrobenioid.IsOfFrobeniusType",
        "PreFrobenioid.IsIsotropic",
        "PreFrobenioid.FrobeniusTrivialization",
        "PreFrobenioid.IsFrobeniusNormalized",
        "PreFrobenioid.IsFrobeniusNormalizedType"]
      .partialImplementation
      "The principal source morphism classes are literal predicates on actual categorical arrows; pullback uses the representable fiber-product comparison, Frobenius triviality is a multiplicative degree section by Frobenius-type endomorphisms, and Frobenius normalization is the paper's power-conjugation equation. The remaining ample, perfect, compact, and related object classes remain open.",
    clause "FrdI.1.3" .frobenioidsI
      "Frobenioids I, Definition 1.3"
      ["PreFrobenioid.FrobenioidAxioms",
        "PreFrobenioid.PullbackBaseSliceEquivalence",
        "PreFrobenioid.CommonPreStepWitness",
        "PreFrobenioid.FrobeniusDegreeWitness",
        "PreFrobenioid.FrobenioidFactorization",
        "PreFrobenioid.PreStepFactorization",
        "PreFrobenioid.IsotropicHull",
        "PreFrobenioid.CoAngularUnitTransport",
        "PreFrobenioid.OutgoingCoAngularPreStep",
        "PreFrobenioid.IncomingCoAngularPreStep",
        "FrobenioidPresentation"] .partialImplementation
      "All seven axiom groups are explicit: base-slice and divisor-order classifications, common pre-steps, Frobenius-degree essential uniqueness, co-angular unit transport, arbitrary and pre-step factorization with unique comparison isomorphisms, faithfulness up to base-identity automorphisms, and isotropic hulls. This remains partial until the pointwise slice classifications are connected to formal category equivalences and the definition is validated clause-by-clause against the source.",
    clause "FrdI.2.2" .frobenioidsI
      "Frobenioids I, Proposition 2.2"
      ["PreFrobenioid.IsotropicLinearObject",
        "PreFrobenioid.IsotropicLinearHom",
        "PreFrobenioid.RationalMonoidTransport",
        "PreFrobenioid.RationalMonoidTransport.functor",
        "SourceModelFrobenioid.Carrier.linearEndomorphismPullbackHom",
        "SourceModelFrobenioid.Carrier.rationalMonoidTransport"]
      .partialImplementation
      "The isotropic linear category and actual base-identity linear endomorphism monoids are typed. In Theorem 5.2's model, divisor and rational-function pullback construct the contravariant monoid transport with identity and composition laws, while co-angular unit transport supplies the injective isotropic-hull map. Deriving this transport for an arbitrary Frobenioid solely from Definition 1.3, and proving the divisor/characteristic-quotient assertions, remain open.",
    clause "FrdI.2.3" .frobenioidsI
      "Frobenioids I, Definition 2.3"
      ["PreFrobenioid.CharacteristicSplitting",
        "SplitFrobenioidPresentation",
        "SplitFrobenioidEquivalence",
        "SplitFrobenioidEquivalence.refl",
        "SplitFrobenioidEquivalence.trans"]
      .partialImplementation
      "A characteristic splitting is an actual subfunctor of O-triangle, multiplication with units is objectwise bijective with commuting factors, and the isotropic-hull image condition is explicit. Split Frobenioids carry a nonempty indexed collection of such splittings with structure-preserving equivalences. Constructing the splittings in Examples 3.2-3.4 remains open.",
    clause "FrdI.2.7" .frobenioidsI
      "Frobenioids I, Definition 2.7"
      ["PreFrobenioid.BaseSection",
        "PreFrobenioid.FrobeniusSection",
        "PreFrobenioid.BaseFrobeniusPair",
        "PreFrobenioid.IsPreModelType",
        "SourceModelFrobenioid.Carrier.zeroBaseSection",
        "SourceModelFrobenioid.Carrier.zeroFrobeniusSection",
        "SourceModelFrobenioid.Carrier.baseFrobeniusPair",
        "SourceModelFrobenioid.Carrier.isPreModelType"]
      .sourceFaithful
      "A base-section is a skeletal faithful subcategory of actual pullback arrows, consists of Frobenius-trivial objects, and projects equivalently to D. A Frobenius-section is a multiplicative family of natural endomorphisms with the exact degree, base-identity, and Frobenius-type clauses. For the model Frobenioid, the zero-divisor objects over a skeleton of D and their canonical degree-n maps construct the base-Frobenius pair specified in the proof of Theorem 5.2(ii).",
    clause "FrdI.4.4" .frobenioidsI
      "Frobenioids I, Proposition 4.4"
      ["SourceModelFrobenioid.zeroDivisorialMonoidOn",
        "SourceModelFrobenioid.BirationalObject",
        "SourceModelFrobenioid.BirationalHom",
        "SourceModelFrobenioid.BirationalHom.divisorClass",
        "SourceModelFrobenioid.BirationalObject.structureFunctor",
        "SourceModelFrobenioid.BirationalObject.preFrobenioid",
        "SourceModelFrobenioid.BirationalObject.inclusionFunctor",
        "SourceModelFrobenioid.BirationalObject.inclusionFunctor_faithful",
        "SourceModelFrobenioid.BirationalObject.inclusionFunctor_map_divisorClass",
        "SourceModelFrobenioid.BirationalObject.inclusion_map_isIso_of_preStep",
        "SourceModelFrobenioid.BirationalObject.frobenioidAxioms",
        "SourceModelFrobenioid.BirationalObject.frobenioidPresentation",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.homDiagram",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.BirationalHomColimit",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.isFilteredIndexOp",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.colimitComparisonEquiv",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.compositionSquare",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.roofValue_compositeRoof",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.composition_on_roof_iota",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor_faithful",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor_map_isIso_of_preStep",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.preFrobenioid",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.preFrobenioidPresentation",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.frobenioidAxioms",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.frobenioidPresentation",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isGroupLikeType",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.groupifiedDivisorClass",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.comparisonEquivalence",
        "SourceModelFrobenioid.BirationalObject.isIso_iff_isPreStep",
        "SourceModelFrobenioid.BirationalObject.isIsotropic",
        "SourceModelFrobenioid.BirationalObject.isPullback_iff_isLinear",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.BaseIdentityRoof",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isBaseIdentity_iff_nonempty_baseIdentityRoof",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isIso_iff_isPreStep",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isIsotropic",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isPullback_iff_isLinear",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isIso_iff_coAngularPreStep",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isPullback_iff",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isPreStep_iff_isPreStep",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isCoAngular_iff_isCoAngular",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isBaseIso_iff_isBaseIso",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_frobeniusDegree_eq_iff",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isOfFrobeniusType_iff",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_map_isIsometric",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localization_obj_isIsotropic_iff",
        "SourceModelFrobenioid.GroupifiedDivisorSubfunctor",
        "SourceModelFrobenioid.GroupifiedElementaryFrobenioid",
        "SourceModelFrobenioid.GroupifiedElementaryFrobenioid.inclusion_faithful",
        "SourceModelFrobenioid.Input.birationalDivisorSubfunctor",
        "SourceModelFrobenioid.BirationalObject.birationalDivisorFunctor",
        "SourceModelFrobenioid.BirationalObject.groupifiedDivisorFunctor_factorization",
        "SourceModelFrobenioid.Carrier.groupifiedStructureComparison",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.birationalDivisorFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.groupifiedDivisorFunctor_factorization",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.birationalDivisorHom_surjective",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.birationalDivisorHom_eq_one_iff_sourceUnitImage",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.birationalDivisorSubfunctor_unique"]
      .sourceFaithful
      "All four assertions are proved for the Theorem 5.2 model: the filtered Hom colimit and source composition square construct the birational category; the actual colimit is a connected, totally epimorphic, group-like Frobenioid satisfying all seven Definition 1.3 axiom groups; the unique divisor image subfunctor and exact unit kernel sequence are constructed; and every morphism and object clause of (iv), including the exact base-identity roof classification, is proved.",
    clause "FrdI.4.5(i)" .frobenioidsI
      "Frobenioids I, Definition 4.5(i)"
      ["PreFrobenioid.IsBirationallyFrobeniusNormalized",
        "PreFrobenioid.IsBirationallyFrobeniusNormalizedType",
        "PreFrobenioid.IsModelType",
        "SourceModelFrobenioid.BirationalObject.isFrobeniusNormalized",
        "SourceModelFrobenioid.BirationalObject.isFrobeniusNormalizedType",
        "SourceModelFrobenioid.BirationalObject.isModelTypeForConcreteBirationalization",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isFrobeniusNormalizedType",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isModelTypeForColimitBirationalization"]
      .partialImplementation
      "The three source predicates are explicit relative to a typed birationalization functor. The canonical filtered-colimit target is proved Frobenius-normalized and combines with the model's base-Frobenius pair to satisfy model type. Proving the source's general implication from birational Frobenius normalization back to Frobenius normalization remains open.",
    clause "FrdI.5.2(i)" .frobenioidsI
      "Frobenioids I, Theorem 5.2(i)"
      ["SourceModelFrobenioid.GroupLikeAddMonoidOn",
        "SourceModelFrobenioid.gpPullback",
        "SourceModelFrobenioid.gpPullback_id",
        "SourceModelFrobenioid.gpPullback_comp",
        "SourceModelFrobenioid.Input",
        "SourceModelFrobenioid.Input.birationalDivisors",
        "SourceModelFrobenioid.Object",
        "SourceModelFrobenioid.Hom",
        "SourceModelFrobenioid.Hom.comp",
        "SourceModelFrobenioid.Carrier",
        "SourceModelFrobenioid.Carrier.structureFunctor",
        "SourceModelFrobenioid.Carrier.preFrobenioid"]
      .sourceFaithful
      "The group-like monoid is a genuine Definition 1.1(ii) monoid on D: pullbacks are injective and FSM pullbacks are bijective. The exact object and four-component arrow data, balance equation, identity, composition formulas, category laws, birational-divisor image, and functor to the elementary Frobenioid are constructed. The Frobenioid-axiom conclusion belongs to Theorem 5.2(ii), not this clause.",
    clause "FrdI.5.2(ii)" .frobenioidsI
      "Frobenioids I, Theorem 5.2(ii)"
      ["SourceModelFrobenioid.Carrier.zeroObject",
        "SourceModelFrobenioid.Carrier.effectiveObject",
        "SourceModelFrobenioid.Carrier.toEffectiveObject",
        "SourceModelFrobenioid.Carrier.zeroToEffectiveObject",
        "SourceModelFrobenioid.Carrier.isConnected",
        "SourceModelFrobenioid.Carrier.epi",
        "SourceModelFrobenioid.Carrier.inverseOfPreStepIsometric",
        "SourceModelFrobenioid.Carrier.isIso_of_preStep_isometric",
        "SourceModelFrobenioid.Carrier.isIsotropic",
        "SourceModelFrobenioid.Carrier.isCoAngular",
        "SourceModelFrobenioid.Carrier.isOfFrobeniusType_iff",
        "SourceModelFrobenioid.Carrier.zeroFrobeniusTrivialization",
        "SourceModelFrobenioid.Carrier.baseRepresented",
        "SourceModelFrobenioid.Carrier.commonLower_add_left",
        "SourceModelFrobenioid.Carrier.commonLower_add_right",
        "SourceModelFrobenioid.Carrier.localizationRepresentative",
        "SourceModelFrobenioid.Carrier.commonPreSteps",
        "SourceModelFrobenioid.Carrier.pullbackObject",
        "SourceModelFrobenioid.Carrier.pullbackArrow",
        "SourceModelFrobenioid.Carrier.pullbackArrow_isPullback",
        "SourceModelFrobenioid.Carrier.pullbackSliceProjection_bijective",
        "SourceModelFrobenioid.Carrier.pullbackBaseSlices",
        "SourceModelFrobenioid.Carrier.frobeniusCodomain",
        "SourceModelFrobenioid.Carrier.frobeniusArrow",
        "SourceModelFrobenioid.Carrier.frobeniusComparison",
        "SourceModelFrobenioid.Carrier.frobeniusDegreeWitness",
        "SourceModelFrobenioid.Carrier.isotropicHull",
        "SourceModelFrobenioid.Carrier.isotropic_closedUnderTargets",
        "SourceModelFrobenioid.Carrier.coAngular_comp",
        "SourceModelFrobenioid.Carrier.parallelToCoAngularPreStep",
        "SourceModelFrobenioid.Carrier.endomorphism_divisor_eq",
        "SourceModelFrobenioid.Carrier.baseIsoTransport",
        "SourceModelFrobenioid.Carrier.baseIsoTransportEquiv",
        "SourceModelFrobenioid.Carrier.baseIsoTransport_conjugates",
        "SourceModelFrobenioid.Carrier.unitTransport",
        "SourceModelFrobenioid.Carrier.unitTransport_unique",
        "SourceModelFrobenioid.Carrier.unitTransport_dependsOnlyOnBase",
        "SourceModelFrobenioid.Carrier.outgoingDivisorTarget",
        "SourceModelFrobenioid.Carrier.outgoingDivisorArrow",
        "SourceModelFrobenioid.Carrier.outgoingDivisorRepresentative",
        "SourceModelFrobenioid.Carrier.outgoingDivisorComparison",
        "SourceModelFrobenioid.Carrier.outgoingDivisorOrderFullyFaithful",
        "SourceModelFrobenioid.Carrier.outgoingDivisorRepresentative_unique",
        "SourceModelFrobenioid.Carrier.incomingDivisorSource",
        "SourceModelFrobenioid.Carrier.incomingDivisorArrow",
        "SourceModelFrobenioid.Carrier.incomingDivisor",
        "SourceModelFrobenioid.Carrier.incomingDivisorRepresentative",
        "SourceModelFrobenioid.Carrier.incomingDivisorComparison",
        "SourceModelFrobenioid.Carrier.incomingDivisorOrderFullyFaithful",
        "SourceModelFrobenioid.Carrier.incomingDivisorRepresentative_unique",
        "SourceModelFrobenioid.Carrier.factorizationPreStep",
        "SourceModelFrobenioid.Carrier.factorization",
        "SourceModelFrobenioid.Carrier.isIso_linear_isometric",
        "SourceModelFrobenioid.Carrier.pullback_linear_lbInvertible",
        "SourceModelFrobenioid.Carrier.factorizationPullbackComparison",
        "SourceModelFrobenioid.Carrier.factorizationFrobeniusComparison",
        "SourceModelFrobenioid.Carrier.factorizationIso",
        "SourceModelFrobenioid.Carrier.factorizationIso_unique",
        "SourceModelFrobenioid.Carrier.preStep_mono",
        "SourceModelFrobenioid.Carrier.preStep_coAngularThenIsometric",
        "SourceModelFrobenioid.Carrier.transportedPreStepDivisor",
        "SourceModelFrobenioid.Carrier.preStep_isometricThenCoAngular",
        "SourceModelFrobenioid.Carrier.preStepFactorizationIso",
        "SourceModelFrobenioid.Carrier.preStepFactorizationIso_unique",
        "SourceModelFrobenioid.Carrier.faithfulUnitRationalFunction",
        "SourceModelFrobenioid.Carrier.faithfulUnit",
        "SourceModelFrobenioid.Carrier.faithfulUpToUnits",
        "SourceModelFrobenioid.Carrier.linearEndomorphismPullbackHom",
        "SourceModelFrobenioid.Carrier.rationalMonoidTransport",
        "SourceModelFrobenioid.Carrier.zeroBaseArrow_isPullback",
        "SourceModelFrobenioid.Carrier.zeroBaseSection",
        "SourceModelFrobenioid.Carrier.zeroFrobeniusNaturalTransformation",
        "SourceModelFrobenioid.Carrier.zeroFrobeniusSection",
        "SourceModelFrobenioid.Carrier.baseFrobeniusPair",
        "SourceModelFrobenioid.Carrier.isPreModelType",
        "SourceModelFrobenioid.Carrier.frobenioidAxioms",
        "SourceModelFrobenioid.Carrier.preFrobenioidPresentation",
        "SourceModelFrobenioid.Carrier.frobenioidPresentation",
        "SourceModelFrobenioid.BirationalObject.inclusionFunctor_faithful",
        "SourceModelFrobenioid.BirationalObject.inclusion_map_isIso_of_preStep",
        "SourceModelFrobenioid.BirationalObject.rationalFunctionEquiv",
        "SourceModelFrobenioid.BirationalObject.rationalFunctionEndomorphism_divisorClass",
        "SourceModelFrobenioid.BirationalObject.frobenioidAxioms",
        "SourceModelFrobenioid.BirationalObject.frobenioidPresentation",
        "SourceModelFrobenioid.BirationalObject.isModelTypeForConcreteBirationalization",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.colimitComparisonEquiv",
        "SourceModelFrobenioid.Carrier.CoAngularPreStepOver.roofValue_compositeRoof",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.composition_on_roof_iota",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor_faithful",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor_map_isIso_of_preStep",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.preFrobenioid",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.preFrobenioidPresentation",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.frobenioidAxioms",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.frobenioidPresentation",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isGroupLikeType",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalFunctionEquiv",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.linearBaseIdentityEndomorphism_isIso",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalFunctionEndomorphism_groupifiedDivisorClass",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.isModelTypeForColimitBirationalization",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.comparisonEquivalence",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.linearEndomorphismPullback_conjugates",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalMonoidTransport",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.zeroIsotropicLinearFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalMonoidFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.inputRationalFunctionFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalFunctionNatIso",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalFunctionNatIso_divisor_compatible",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.linearEndomorphismUnit",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalUnitEquiv",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalUnitFunctor",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalUnitNatIso",
        "SourceModelFrobenioid.Carrier.ColimitBirationalObject.rationalUnitNatIso_divisor_compatible"]
      .sourceFaithful
      "The model category, concrete birational target, and actual canonical Hom-colimit target are full Frobenioid presentations. All seven Definition 1.3 axiom groups, source roof composition, canonical model type, group-like and Frobenius-normalized type are proved. Proposition 2.2 transport is constructed on the actual Hom-colimit and characterized by its conjugation square. Every O-triangle element is constructed as a literal unit; restriction of this units subfunctor along the canonical zero-object section gives O-times on D, with a natural isomorphism to B compatible with the groupified divisor maps, exactly as asserted.",
    clause "FrdII.5.1" .frobenioidsII
      "Frobenioids II, Definition 5.1"
      [] .unformalized
      "Grafting data, contact functors, tactile morphisms, and the grafted category remain to be formalized.",
    clause "FrdII.5.3" .frobenioidsII
      "Frobenioids II, Definition 5.3"
      [] .unformalized
      "GC/LC-admissibility and poly-Frobenioids remain to be formalized.",
    clause "I.0.pseudo-monoid" .iutI
      "IUT I, Section 0: topological pseudo-monoids"
      ["SourceTopologicalPseudoMonoid",
        "SourceTopologicalPseudoMonoid.Carrier",
        "SourceTopologicalPseudoMonoid.MultiplicationDomain",
        "SourceTopologicalPseudoMonoid.partialMul",
        "SourceTopologicalPseudoMonoid.carrier_isEmbedding",
        "SourceTopologicalPseudoMonoid.continuous_partialMul",
        "SourceTopologicalPseudoMonoid.partialMul_comm",
        "SourceTopologicalPseudoMonoid.partialMul_assoc",
        "SourceTopologicalPseudoMonoid.IsDivisible",
        "SourceTopologicalPseudoMonoid.IsCyclotomic",
        "SourceTopologicalPseudoMonoid.Hom",
        "SourceTopologicalPseudoMonoid.Iso.maps_domain_iff",
        "SourceTopologicalGroupPseudoMonoidActionPair",
        "SourceTopologicalGroupPseudoMonoidActionPair.action_maps_domain_iff",
        "SourceTopologicalGroupPseudoMonoidActionPair.action_partialMul"]
      .sourceFaithful
      "The chosen ambient topological abelian group and embedded image are retained. Multiplication is defined exactly on pairs whose ambient product remains in the image, is continuous, commutative, and associative wherever the relevant composites exist. Divisibility and cyclotomicity are the paper's ambient-root, power-membership, torsion Q/Z, and torsion-stability conditions. Continuous morphisms preserve defined products, categorical isomorphisms reflect their domain, and continuous group actions are by these actual pseudo-monoid automorphisms.",
    clause "I.3.1(a)" .iutI "IUT I, Definition 3.1(a)"
      ["PrimeGeFive", "ThetaFieldTower", "SqrtMinusOneData",
        "AbsoluteGaloisProfinite", "SignQuotientOrbicurveData.absoluteGalois_def",
        "SourceThetaCurveModuliData"] .partialImplementation
      "The prime, number-field tower, degree, square-root data, absolute separable closure, and its Krull-topological Galois group are typed. Every source orbicurve package uses this group definitionally, with no arbitrary profinite replacement or equality certificate; construction of the remaining source identifications is incomplete.",
    clause "I.3.1(b).curve" .iutI "IUT I, Definition 3.1(b): once-punctured elliptic curve"
      ["PuncturedEllipticCurve", "PuncturedEllipticCurve.Torsion23Rational",
        "PuncturedEllipticSchemeRealization",
        "PuncturedEllipticSchemeRealization.puncturedScheme",
        "PuncturedEllipticSchemeRealization.openImmersion",
        "PuncturedEllipticInversionRealization",
        "schemeRepresentableEtalePseudofunctor",
        "SchemeEtaleStackPresentation"] .partialImplementation
      "The curve and puncture are tied to a scheme, origin section, complementary open, and a bicategorical equivalence with its representable Yoneda-style etale pseudofunctor; pullback, identity, and composition coherence are therefore intrinsic. An actual involutive scheme map acts by elliptic negation on rational points, and the stack sign action is identified with it. Constructing this presentation from the projective Weierstrass model remains open.",
    clause "I.3.1(b).reduction" .iutI "IUT I, Definition 3.1(b): stable reduction"
      ["PuncturedEllipticCurve.HasStableReductionAt",
        "PuncturedEllipticCurve.HasMultiplicativeReductionAt",
        "SourceInitialThetaCore"] .partialImplementation
      "Stable reduction is expressed by good-or-multiplicative reduction over completed local fields, and multiplicative reduction is required at every F-place above the bad moduli locus, not only at a selected K-lift; construction of witnesses for the chosen curve remains a source obligation.",
    clause "I.3.1(b).quotient" .iutI "IUT I, Definition 3.1(b): quotient orbicurve"
      ["OrbicurveSignAction", "SignQuotientOrbicurveData",
        "OrbicurveSignInvariantMorphism",
        "OrbicurveSignQuotientWitness",
        "HyperbolicOrbicurve.Hom.TwoIso",
        "OrbicurveSquare.TwoPullbackWitness"] .partialImplementation
      "The source path has etale stacks, a geometric-negation-compatible coherent C2-action, coherent invariant maps, and the full bicategorical quotient property via factorization and full faithfulness on 2-cells, together with exact fundamental groups over the canonical absolute Galois group, compatible open immersions, and a full two-pullback witness; constructing the quotient stack remains open.",
    clause "I.3.1(b).moduli" .iutI "IUT I, Definition 3.1(b): field of moduli and bad places"
      ["EllipticFieldOfModuliData",
        "EllipticFieldOfModuliData.jAutomorphismStabilizerInFbar",
        "EllipticFieldOfModuliData.automorphismFixedModuliFieldInFbar",
        "EllipticFieldOfModuliData.moduliEmbeddingInFbar_fieldRange_eq_jModuliFieldInFbar",
        "EllipticFieldOfModuliData.fixes_jModuliInFbar_iff_variableChange",
        "EllipticFieldOfModuliData.fsol",
        "maximalSolvableExtension", "ThetaValuationData", "SourceInitialThetaCore"]
      .partialImplementation
      "Inside the selected Fbar, the embedded j-generated moduli field is proved equal to the fixed field of its geometric-j automorphism stabilizer, fixing j is proved equivalent to an actual Weierstrass change of variables with the conjugate curve, and Fsol is the compositum there of all finite solvable Galois layers over Fmod. Transporting this comparison to the punctured scheme/stack and deriving the bad locus remain open.",
    clause "I.3.1(c).torsion" .iutI "IUT I, Definition 3.1(c): mod-l representation and kernel field"
      ["ThetaLTorsionRepresentationData",
        "PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv",
        "PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquivHom",
        "PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation",
        "PuncturedEllipticCurve.galoisActionOnPoint_stabilizer_isOpen",
        "PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_ker_isOpen",
        "PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_continuous",
        "PuncturedEllipticCurve.galoisLTorsionKernelField",
        "PuncturedEllipticCurve.galoisLTorsionKernelField_fixingSubgroup",
        "PuncturedEllipticCurve.galoisLTorsionKernelField_finiteDimensional",
        "PuncturedEllipticCurve.galoisLTorsionKernelField_isGalois",
        "PuncturedEllipticCurve.galoisLTorsionKernelField_numberField",
        "ThetaLTorsionRepresentationData.representation_continuous",
        "ThetaLTorsionRepresentationData.representation_acts_on_torsion",
        "ThetaLTorsionRepresentationData.embeddedK_eq_kernelFixedField",
        "ThetaLTorsionRepresentationData.isKernelField",
        "ThetaLTorsionRepresentationData.kernelFixedField",
        "ThetaLTorsionRepresentationData.embeddedK",
        "ThetaFieldTower"] .partialImplementation
      "The Galois action on algebraic-closure points is proved multiplicative, restricted to actual elliptic l-torsion, promoted to ZMod-l linear equivalences, and transported through the chosen basis to a derived GL2 representation. Point stabilizers are reduced to Krull-open affine-coordinate stabilizers; the representation kernel is their finite intersection, so continuity is proved. K is the literal fixed field of this open normal kernel and is proved finite Galois and a number field. An externally named K must be algebra-equivalent to that field, from which its embedding and kernel-field equality are derived; independent kernel-field proof fields have been removed. Existence of the chosen torsion basis remains the source obligation not supplied by mathlib's current elliptic-curve API.",
    clause "I.3.1(c).residue" .iutI "IUT I, Definition 3.1(c): residue characteristics and q-orders"
      ["ThetaValuationData", "ThetaTateParameterData",
        "ThetaTateParameterData.order",
        "ThetaTateParameterData.order_pos"] .partialImplementation
      "Residue characteristics are derived from residue fields; q-parameters and prime-to-l orders are required at every F-place above the bad moduli locus as well as selected K-localizations. Each order is derived from a nonzero contracting Tate parameter and its Galois-equivariant group-level uniformization. Analytic/topological realization remains open.",
    clause "I.3.1(d)" .iutI "IUT I, Definition 3.1(d)"
      ["PuncturedEllipticCurve.baseChangeOrigin",
        "PuncturedEllipticCurveScalarExtension.result",
        "OrbicurveScalarExtension",
        "SignQuotientOrbicurveScalarExtension",
        "SignQuotientOrbicurveScalarExtension.result",
        "SourceThetaKCoreData",
        "SourceThetaKCoreData.orbicurves",
        "OrbicurveMorphismScalarExtension",
        "EtaleTheta.ArithmeticEllipticQuotientData",
        "GlobalLTorsionCoverInput", "TypeOneLTorsionStackRealization",
        "ThetaRootStackRealization",
        "SourceInitialThetaCore"] .partialImplementation
      "The punctured K-curve is definitionally the actual Weierstrass base change of X_F, with the origin preserved rather than an arbitrary target supplied. The K-core sign quotient is constructed from the scalar-extension objects: its X-stack, C-stack, and quotient map are definitionally the two extended stacks and extended morphism, so no separately assembled target pair or comparison equalities are accepted. The remaining sign action, quotient universal property, and fundamental groups are explicit geometric realization obligations. Distinct class-two theta and rank-two elliptic arithmetic quotients are then attached; the Lagrangian lives on the latter. The morphism comparison is an invertible modification pinned componentwise and on naturality cells. Both l-torsion and global theta-root X/C stack interfaces carry coherent quotient and two-pullback universal properties, derived arithmetic groups, and the X-to-C-to-base open fundamental-group chain. Their finite-etale construction remains open.",
    clause "I.3.1(e).places" .iutI "IUT I, Definition 3.1(e): sections of places and local base change"
      ["ThetaPlace", "ThetaPlace.comap", "ThetaValuationData",
        "ThetaValuationData.selectedPlaceEquiv",
        "ThetaValuationData.selectedPlaces_eq_vnon_union_varc",
        "ThetaValuationData.vnon_eq_vbad_union_vgood",
        "ThetaValuationData.vnon_disjoint_varc",
        "ThetaValuationData.vbad_disjoint_vgood",
        "SourceThetaFiniteLocalCoreData",
        "SourceThetaInfiniteLocalCoreData",
        "SourceThetaFiniteLocalCoreData.orbicurves",
        "SourceThetaInfiniteLocalCoreData.orbicurves",
        "SignQuotientOrbicurveBaseChange",
        "TypeOneLTorsionStackScalarExtension",
        "TypeOneCuspidalAtlasScalarExtension",
        "SourceThetaFiniteLTorsionCoverScalarExtension",
        "SourceThetaInfiniteLTorsionCoverScalarExtension",
        "ArrowedCuspidalEigenspaceScalarExtension",
        "ArrowedJQuotientScalarExtension",
        "ArrowedTypeOneStackScalarExtension",
        "AbsoluteGaloisPlaceStabilizerData",
        "ProfiniteDecompositionGroupData",
        "ProfiniteDecompositionGroupData.embedding_range",
        "SourceThetaFiniteLocalCoreData.xDiagram_galois_range_eq_placeStabilizer",
        "SourceThetaInfiniteLocalCoreData.xDiagram_galois_range_eq_placeStabilizer",
        "ProfiniteFundamentalExactSequenceEmbedding",
        "SourceThetaBadLocalStandardData",
        "SourceThetaBadLocalThetaRootStackRealization"] .partialImplementation
      "The projections on finite and infinite places are canonical restrictions along Fmod -> K, and only their section is chosen. These typed sections assemble into one section on all places; its inverse is restriction, yielding the actual equivalence Vmod ≃ V. The source partitions V = Vnon ∪ Varc and Vnon = Vbad ∪ Vgood are proved exact and disjoint. Every local punctured curve is definitionally the Weierstrass base change to the corresponding completion, not an independently supplied target. At every finite and infinite place, the local X-stack, C-stack, and quotient map are constructed from one sign-quotient scalar-extension package; separate local targets and three comparison certificates have been removed. Local core diagrams exist at every K-place; each decomposition subgroup is the literal stabilizer of a prolongation to the absolute separable closure inside the canonical absolute Galois group. Its local embedding is derived from the local-Galois equivalence, and its image is proved equal to that stabilizer for both X and C; no ambient-group isomorphism, arbitrary subgroup, or subgroup-equality certificate remains. Selected places additionally carry the l-torsion cover, complete cusp atlas, and local epsilon. Good and bad specializations have the source-prescribed arrowed and theta-root data. Finite-etale construction remains open.",
    clause "I.3.1(e).groups" .iutI "IUT I, Definition 3.1(e): theta roots and open subgroups"
      ["ProfiniteOpenEmbedding", "EtaleTheta.ThetaRootSplittingData",
        "EtaleTheta.ThetaRootSplittingData.thetaRootSubgroup",
        "SourceThetaBadLocalStandardData.thetaRootProfiniteGroup",
        "SourceThetaBadLocalStandardData.thetaRootInclusion",
        "SourceThetaBadLocalThetaRootStackRealization"] .partialImplementation
      "The theta-root subgroup is derived as the preimage of a Galois splitting and proved open; its profinite inclusion and the two local fundamental-group inclusions form the required open-subgroup chain. The local stacks have coherent sign-quotient and full two-pullback witnesses. Their construction and finite-etale representability from the source hypotheses remain open.",
    clause "I.3.1(f)" .iutI "IUT I, Definition 3.1(f)"
      ["EtaleTheta.NonzeroLabel", "EtaleTheta.SignLabel",
        "EtaleTheta.canonicalTateSignLabel",
        "OrbicurveCuspidalDecompositionData",
        "TypeOneCuspidalAtlas",
        "TypeOneNonzeroCusp",
        "TypeOneNonzeroCusp.doubledOrigin",
        "TypeOneNonzeroCusp.discardedInertiaSubgroup",
        "TypeOneNonzeroCusp.ArrowedDelta",
        "ArrowedCuspidalEigenspaceData",
        "ArrowedPositiveProfiniteRealization",
        "ArrowedJQuotientData",
        "ArrowedJQuotientData.doubledCuspSectionImage_normal",
        "ArrowedTypeOneStackRealization",
        "TypeOneNonzeroCuspScalarExtension",
        "TypeOneCuspidalAtlasScalarExtension",
        "TypeOneCuspidalAtlasScalarExtension.toNonzeroCuspScalarExtension",
        "TypeOneNonzeroCuspScalarExtension.signLabel_eq",
        "SourceInitialThetaCore.finiteLocalEpsilon",
        "SourceInitialThetaCore.infiniteLocalEpsilon",
        "SourceInitialThetaCore.globalEpsilon_canonicalAtBad"]
      .partialImplementation
      "The full Q-indexed X-cusp and sign-orbit C-cusp atlas is represented by rational inertia/decomposition exact sequences, with sheet conjugacy and inversion action. At every selected finite and infinite place, local epsilon is constructed as the cusp at the global Q-label in the localized complete atlas; its X/C decomposition diagrams and sign-label equality are derived, so no separate local cusp, atlas equality, or sheet-representative synchronization is accepted. The Definition 1.1 dependency is explicit: discard all nonselected inertia, form Delta-dagger and its plus/minus splitting, derive 2-epsilon and prove it differs from both selected sheets, construct continuous J_X/J_C exact quotients, pin the section to the doubled-cusp decomposition group, prove its image normal, and define the arrowed stacks by the preimages of Im(sigma) and Im(sigma) x Gal(X/C). Complete atlases localize at all selected places and arrowed covers at good finite places. Finite-etale/compactified construction of these stack and boundary realizations from the source curve remains open; thus this clause is not yet source-faithful.",
    clause "I.3.4.2" .iutI "IUT I, Remark 3.4.2"
      ["SourceAutHolomorphicRigidity.Automorphism",
        "SourceAutHolomorphicRigidity.Automorphism.exists_integer_exponent",
        "SourceAutHolomorphicRigidity.Automorphism.exponent_eq_one_or_neg_one",
        "SourceAutHolomorphicRigidity.Automorphism.toAutHolomorphic_eq_identity_of_preservesClosedUnitSubmonoid"]
      .partialImplementation
      "A holomorphic automorphism of the actual complex Lie group C-times is represented by a continuous multiplicative equivalence with holomorphic forward and inverse maps. Pullback along exp, a derived differential equation, period-lattice integrality, and the inverse automorphism prove that it is z maps to z or z maps to z inverse; preservation of the norm-at-most-one submonoid rules out inversion. The resulting element of Aut_hol(C-times) is proved equal to the identity. The converse reconstruction of the Kummer structure from the Aut-holomorphic structure and co-holomorphicization remains open.",
    clause "I.3.6(a)" .iutI "IUT I, Definition 3.6(a)"
      ["ToyThetaFrobenioidObject", "ToyIUTIHodgeTheaterRealization",
        "PreFrobenioid", "IUTINonarchimedeanLocalModel",
        "SourceThetaHodgeTheater"] .partialImplementation
      "The former natural-number degree path is explicitly isolated as a toy. The source path indexes packaged Frobenioids and the five derived local categories by actual selected finite places and ties the local arithmetic group to the source orbicurve. The cited local models and category-theoretic reconstruction are not yet constructed.",
    clause "I.3.6(b)" .iutI "IUT I, Definition 3.6(b)"
      ["ToyThetaFrobenioidObject", "ToyIUTIHodgeTheaterRealization",
        "AutHolomorphicOrbispacePresentation",
        "IUTIArchimedeanLocalModel",
        "SourceThetaHodgeTheater"] .partialImplementation
      "The source interface has an actual autoequivalence action and a continuous injective Kummer homomorphism at each selected infinite place. The Absolute Anabelian Topics III reconstruction and the canonical archimedean models are not yet constructed.",
    clause "I.3.6(c)" .iutI "IUT I, Definition 3.6(c)"
      ["ToyThetaFrobenioidObject", "ToyIUTIHodgeTheaterRealization",
        "IUTIGlobalFrobenioidModel",
        "IUTIThetaHodgeTheaterModels",
        "SourceThetaHodgeTheater"] .partialImplementation
      "The source interface includes a packaged global Frobenioid, a prime-to-selected-place equivalence, local topological monoids and rho isomorphisms, derived theta/D global presentations, and compatibility for equivalent theater copies. The global model, category-derived primes, and reconstruction theorem remain open.",
    clause "I.3.7(i)" .iutI "IUT I, Corollary 3.7(i)"
      ["ThetaZeroToOneLink", "SourceThetaLinkCore",
        "SourceThetaLinkCore.ofTheaters",
        "FullPolyIsomorphism",
        "SourceThetaLinkCore.globalFullPolyIsomorphism_nonempty"]
      .partialImplementation
      "The typed legacy reindexing remains a toy. For source theaters over common models, the global theta-to-moduli Frobenioid equivalence is constructed by composing the theater/model and canonical moduli/theta equivalences. The full poly-isomorphism is the quotient of all categorical equivalences by natural isomorphism and is proved nonempty. Packaging the additional collection compatibilities into the same quotient remains open.",
    clause "I.3.7(ii)" .iutI "IUT I, Corollary 3.7(ii)"
      ["SourceThetaLinkCore",
        "SourceThetaLinkCore.ofTheaters"] .partialImplementation
      "The local nonarchimedean D-tilde equivalences are transported through the common source models. The complete poly-isomorphism and archimedean mono-analytic compatibility remain open.",
    clause "I.3.7(iii)" .iutI "IUT I, Corollary 3.7(iii)"
      ["SourceThetaLinkCore",
        "SourceThetaLinkCore.ofTheaters",
        "TopologicalMonoidIso"] .partialImplementation
      "At every selected finite and infinite place, the composite O-times transport is an actual topological-monoid isomorphism from the source tilde units through the source theta units and common model to the target tilde units. Integrating these maps with the full poly-isomorphism and its D-tilde comparison remains open.",
    clause "I.4.1" .iutI "IUT I, Definition 4.1"
      ["ThetaPrimeStrip", "SourceDPrimeStrip",
        "SourceDPrimeStripHom",
        "SourceDMonoAnalyticPrimeStrip",
        "SourceDMonoAnalyticPrimeStripHom",
        "SourceDMonoAnalyticization",
        "AutHolomorphicOrbispaceHom",
        "AutHolomorphicOrbispaceIso"] .partialImplementation
      "The empty legacy prime-strip remains a toy. The source path now has holomorphic and mono-analytic local objects, actual label classes, categories of placewise morphisms, and a natural mono-analyticization interface with fully faithful finite inclusions and naturality squares. Constructing this functor from the paper's subcategories and archimedean reconstruction, as well as the global D-categories, remains open.",
    clause "I.4.10" .iutI "IUT I, Definition 4.10 and Section 0 capsule conventions"
      ["CategoryCapsule", "CategoryCapsule.Hom",
        "CategoryCapsule.FullPolyMorphism",
        "CategoryCapsule.FullPolyMorphism.Members",
        "CategoryCapsule.FullPolyMorphism.IsPolyIsomorphism",
        "CategoryCapsule.FullMemberMorphism",
        "CategoryProcession", "CategoryProcession.transition",
        "CategoryProcession.Hom", "CategoryProcessionObject",
        "CategoryProcession.MemberHom",
        "CategoryProcessionMemberObject"]
      .sourceFaithful
      "The generic definition is complete: capsules retain finite index types; a full poly-morphism separates its fixed index injection from the collection of componentwise isomorphism members; and the member-carrying capsule and procession categories retain an actual chosen member when an ordinary categorical arrow is required. A positive n-procession has j-capsules of exact cardinality j. Proposition 4.11's source-specific l-star procession functors are tracked separately.",
    clause "I.4.6(ii)" .iutI "IUT I, Definition 4.6(ii)"
      ["SourceDThetaBridgeCore",
        "SourceDThetaBridgeCore.IsomorphismMember",
        "SourceDThetaBridgeCore.IsomorphismMember.id",
        "SourceDThetaBridgeCore.IsomorphismMember.comp",
        "SourceDPrimeStripHom"] .partialImplementation
      "The bridge core has a finite capsule of actual D-prime strips, a D-prime-strip target, and nonempty poly-morphism sets of genuine placewise arrows. Isomorphism members carry component and target isomorphisms, preserve evaluation labels, conjugate poly-arrow membership, and have identity and composition. The required conjugacy to the model D-theta bridge and passage from members to the paper's full-poly bridge category remain open.",
    clause "I.4.7(i)" .iutI "IUT I, Proposition 4.7(i)"
      ["SourceDThetaBridgeCore.evaluationLabelEquiv",
        "IUTIPositiveLabel.signLabelEquiv",
        "SourceDThetaBridgeCore.orderedIndexEquiv"]
      .partialImplementation
      "Positive representatives 1 through l-star are proved equivalent to the actual nonzero Tate labels modulo sign, and a bijective evaluation-label map yields the paper's ordered capsule-index equivalence. Deriving that map and its bijectivity from the bad-place evaluation sections of a model D-theta bridge remains open.",
    clause "I.4.11(i-ii)" .iutI "IUT I, Proposition 4.11(i)-(ii)"
      ["CategoryCapsule.nestedProcession",
        "CategoryCapsule.nestedTransitionMember",
        "CategoryCapsule.nested_label_indeterminacy",
        "SourceDThetaBridgeCore.procession",
        "SourceDThetaBridgeCore.procession_capsule_card",
        "SourceDThetaBridgeCore.procession_label_indeterminacy",
        "SourceDThetaBridgeCore.monoAnalyticProcession",
        "SourceDThetaBridgeCore.monoAnalyticTransitionMember",
        "SourceDThetaBridgeCore.monoAnalyticProcession_label_indeterminacy",
        "SourceDThetaBridgeCore.IsomorphismMember.processionHom",
        "SourceDThetaBridgeCore.IsomorphismMember.processionHomMember",
        "SourceDThetaBridgeCore.IsomorphismMember.monoAnalyticProcessionHom",
        "SourceDThetaBridgeCore.IsomorphismMember.monoAnalyticProcessionHomMember"]
      .partialImplementation
      "The label bijection derives the nested holomorphic l-star procession; every adjacent full-poly arrow has its canonical identity member, every j-capsule has cardinality j, and the reduced indeterminacy is l-star factorial. Applying a natural mono-analyticization functor derives the mono-analytic procession and preserves these proofs. Compatible bridge-isomorphism members induce procession morphisms with actual full-poly members in both settings. Constructing mono-analyticization from the source and upgrading memberwise naturality to the paper's full bridge category remain open.",
    clause "I.5.2(i)" .iutI "IUT I, Definition 5.2(i)"
      ["SourceFPrimeStrip", "SourceFPrimeStripArchHom",
        "SourceFPrimeStripHom"] .partialImplementation
      "A holomorphic F-prime-strip carries packaged finite Frobenioids and the complete archimedean category/Aut-holomorphic-orbispace/Kummer collection. Its component arrows are actual categorical or topological isomorphisms and preserve the Kummer square. Constructing the local Examples 3.2-3.4 models from initial theta data remains open.",
    clause "I.5.2(ii)" .iutI "IUT I, Definition 5.2(ii)"
      ["PreFrobenioid.CharacteristicSplitting",
        "SplitFrobenioidPresentation",
        "SplitTopologicalMonoidPresentation",
        "ArchimedeanSplitFrobenioidPresentation",
        "SourceFMonoAnalyticPrimeStrip",
        "SourceThetaHodgeTheater.MonoAnalyticTransport",
        "SourceThetaHodgeTheater.associatedFMonoAnalytic"] .partialImplementation
      "Finite components are actual split Frobenioids, and archimedean components are Frobenioid/TM-tilde/selected-splitting triples whose characteristic submonoid is identified with the noncompact factor. Every component is tied to the canonical model by a structure-preserving equivalence. A theta-Hodge theater now yields its associated mono-analytic F-prime-strip only after explicit Corollaries 4.5/4.6 transport of the rational monoids, characteristic splittings, and selected archimedean splitting has been supplied; bare carrier-category equivalences cannot discharge this boundary. Constructing that transport and mono-analyticization from the paper remains open.",
    clause "I.5.2(iii)" .iutI "IUT I, Definition 5.2(iii)"
      ["SourceFPrimeStripHom", "SourceFPrimeStripCapsule",
        "CategoryCapsule", "CategoryCapsule.FullPolyMorphism"]
      .partialImplementation
      "Holomorphic F-prime-strips form a category in which every constituent map is an isomorphism, so finite capsules and ordinary/full-poly morphisms are genuine. The corresponding category and capsules for mono-analytic F-prime-strips still require composition of complete archimedean triple equivalences.",
    clause "I.5.2(iv)" .iutI "IUT I, Definition 5.2(iv)"
      ["IUTIGlobalFrobenioidModel",
        "SourceFGloballyRealifiedMonoAnalyticPrimeStrip"]
      .partialImplementation
      "The source object has a packaged global Frobenioid, a prime-to-place equivalence, an actual mono-analytic F-prime-strip, local characteristic and realified topological monoids, rho isomorphisms, and componentwise compatibility with the Example 3.5 model. Its isomorphism category and capsules, derivation of local realifications from divisor monoids, and the construction algorithm remain open.",
    clause "I.5.2(v)" .iutI "IUT I, Definition 5.2(v)"
      ["SourceTopologicalPseudoMonoid",
        "SourceTopologicalGroupPseudoMonoidActionPair"] .unformalized
      "The exact Section 0 pseudo-monoid and continuous action-pair targets are available, but the group-theoretic reconstruction of the ambient profinite group, rational fundamental group, ind-topological monoid, and kappa/infinity-kappa/infinity-kappa-times coric pseudo-monoids is absent.",
    clause "I.5.2(vi)" .iutI "IUT I, Definition 5.2(vi)"
      ["SourceTopologicalPseudoMonoid.IsCyclotomic"] .unformalized
      "The exact cyclotomic pseudo-monoid predicate is available, but the nonarchimedean infinity-kappa coric structures, cyclotomic comparison, uniqueness, critical-point restriction criterion, and field reconstruction algorithms are absent.",
    clause "I.5.2(vii)" .iutI "IUT I, Definition 5.2(vii)"
      [] .unformalized
      "The archimedean rational covering system and algorithmic meromorphic-function pseudomonoids are absent.",
    clause "I.5.2(viii)" .iutI "IUT I, Definition 5.2(viii)"
      [] .unformalized
      "The archimedean coric structures, Kummer cyclotomic reconstruction, critical-point splittings, and field reconstruction algorithms are absent.",
    clause "I.5.5(i)" .iutI "IUT I, Definition 5.5(i)"
      [] .unformalized
      "The NF-bridge's global Frobenioids, restriction equivalence, local-to-global poly-morphism, and associated D-NF-bridge are absent.",
    clause "I.5.5(ii)" .iutI "IUT I, Definition 5.5(ii)"
      ["SourceThetaHodgeTheater.associatedF",
        "SourceFThetaBridge",
        "SourceFThetaBridge.associatedD",
        "SourceFThetaBridge.associatedD_lift_unique",
        "SourceFThetaBridge.procession"]
      .partialImplementation
      "The target F-prime-strip is derived from the actual theta-Hodge theater, selected F-poly-arrows map functorially to an associated D-theta bridge, and uniqueness of selected F-lifts is explicit. Conjugacy to the model theta bridge and the full isomorphism category of F-theta bridges remain open.",
    clause "I.5.5(iii)" .iutI "IUT I, Definition 5.5(iii)"
      [] .unformalized
      "The theta-NF Hodge theater cannot be assembled until the NF-bridge and common-capsule gluing compatibility are formalized.",
    clause "I.6.4(i-iii)" .iutI "IUT I, Definition 6.4(i)-(iii)"
      ["PrimeGeFive.lPlusMinus",
        "IUTIIAbsoluteThetaLabel.orderedIndexEquiv",
        "SourceDAbsoluteThetaBridgeCore",
        "SourceFAbsoluteThetaBridge",
        "SourceFAbsoluteThetaBridge.associatedD",
        "ThetaPlusMinusEllHodgeTheater",
        "ThetaHodgeTheaterGluing"] .partialImplementation
      "The D-Theta-plus-minus bridge now has the complete absolute-label set, including zero, and an exact l-plus-minus ordering; its F-prime-strip lift and selected arrows are genuine. The Definition 6.4(ii) D-Theta-ell bridge, the common-capsule gluing of (iii), conjugacy to the model bridges, and their full isomorphism categories remain open. The older typed ThetaPlusMinusEllHodgeTheater is only incidence data and does not discharge those source clauses.",
    clause "I.6.9(i-iii)" .iutI "IUT I, Proposition 6.9(i)-(iii)"
      ["SourceDAbsoluteThetaBridgeCore.procession",
        "SourceDAbsoluteThetaBridgeCore.procession_capsule_card",
        "SourceDAbsoluteThetaBridgeCore.monoAnalyticProcession",
        "SourceDAbsoluteThetaBridgeCore.monoAnalyticProcession_capsule_card",
        "SourceDAbsoluteThetaBridgeCore.IsomorphismMember.processionHom",
        "SourceDAbsoluteThetaBridgeCore.IsomorphismMember.processionHomMember",
        "CategoryProcession.MemberHom",
        "CategoryProcessionMemberObject"]
      .partialImplementation
      "The nested procession has the correct l-plus-minus length and its j-th capsule has exactly j+1 members, including zero. Mono-analyticization and compatible bridge members yield actual procession maps with component isomorphisms, and the member category composes these maps without erasing the chosen strip isomorphisms. Packaging Definition 6.4 bridges into the complete additive functor and proving all naturality and poly-isomorphism assertions remain open.",
    clause "I.6.7" .iutI "IUT I, Proposition 6.7"
      ["ThetaHodgeTheater", "ThetaZeroToOneLink"] .unformalized
      "The stated mono-analytic and theta-link compatibility is not proved.",
    clause "I.6.12.2" .iutI "IUT I, Remark 6.12.2"
      ["ThetaHodgeTheaterHistory", "ThetaHodgeGluing"] .toyModel
      "Finite histories with reflexive gluing do not realize the paper's procession/gluing construction.",
    clause "I.6.13(i)" .iutI "IUT I, Definition 6.13(i)"
      ["ThetaHodgeTheater"] .partialImplementation
      "The theater is typed, but its constituent prime strips, Frobenioids, links, and symmetries are not source-faithful.",
    clause "I.6.13(ii)" .iutI "IUT I, Definition 6.13(ii)"
      ["ThetaHodgeGluing"] .toyModel
      "Identity equivalences do not construct the gluing data of a collection of Hodge theaters.",

    clause "AbsTopIII.1.5(a-b),Rmk1.5.4(i)" .absoluteAnabelianIII
      "Absolute Anabelian Topics III, Definition 1.5 and Remark 1.5.4(i)"
      ["SourceKummerFaithfulness.eq_one_of_roots_of_residuallyFinite",
        "SourceKummerFaithfulness.residuallyFinite_of_profinite",
        "SourceKummerFaithfulness.eq_one_of_roots_in_profinite"]
      .partialImplementation
      "The finite-quotient argument is proved: a residually finite, hence profinite, multiplicative group has no nontrivial element admitting roots of every positive degree, exactly the condition of Definition 1.5(a). Applying this theorem to the unit groups of every finite MLF extension and identifying the resulting condition with the constructed continuous Kummer classes remain open.",

    clause "AbsTopIII.2.1(i-ii),Cor2.3" .absoluteAnabelianIII
      "Absolute Anabelian Topics III, Definition 2.1(i)-(ii) and Corollary 2.3"
      ["SourceAutHolomorphic.ConnectedOpen",
        "SourceAutHolomorphic.HasAmbientHolomorphicLift",
        "SourceAutHolomorphic.HasAmbientHolomorphicLift.comp",
        "SourceAutHolomorphic.autHolomorphicSubgroup",
        "SourceAutHolomorphic.AutHolomorphic.RestrictionDomain",
        "SourceAutHolomorphic.AutHolomorphic.restrict",
        "SourceAutHolomorphic.AutHolomorphic.restrict_mul",
        "SourceAutHolomorphic.AutHolomorphic.restrict_inv"]
      .partialImplementation
      "For every connected open subset U of the complex plane, Lean derives the actual group Aut_hol(U) from homeomorphisms admitting ambient holomorphic lifts in both directions. Identity, composition, inversion, and restriction of automorphisms preserving a connected open subdomain are proved. The general Riemann-surface assignment, local RC-holomorphic morphisms, the two co-holomorphicizations, and Corollary 2.3's classification and unique-extension theorem remain open.",

    clause "AbsTopIII.3.1(i-iii,v)" .absoluteAnabelianIII
      "Absolute Anabelian Topics III, Definition 3.1(i)-(iii),(v)"
      ["SourceTopologicalGroupMonoidActionPair",
        "SourceTorsionCyclotomicCommMonoid",
        "SourceTorsionCyclotomicTopologicalCommMonoid",
        "SourceMonoidCyclotome",
        "SourceTorsionCyclotomicCommMonoid.rootsOfUnity_finite",
        "SourceMonoidCyclotome.topology",
        "SourceMonoidCyclotome.boundedCoe_isClosedEmbedding",
        "SourceMonoidCyclotome.asProfinite",
        "SourceMonoidCyclotome.eq_one_of_roots",
        "SourceMLFAlgebraicIntegerRing",
        "SourceMLFIntegralMonoid",
        "SourceMLFAbsoluteGaloisGroup",
        "SourceMLFIntegralMonoid.galoisAction",
        "SourceMLFModelTMStructure",
        "SourceMLFModelTMPair",
        "SourceMLFModelTMPair.augmentation_surjective",
        "SourceMLFGaloisTMPairData",
        "SourceMLFGaloisTMPairData.cyclotomeAction",
        "SourceMLFGaloisTMPairData.toActionPair",
        "SourceMLFGaloisTMPair",
        "SourceMLFGaloisTMPair.augmentation",
        "SourceMLFGaloisTMPair.augmentation_surjective",
        "SourceIUTIIUnitKummerEmbedding"]
      .partialImplementation
      "The model carrier is literally the nonzero elements of the integral closure of O_k in an algebraic closure, its absolute Galois group has the Krull topology, and its algebraic Galois action is constructed. A model pair has an actual continuous surjective augmentation Pi_k -> G_k; every general pair is required to be equivariantly isomorphic to such a model, and its augmentation is transported and proved surjective. The exact TM object uses the topology-free algebraic presentation authorized by Remark 3.1.1, so no arbitrary topology can certify the model. The cyclotome is literally Hom(Q/Z,M). Its pointwise topology is realized as a closed subspace of the product of the finite root-of-unity coordinate groups derived from the Q/Z torsion certificate; hence its compact, Hausdorff, totally disconnected, and bundled Profinite structures are proved. The Q/Z torsion identification remains a precise model certificate; the categories and morphisms of Definition 3.1(iii) remain open.",
    clause "AbsTopIII.3.2(ii)" .absoluteAnabelianIII
      "Absolute Anabelian Topics III, Proposition 3.2(ii)"
      ["ContinuousH1.toGerm",
        "SourceMLFIntegralMonoid.algebraicClosure_isFractionRing",
        "SourceMLFIntegralMonoid.groupificationEquivAlgebraicClosureUnits",
        "SourceMLFIntegralMonoid.torsionUnit",
        "SourceMLFIntegralMonoid.torsionUnit_image",
        "SourceMLFIntegralMonoid.groupificationRootableByNat",
        "SourceMLFGaloisTMPair.fixedSubmonoid",
        "SourceMLFIntegralMonoid.absoluteOpenStabilizer",
        "SourceMLFGaloisTMPair.openStabilizer",
        "SourceMLFGaloisTMPair.openStabilizer_fixed",
        "SourceMLFGaloisTMPair.continuousCyclotomeAction",
        "SourceMLFGaloisTMPair.rootableRationalPowers",
        "SourceMLFGaloisTMPair.groupificationRootableByNat",
        "SourceMLFGaloisTMPair.CompatibleRootSystem",
        "SourceMLFGaloisTMPair.CompatibleRootSystem.ofModel",
        "SourceMLFGaloisTMPair.CompatibleRootSystem.quotient_pow_den",
        "SourceMLFGaloisTMPair.CompatibleRootSystem.galoisTranslate",
        "SourceMLFGaloisTMPair.CompatibleRootSystem.quotientUnit_exists",
        "SourceMLFGaloisTMPair.KummerRootRealization",
        "SourceMLFGaloisTMPair.KummerRootRealization.ofRootSystem",
        "SourceMLFGaloisTMPair.KummerRootRealization.ratioCyclotome",
        "SourceMLFGaloisTMPair.KummerRootRealization.ratioUnit_isLocallyConstant",
        "SourceMLFGaloisTMPair.KummerRootRealization.ratioCyclotome_continuous",
        "SourceMLFGaloisTMPair.ContinuousKummerRootRealization",
        "SourceMLFGaloisTMPair.ContinuousKummerRootRealization.cocycle",
        "SourceMLFGaloisTMPair.CompatibleRootComparison",
        "SourceMLFGaloisTMPair.CompatibleRootComparison.comparisonUnit_exists",
        "SourceMLFGaloisTMPair.CompatibleRootComparison.ofModel",
        "SourceMLFGaloisTMPair.CompatibleRootComparison.germ_eq",
        "SourceMLFGaloisTMPair.CompatibleRootComparison.localClass_eq",
        "SourceMLFGaloisTMPair.ContinuousModelKummerRootChoice",
        "SourceMLFGaloisTMPair.KummerRootTheory",
        "SourceMLFGaloisTMPair.KummerRootTheory.ofContinuousEquiv",
        "SourceMLFGaloisTMPair.KummerRootTheory.chosen_rootSystem",
        "SourceMLFGaloisTMPair.KummerRootTheory.kummerMap",
        "SourceMLFGaloisTMPair.KummerRootTheory.canonicalKummerMap",
        "SourceMLFGaloisTMPair.ContinuousLocalModelKummerRootRealization",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.ofContinuousEquiv",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.chosen_rootSystem",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.kummerMap",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.local_toGerm_eq_global",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.canonicalKummerMap",
        "SourceMLFGaloisTMPair.LocalKummerRootTheory.canonicalKummerMap_toGerm",
        "SourceIUTIIUnitKummerEmbedding",
        "SourceIUTIIUnitKummerEmbedding.monoidKummer",
        "SourceIUTIIUnitKummerEmbedding.unitKummer",
        "SourceIUTIIUnitKummerEmbedding.constantSubgroup",
        "SourceIUTIIUnitKummerEmbedding.torsionUnitImage",
        "SourceIUTIIUnitKummerEmbedding.torsionUnitImage_eq_constant_torsion",
        "sourceConstantTorsion_unitKummer"]
      .partialImplementation
      "The fraction-field theorem identifies the groupification of the literal monoid O_kbar^triangle with kbar^x. Algebraic closedness makes it rootable, and injectivity of divisible abelian groups extends Z -> kbar^x across Z -> Q; transporting through the model isomorphism constructs a coherent compatible rational-root system for every monoid element. Two systems agree on integers, so their quotient at q has order dividing den(q); integrality of a finite-order element and its inverse constructs the actual comparison unit in O_kbar^triangle and transports it to every model pair. Applying Galois to a compatible root system and comparing it with the original constructs every integral Galois root ratio from fixedness. Root, comparison, and ratio existence are therefore no longer supplied assumptions. The Krull stabilizer of each algebraic integer is open and transports to the general pair. Root ratios are locally constant into discrete units, hence continuous in the proved profinite pointwise cyclotome topology; the canonical continuous Galois action is constructed coordinatewise. The ratios are multiplicative, killed on Z, descended through Q/Z, and satisfy the cocycle law. The constructed comparison gives the coboundary between choices. Both canonical Kummer maps are derived monoid homomorphisms and commute with the canonical local-to-germ map. Injectivity is not asserted by Proposition 3.2(ii); formalizing its separate MLF Kummer-faithfulness proof from Definition 1.5 and Remark 1.5.4 remains explicit.",
    clause "EtTh.2.13(ii)" .etaleTheta
      "Etale Theta, Definition 2.13(ii)"
      ["TopologicalGroupCat", "ContinuousAutomorphism",
        "ContinuousAutomorphism.inner_range_normal",
        "ContinuousOuterSubgroup", "SourceMonoThetaEnvironmentData",
        "SourceModelMonoThetaEnvironment",
        "SourceMonoThetaEnvironmentRealization",
        "SourceMonoThetaEnvironment"] .partialImplementation
      "The ordered topological-group triple, exact normal subgroup of inner automorphisms, full inverse image of the outer subgroup, cyclic mu_N kernel, theta-section conjugacy class, geometric generators, and explicit realization by a model environment are typed. Construction of the tempered/Kummer model and the full reduction morphism of Definition 2.13(ii) remain open.",
    clause "II.1.4" .iutII "IUT II, Proposition 1.4"
      ["SourceIUTIIThetaEvaluationOrbits",
        "SourceIUTIIInfiniteThetaRelation"] .partialImplementation
      "Theta and infinite-theta values inhabit actual continuous H1 germs and retain their root-of-unity orbits. The Etale Theta standard-type class, its l-th root, l*Z-by-mu2 orbit, and the exact some-positive-power-equals-theta-up-to-torsion definition are not yet constructed from the tempered fundamental group.",
    clause "II.1.5(i-iv)" .iutII "IUT II, Proposition 1.5(i)-(iv)"
      ["SourceMonoThetaProjectiveSystem",
        "SourceMonoThetaProjectiveSystem.inverseLimit",
        "SourceIUTIIDefinition27PartI",
        "SourceIUTIIDefinition27PartII.cyclotomicRigidity_source"]
      .partialImplementation
      "The projective system, inverse limit, exterior cyclotome kernel, and restricted cyclotomic-rigidity isomorphism are typed. Discrete rigidity, exact theta_env transport, the torsion Kummer injection of Remark 1.5.2, and compatibility with the Frobenioid Kummer construction remain open.",
    clause "II.1.12(i-ii)" .iutII "IUT II, Corollary 1.12(i)-(ii)"
      ["SourceIUTIIPointedInversion",
        "SourceIUTIIPointedInversion.decompositionGroupObject",
        "SourceIUTIIPointedInversion.decompositionInclusion",
        "SourceIUTIICorollary112PointedRestriction",
        "SourceIUTIICorollary112PointedRestriction.detects_constant_torsion",
        "SourceIUTIICorollary112PointedRestriction.toTorsionDetectingRestriction",
        "SourceIUTIICorollary112PointedRestriction.splittingUpToTorsion"]
      .partialImplementation
      "A pointed inversion is an actual continuous automorphism of outer order two relative to the geometric subgroup and preserves the geometric-conjugacy class of an actual decomposition subgroup. Restriction is induced on continuous H1; the equality M_TM^x intersect res^-1(torsion)=M_TM^mu derives torsion detection and the splitting. The group-theoretic construction of pointed inversions, proof of this equality by standard-type theta evaluation, invariant subsets, and vertical cyclotomic-rigidity diagram remain open.",
    clause "II.2.7(i)" .iutII "IUT II, Definition 2.7(i)"
      ["MonoThetaModulus", "SourceMonoThetaProjectiveSystem",
        "SourceMonoThetaProjectiveSystem.inverseLimit",
        "SourceMonoThetaProjectiveSystem.projection",
        "SourceIUTIIDefinition27PartI"] .partialImplementation
      "The environments form an actual projective functor with a certified categorical inverse limit; the natural ambient map has the exterior cyclotome as its exact kernel and the tempered subgroup as its exact image. Constructing the system from the local tempered group remains open.",
    clause "II.2.7(ii)" .iutII "IUT II, Definition 2.7(ii)"
      ["TopologicalGroupCat.subgroupInclusion",
        "SourceTopologicalSubquotient",
        "SourceTopologicalSubquotient.Carrier",
        "SourceTopologicalSubquotient.projection",
        "SourceTopologicalSubquotient.comap",
        "SourceIUTIIDefinition27PartI.inverseImage",
        "SourceIUTIIDefinition27PartI.exteriorCyclotomeRestriction",
        "SourceIUTIIDefinition27PartI.restrictAmbientSubquotient",
        "SourceIUTIIDefinition27PartII",
        "SourceIUTIIDefinition27PartII.wideInverseImage",
        "SourceIUTIIDefinition27PartII.narrowInverseImage",
        "SourceIUTIIDefinition27PartII.narrowInverseImage_le_wide",
        "SourceIUTIIDefinition27PartII.exteriorCyclotomeSubquotient",
        "SourceIUTIIDefinition27PartII.lDeltaThetaSubquotient",
        "SourceIUTIIDefinition27PartII.restrictedTemperedSubquotient",
        "SourceIUTIIDefinition27PartII.localGaloisSubquotient",
        "SourceIUTIIDefinition27PartII.cyclotomicRigidity_source"]
      .partialImplementation
      "The nested groups are actual inverse images under the Definition 2.7(i) ambient homomorphism. Pullback of a topological subquotient is implemented as f^-1(U)/f^-1(N). The exterior cyclotome is restricted from the exact kernel in part (i), while the other three narrow-level subquotients are derived by pulling back ambient subquotients; rigidity is a continuous group equivalence between the derived endpoints. Constructing the three precise ambient subquotients from Proposition 1.4 and Corollary 2.5, and proving that rigidity is the restriction of Proposition 1.5(iii), remain open.",
    clause "II.2.8(i)" .iutII "IUT II, Corollary 2.8(i)"
      ["ContinuousGroupAction", "ContinuousOneCocycle",
        "ContinuousH1", "ContinuousH1.restrict",
        "ContinuousH1.restrictMonoidHom",
        "ContinuousH1GermRepresentative",
        "ContinuousH1GermRepresentative.pullback",
        "ContinuousH1Germ", "ContinuousH1Germ.restrict",
        "ContinuousH1Germ.restrictMonoidHom",
        "EquivariantOrbitMap",
        "SourceIUTIIThetaEvaluationOrbits",
        "SourceIUTIICorollary28RestrictionStages",
        "SourceIUTIICorollary28RestrictionStages.afterSecond",
        "SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom",
        "SourceIUTIICorollary28RestrictionStages.totalRestriction_mem_afterSecond_theta_carrier",
        "SourceIUTIICorollary28RestrictionStages.totalRestriction_mem_afterSecond_infiniteTheta_carrier",
        "SourceIUTIICorollary28RestrictionStages.afterSecond_zero_representatives"]
      .partialImplementation
      "Continuous nonabelian H1 is a quotient of actual continuous cocycles, and the displayed colimit over open subgroups is an explicit germ quotient. For abelian coefficients, pointwise cocycle multiplication descends to commutative group structures on H1 and its germ colimit; both restriction operations are proved homomorphisms. Two equivariant restriction stages derive the final mu_2l/mu orbit families indexed by |F_l|, preserve identity representatives at the zero label, and prove that the composite restriction sends every ambient orbit value into its final orbit. Constructing the paper's subgroup/subquotient and decomposition-group maps, coefficient actions, and input orbits from the mono-theta environment remains open.",
    clause "II.2.8(ii)" .iutII "IUT II, Corollary 2.8(ii)"
      ["independentConjugacyMulAction",
        "EquivariantOrbitMap.onOrbitQuotients",
        "SourceIUTIIIndependentConjugacyEvaluationAlgorithm",
        "SourceIUTIIIndependentConjugacyEvaluationAlgorithm.toEquivariantOrbitMap",
        "SourceIUTIIIndependentConjugacyEvaluationAlgorithm.onIndependentConjugacyClasses"]
      .partialImplementation
      "The two independent copies of the conjugacy group act componentwise on inertia and ambient-subgroup choices. An evaluation into actual theta H1-orbit families is required to be equivariant for this product action and is proved to descend to orbit quotients. Constructing the choices and output action from Delta_v^plus/minus conjugation, constructing evaluation from the restriction stages, and proving functoriality in the mono-theta projective system remain open.",
    clause "II.2.8(iii)" .iutII "IUT II, Corollary 2.8(iii)"
      ["SourceIUTIIUnitKummerEmbedding.constantSubgroup",
        "SourceIUTIIUnitKummerEmbedding.torsionUnitImage",
        "SourceIUTIIUnitKummerEmbedding.torsionUnitImage_eq_constant_torsion",
        "sourceConstantTorsion_unitKummer",
        "sourceConstantTorsion",
        "sourceSplittingUpToTorsionMap",
        "SourceSplittingUpToTorsion",
        "SourceTorsionDetectingRestriction",
        "SourceTorsionDetectingRestriction.splittingUpToTorsion",
        "SourceIUTIIPointedInversion",
        "SourceIUTIICorollary112PointedRestriction",
        "SourceIUTIICorollary112PointedRestriction.detects_constant_torsion",
        "SourceIUTIICorollary112PointedRestriction.splittingUpToTorsion",
        "SourceIUTIIMultiplicativeFiniteOrderAction",
        "SourceIUTIIMultiplicativeFiniteOrderAction.orbitCarrier_subset_torsion",
        "SourceIUTIICorollary28RestrictionStages.afterSecond_zero_theta_carrier_subset_torsion",
        "SourceIUTIICorollary28RestrictionStages.afterSecond_zero_infiniteTheta_carrier_subset_torsion",
        "SourceIUTIICorollary28RestrictionStages.zeroThetaTorsionDetectingRestriction",
        "SourceIUTIICorollary28RestrictionStages.zeroInfiniteThetaTorsionDetectingRestriction",
        "SourceIUTIICorollary28RestrictionStages.zeroThetaSplittingUpToTorsion",
        "SourceIUTIICorollary28RestrictionStages.zeroInfiniteThetaSplittingUpToTorsion",
        "sourceZeroLabelSplittingUpToTorsion",
        "SourceIUTIICorollary28RestrictionStages.afterSecond_zero_representatives"]
      .partialImplementation
      "M_TM^x is now the range of an injective unit Kummer homomorphism, and its torsion M_TM^mu is proved exactly equal to the image of torsion units. A pointed inversion has an actual decomposition subgroup, and the exact equality M_TM^x intersect res^-1(torsion)=M_TM^mu derives the weaker detection implication and splitting. For both finite mu_2l and infinite mu orbits, the identity representative and finite-order action prove the entire final zero-label orbit is torsion; the composite H1 restriction constructs both zero-label splittings. Constructing the MLF-Galois TM-pair and Kummer embedding, proving the pointed inverse-image equality from Corollary 1.12, and identifying the two-stage composite with that pointed restriction remain open.",
    clause "II.3.5(i)" .iutII "IUT II, Corollary 3.5(i)"
      ["IUTIPositiveLabel.signLabelEquiv",
        "etaleThetaUnitActionOnSignLabel",
        "iutIISignQuotientPermHom",
        "iutIISignQuotientPermHom_transitive",
        "iutIISignQuotientAction_transitive",
        "SourceTopologicalGroupMonoidActionPair",
        "SourceTopologicalGroupMonoidActionPair.Iso",
        "SourceTopologicalGroupMonoidActionPair.Iso.castTarget",
        "SourceTopologicalGroupMonoidActionPair.Iso.symm",
        "SourceIUTIISymmetrizingIsomorphisms",
        "SourceIUTIISymmetrizingIsomorphisms.outerTransport_one",
        "SourceIUTIISymmetrizingIsomorphisms.outerTransport_mul",
        "SourceIUTIISymmetrizingIsomorphisms.fromBase",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalMonoidHom",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalMonoidHom_injective",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalRangeSubmonoid",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalRangeContinuousMulEquiv",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalRangeContinuousMulEquiv_equivariant",
        "SourceIUTIISymmetrizingIsomorphisms.between",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalUnitSubmonoid",
        "MulEquivsDifferBySingleInner",
        "singleInnerIsomorphismSetoid",
        "SourceSingleInnerIsomorphismClass",
        "SourceIUTIISynchronizedRestrictionIsomorphismClass",
        "SourceIUTIICorollary35RestrictionContext",
        "SourceIUTIICorollary35RestrictionDiagram",
        "SourceIUTIICorollary35SingleBasepointAction",
        "RestrictionDiagramsDifferBySingleInner",
        "RestrictionDiagramsDifferBySingleInner.afterBaseInclusion",
        "singleInnerRestrictionDiagramSetoid",
        "SourceIUTIISynchronizedRestrictionDiagramClass",
        "SourceIUTIICorollary35RestrictionDiagram.synchronizedClassToMonoidIsomorphismClass",
        "ToyIUTIIHodgeArakelovEvaluationData"]
      .partialImplementation
      "After the t ~ -t identification, the full nonzero absolute-label set remains indexed by the proved sign-label equivalence. Multiplication by (Z/lZ)^x descends to EtaleTheta sign labels, factors through the exact quotient by {+1,-1}, and the resulting F_l^{x+-}-style action is proved transitive. Each label owns a topological group acting continuously on a topological monoid. The supplied outer transports satisfy identity and multiplication coherence, and all base-to-label symmetrizing isomorphisms are derived. Their diagonal map has an actual range submonoid, a two-sided continuous multiplicative equivalence from the base monoid, and proved equivariance under the transported action. The full compatible diagram Pi_X <- Pi_v <- G_v^(<|F_l|>) together with its equivariant monoid isomorphism is typed. Difference by one base-group element acting simultaneously on the group map and monoid map is proved an equivalence relation, its quotient is constructed, and it maps to the monoid-only quotient. Constructing the diagram, coherent transports, restriction isomorphism, and single-basepoint action from the paper's Delta_C/Delta_X and Corollary 2.8 data remains open; the degree model is only toy.",
    clause "II.3.5(ii)" .iutII "IUT II, Corollary 3.5(ii)"
      ["sourceGaussianMonoid", "diagonalConstantUnitSubmonoid",
        "valueProfileNaturalPowers", "SourceIUTIIValueProfile",
        "TorsionUnitSubgroup",
        "SourceIUTIIMultiplicativeTorsionAction",
        "SourceIUTIIMultiplicativeTorsionAction.actionMap_injective",
        "SourceIUTIIMultiplicativeTorsionAction.toTorsionUnitSubgroup",
        "SourceIUTIIMultiplicativeTorsionAction.toTorsionThetaValueFamily",
        "SourceIUTIIMultiplicativeTorsionAction.thetaValues_eq_orbitCarriers",
        "SourceIUTIIMultiplicativeTorsionAction.toFiniteOrderAction",
        "SourceIUTIIMultiplicativeFiniteOrderAction",
        "SourceIUTIIMultiplicativeFiniteOrderAction.orbitCarrier_subset_torsion",
        "SourceIUTIITorsionThetaValueFamily",
        "SourceIUTIIThetaEvaluationOrbits.toTorsionThetaValueFamily",
        "SourceIUTIIThetaEvaluationOrbits.toTorsionThetaValueFamily_thetaValues",
        "SourceIUTIIValueProfile.equivPi",
        "SourceIUTIIValueProfile.natCard_eq_twoEll_pow_lStar",
        "SourceIUTIITorsionThetaValueFamily.representativeProfile",
        "SourceIUTIITorsionThetaValueFamily.profiles_differByPointwiseTorsion",
        "ValueProfilesDifferByPointwiseTorsion",
        "sourceTwoEllGaussianSubmonoid",
        "sourceTwoEllGaussianSubmonoid_eq",
        "SourceIUTIITorsionThetaValueFamily.twoEllGaussianSubmonoid_eq",
        "SourceIUTIITorsionThetaValueFamily.profileIndependentTwoEllGaussianSubmonoid",
        "SourceIUTIITorsionThetaValueFamily.twoEllGaussianSubmonoid_eq_profileIndependent",
        "ValueProfileRootSystem",
        "ValueProfilesDifferByDiagonalTorsion",
        "ValueProfileRootSystemsDifferByDiagonalTorsion",
        "sourceInfiniteGaussianMonoid_eq_of_differByDiagonalTorsion",
        "SourceIUTIISymmetrizingIsomorphisms.gaussianMonoid",
        "SourceIUTIISymmetrizingIsomorphisms.profile_mem_gaussianMonoid",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalActionHom",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalMonoidHom_equivariant",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalAction_mem_diagonalUnitSubmonoid",
        "SourceIUTIISymmetrizingIsomorphisms.diagonalAction_map_gaussianMonoid_eq",
        "SourceIUTIISymmetrizingIsomorphisms.gaussianMonoidActionHom",
        "SourceIUTIISynchronizedRestrictionIsomorphismClass",
        "SourceIUTIISynchronizedRestrictionDiagramClass",
        "sourceInfiniteGaussianMonoid",
        "thetaPowerValueProfile", "thetaPowerGaussianMonoid",
        "SourceTorsionCyclotomicCommMonoid.rationalCircle_torsion_natCard",
        "SourceTorsionCyclotomicCommMonoid.rootsOfUnityEquiv",
        "SourceTorsionCyclotomicCommMonoid.rootsOfUnity_natCard",
        "SourceTorsionCyclotomicCommMonoid.RootsOfUnityGroup",
        "SourceTorsionCyclotomicCommMonoid.rootsOfUnityGroup_natCard",
        "SourceIUTIIHodgeArakelovThetaPilot",
        "SourceIUTIIHodgeArakelovThetaPilot.thetaPowerProfile",
        "SourceIUTIIHodgeArakelovThetaPilot.finiteGaussianMonoid",
        "SourceIUTIIHodgeArakelovThetaPilot.infiniteGaussianMonoid",
        "SourceIUTIIHodgeArakelovThetaPilot.twoEllGaussianSubmonoid_eq_profileIndependent",
        "SourceIUTIIHodgeArakelovThetaPilot.thetaOrbit_natCard",
        "SourceIUTIIHodgeArakelovThetaPilot.valueProfiles_natCard",
        "SourceIUTIIHodgeArakelovThetaPilot.zeroTheta_carrier_subset_torsion",
        "ToyIUTIIGaussianFrobenioidObject"] .partialImplementation
      "A value profile is an actual simultaneous theta-value choice and is proved equivalent to the dependent product of its label fibers. Hence the (2l)^(l*) cardinality is derived from exact 2l orbit sizes. The finite Gaussian monoid is constructed in the heterogeneous product of the symmetrized labeled monoids from its derived diagonal unit submonoid and profile powers. The base group acts diagonally through the symmetrizing group isomorphisms; the constant embedding is equivariant, diagonal units are stable, and any profile-stable Gaussian monoid carries a derived natural action by monoid automorphisms. Restriction isomorphisms and their complete compatible group diagram may be recorded in exact quotients by one label-independent inner action. The homogeneous finite and rational-root variants are submonoids generated by diagonal units and natural/profile-root powers. Root-system ambiguity is expressed as diagonal N-torsion and is proved not to change the infinite Gaussian monoid. The n-torsion of Q/Z and the roots-of-unity group of a torsion-cyclotomic monoid are proved to have exactly n elements. A multiplicative mu_2l action is required to be injective, hence acts freely. The source Hodge-Arakelov pilot records actual q^(j^2) membership in continuous H1 theta orbits and compatible roots in infinite-theta orbits; from it Lean derives both Gaussian monoids, profile independence, zero-label torsion, every 2l orbit size, and the full profile count. Constructing this pilot, its multiplicative realization, profile stability, restriction-diagram representatives and inner action from the mono-theta data, and Frobenioid realization remain open; the real-degree preorder remains toy.",
    clause "II.3.5(iii)" .iutII "IUT II, Corollary 3.5(iii)"
      ["sourceConstantTorsion",
        "sourceConstantTorsion_map",
        "sourceConstantTorsionQuotientCongr",
        "sourceQuotientConstantSubgroup_map",
        "sourceQuotientThetaSet_image",
        "sourceSplittingFactorCongr",
        "SourceSplittingUpToTorsion",
        "SourceSplittingUpToTorsion.map",
        "sourceZeroLabelSplittingUpToTorsion",
        "sourceDiagonalConstantSubgroup",
        "SourceFiniteGaussianSplittingUpToTorsion",
        "SourceInfiniteGaussianSplittingUpToTorsion",
        "sourceGaussianMonoid_carrier_eq_splittingFactorProduct",
        "sourceInfiniteGaussianMonoid_carrier_eq_splittingFactorProduct",
        "sourceCorollary35FiniteGaussianSplittingOfProposition31",
        "sourceCorollary35InfiniteGaussianSplittingOfProposition31",
        "SourceTorsionDetectingRestriction",
        "SourceTorsionDetectingRestriction.splittingUpToTorsion",
        "sourceCorollary35FiniteGaussianSplittingOfRestrictionData",
        "sourceCorollary35InfiniteGaussianSplittingOfRestrictionData",
        "SourceIUTIIZeroLabelConstantComparison",
        "SourceIUTIIZeroLabelConstantComparison.zeroToLabel",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalMonoidHom",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalMonoidHom_injective",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalMonoidHom_eq_diagonalMonoidHom",
        "SourceIUTIIZeroLabelConstantComparison.zeroDiagonalSubmonoid_eq_diagonalRangeSubmonoid",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalMulEquiv",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalContinuousMulEquiv",
        "SourceIUTIIZeroLabelConstantComparison.zeroToDiagonalMonoidHom_equivariant",
        "ToyIUTIIHodgeArakelovEvaluationData"] .partialImplementation
      "Splitting up to torsion is an actual bijectivity predicate in the quotient by constant torsion, and the zero-label case is proved when the theta-value set is torsion. Given the paper's zero-to-base action-pair comparison, the comparisons to every nonzero label are derived. The resulting graph is proved equal to the diagonal range of Corollary 3.5(i), not merely isomorphic to a separately named carrier; the zero factor is continuously and multiplicatively equivalent to this graph and is equivariant for the transported labeled actions. Multiplicative equivalences are proved to preserve constant torsion, the quotient factors, and splitting bijectivity. The finite and infinite Gaussian carriers are proved equal to the displayed products Psi_cns^x * xi^N and Psi_cns^x * xi^Q>=0. Their splittings are derived directly by first applying the source torsion-detecting restriction criterion of Corollaries 1.12/2.6/2.8 and then transporting through one Gaussian restriction equivalence that identifies both factors; no Proposition 3.1 splitting proof is accepted as an endpoint input. Constructing the two paper restriction maps, their torsion and factor-identification proofs, and the zero-to-base comparison from the mono-theta system remains open.",
    clause "II.3.6" .iutII "IUT II, Corollary 3.6"
      ["ToyIUTIIGaussianFrobenioidObject"] .toyModel
      "The Gaussian Frobenioid is represented only by a label and real degree.",
    clause "II.3.7" .iutII "IUT II, Corollary 3.7"
      ["ToyIUTIIHodgeArakelovEvaluationData"] .unformalized
      "The group-theoretic and uniradial reconstruction statements are absent.",
    clause "II.4.6" .iutII "IUT II, Corollary 4.6"
      ["ToyIUTIIHodgeArakelovEvaluationData"] .unformalized
      "The cited Kummer-theoretic evaluation compatibility is not implemented.",
    clause "II.4.8" .iutII "IUT II, Corollary 4.8"
      ["SourceTopologicalPseudoMonoid",
        "SourceTopologicalGroupPseudoMonoidActionPair",
        "SourceKappaLocalizationDiagram",
        "SourceKappaLocalizationDiagram.inclusion_injective",
        "SourceKappaLocalizationDiagramIso",
        "SourceKappaLocalizationDiagramIso.localizationSquare",
        "SourceKappaLocalizationDiagramIso.inclusionSquare",
        "SourceTheorem311LabeledKummerIso"] .partialImplementation
      "The Corollary 4.8(iii) localization display is represented by an actual topological group/pseudo-monoid action pair for the kappa-solvable/global M-infinity-kappa datum, an action pair for each local M-infinity-kappa and M-infinity-kappa-times datum, an equivariant continuous pseudo-monoid localization map, and an equivariant topological embedding for the displayed local inclusion at every selected place. Defined partial products are preserved, and isomorphisms reflect their domains. Diagram isomorphisms preserve both arrows and yield arrow-category compatibility squares. The functorial construction from the NF-bridge, the Corollary 4.8(i)-(ii) Kummer restrictions, and the cyclotomic-rigidity reconstruction of IUT I, Example 5.1(v), remain open.",
    clause "II.4.9(i)" .iutII "IUT II, Definition 4.9(i)"
      ["SourceMLFGaloisTMPair.UnitModuloTorsion",
        "SourceMLFGaloisTMPair.unitModuloTorsion_eq_one_iff",
        "SourceMLFGaloisTMPair.unitModuloTorsionAction",
        "SourceMLFGaloisTMPair.fixedUnitSubgroup",
        "SourceMLFGaloisTMPair.invariantUnitImage",
        "SourceMLFGaloisTMPair.IsKummerIsometry",
        "SourceMLFGaloisTMPair.kummerIsmSubgroup",
        "SourceMLFGaloisTMPair.TimesMuKummerIsomorphism",
        "SourceMLFGaloisTMPair.TimesMuKummerOrbit",
        "SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.orbitOf_eq"]
      .partialImplementation
      "For the literal MLF-Galois model, O-times-mu is the actual quotient of the arithmetic-monoid units by their full torsion subgroup, and the quotient map is proved to kill exactly torsion. The Galois action descends to this quotient. For every Krull-open subgroup H, I_H^kappa is the image of the actual H-fixed unit subgroup. Ism is the subgroup of equivariant quotient automorphisms preserving every such invariant image. A times-mu Kummer structure is the resulting orbit of compatible isomorphisms, and any two compatible representatives are proved to lie in the same orbit. The intrinsic ind-topology and the split Kummer Frobenioids of Definition 4.9(ii)-(v) remain open.",
    clause "II.4.9(ii-iv)" .iutII "IUT II, Definition 4.9(ii)-(iv)"
      ["SourceSplitKummerMonoid.unitCongruence",
        "SourceSplitKummerMonoid.unitQuotient_isUnit_eq_one",
        "SourceMLFGaloisTMPair.TwoEllRootsOfUnity",
        "SourceMLFGaloisTMPair.badPerpMonoid",
        "SourceMLFGaloisTMPair.badCharacteristicQuotient",
        "SourceMLFGaloisTMPair.badTimesMuMonoid",
        "SourceMLFGaloisTMPair.goodTimesMuMonoid",
        "SourceMLFGaloisTMPair.badTimesMuUnitsEquiv",
        "SourceMLFGaloisTMPair.goodTimesMuUnitsEquiv",
        "SourceMLFGaloisTMPair.badCharacteristicAction",
        "SourceMLFGaloisTMPair.badTimesMuAction",
        "SourceMLFGaloisTMPair.goodTimesMuAction",
        "SourceMLFGaloisTMPair.badTimesMuUnitsEquiv_equivariant",
        "SourceMLFGaloisTMPair.goodTimesMuUnitsEquiv_equivariant",
        "SourceFiniteTimesMuKummerInput",
        "SourceFiniteTimesMuKummerInput.timesMuMonoid",
        "SourceFiniteTimesMuKummerInput.timesMuUnitsEquiv",
        "SourceFiniteTimesMuKummerFrobenioid",
        "SourceFiniteTimesMuKummerFrobenioid.rationalUnitsEquiv"]
      .partialImplementation
      "At a bad finite place, O-perp is the actual join of the splitting image with mu_(2l), O-square is its exact multiplicative-congruence quotient by mu_(2l), and O^(square times-mu) is the literal product with O^(times-mu). At a good finite place the literal product uses the splitting image directly. Injectivity of unit-characteristic factorization proves that no new units survive in the characteristic factor. The new finite-place input ties the selected Frobenioid splitting at an isotropic reference object to an actual MLF-Galois TM pair, its stable characteristic submonoid, and the genuine Ism Kummer orbit. The output retains a reconstructed split Frobenioid whose base category is equivalent to the original base and whose reference rational monoid is isomorphic to the constructed bad/good product; its full unit group is consequently proved equivalent to O^(times-mu). Constructing the input from Frobenioid evaluation and deriving the output via Frobenioids I Theorem 5.2(ii) remain open; the analogous archimedean reconstruction boundary is recorded separately in Definition 4.9(v).",
    clause "II.4.9(v)" .iutII "IUT II, Definition 4.9(v)"
      ["SourceArchimedeanKummerSystem.UnitQuotient",
        "SourceArchimedeanKummerSystem.rootsOfUnity_isClosed",
        "SourceArchimedeanKummerSystem.continuousQuotientMap",
        "SourceArchimedeanKummerSystem.continuousQuotientMap_isOpenQuotientMap",
        "SourceArchimedeanKummerSystem.transition",
        "SourceArchimedeanKummerSystem.transition_ker",
        "SourceArchimedeanKummerSystem.continuousTransition",
        "SourceArchimedeanKummerSystem.continuousTransition_comp",
        "SourceArchimedeanKummerSystem.Orientation",
        "SourceArchimedeanKummerSystem.orientationAutomorphism",
        "SourceArchimedeanKummerSystem.orientedQuotientMap_ker",
        "SourceArchimedeanKummerSystem.unitQuotientPresentation",
        "SourceArchimedeanKummerSystem.noncompact_eq_one_of_isUnit",
        "SourceArchimedeanKummerSystem.quotientSplitTopologicalMonoid",
        "SourceArchimedeanKummerSystem.quotientSplitTransition",
        "SourceArchimedeanKummerSystem.FrobenioidStage",
        "SourceArchimedeanKummerSystem.FrobenioidSystem",
        "SourceArchimedeanKummerSystem.FrobenioidSystem.divisor_compatible",
        "SourceArchimedeanKummerSystem.FrobenioidSystem.frobeniusDegree_compatible",
        "SourceArchimedeanKummerSystem.FrobenioidSystem.carrierDiagram",
        "SourceArchimedeanKummerSystem.FrobenioidSystem.baseDiagram",
        "SourceArchimedeanKummerSystem.FrobenioidSystem.rationalMonoidDiagram",
        "SourceArchimedeanKummerSystem.unitQuotientDiagram",
        "SourceArchimedeanKummerSystem.MultiplicativelyCofinalSubset",
        "SourceArchimedeanKummerSystem.MultiplicativelyCofinalSubset.indexInclusionFinal",
        "SourceArchimedeanKummerSystem.MultiplicativelyCofinalSubset.isColimitEquivRestricted",
        "SourceArchimedeanKummerSystem.restrictedUnitQuotientDiagram",
        "SourceArchimedeanKummerSystem.restrictedOrientedQuotientNaturalTransformation",
        "SourceArchimedeanTimesMuQuotientSystem",
        "SourceArchimedeanTimesMuQuotientSystem.reversedQuotientMap_kernel",
        "SourceArchimedeanTimesMuStage",
        "SourceArchimedeanTimesMuSystem",
        "SourceArchimedeanTimesMuSystem.carrierDiagram",
        "SourceArchimedeanTimesMuSystem.isColimitEquivRestricted"]
      .partialImplementation
      "The compact factor is the actual circle, mu_N is the exact closed kernel of the N-th power map, and every quotient carries its quotient topology. The exact split topological stage is the product of Circle/mu_N with the unchanged noncompact factor; the latter is proved to have no nontrivial units. A reconstructed stage must be an actual archimedean split Frobenioid structure-preservingly isomorphic to this product and must retain the original base category. Transition functors preserve the base projection, FSM morphisms, divisors, and Frobenius degrees. Carrier, base, and reference rational-monoid transitions form strict divisibility-indexed diagrams, with the rational transition forced to be the concrete quotient map on the compact factor and the identity on the noncompact factor. Every multiplicatively cofinal subset is proved filtered, its inclusion is final, and the universal colimit cocone is therefore canonically preserved and reflected. The identity/inversion orientations give distinct compatible systems of open quotient maps with the same exact kernels. A universe-polymorphic boundary now retains these same exact kernel, quotient-surjectivity, transition, orientation-classification, split-stage, divisor, and Frobenius conditions for the generic theorem types. Deriving and populating this boundary from the original archimedean TM/Frobenioid data remains open.",
    clause "II.4.9(vi-viii)" .iutII "IUT II, Definition 4.9(vi)-(viii)"
      ["PreFrobenioid.isometricMorphismProperty",
        "PreFrobenioid.IsometryCategory",
        "SourceFTimesMuPrimeStrip",
        "SourceFTimesMuPrimeStrip.finiteUnderlyingIsometryCategory",
        "SourceFTimesMuPrimeStrip.finiteTimesMuIsometryCategory",
        "SourceFTimesMuPrimeStrip.archimedeanUnderlyingIsometryCategory",
        "SourceFTimesMuPrimeStrip.archimedeanTimesMuIsometryCategory",
        "SourceFTimesMuPrimeStrip.archimedeanTimesMuIsometryTransition",
        "SourceMLFGaloisTMPairEquivalence",
        "SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.transport",
        "SourceFiniteTimesMuKummerInput.characteristicGenerator",
        "SourceFiniteTimesMuKummerFrobenioidEquivalence",
        "SourceFiniteTimesMuKummerFrobenioidEquivalence.trans",
        "SourceFiniteTimesMuKummerFrobenioidEquivalence.kummerStructure_compatible",
        "SourceArchimedeanTimesMuStageEquivalence",
        "SourceArchimedeanTimesMuStageEquivalence.isometryFunctor",
        "SourceArchimedeanTimesMuSystemEquivalence",
        "SourceArchimedeanTimesMuSystemEquivalence.trans",
        "SourceArchimedeanTimesMuSystemEquivalence.carrierNaturalTransformation",
        "SourceFTimesMuPrimeStripEquivalence",
        "SourceFTimesMuPrimeStripEquivalence.trans",
        "SourceFrobenioidEquivalence",
        "SourceFrobenioidEquivalence.trans",
        "SourceFTimesMuPilotReconstruction",
        "SourceFTimesMuPilotReconstruction.localPilotCharacter",
        "SourceFTimesMuPilotReconstruction.pilotObject",
        "SourceFTimesMuPilotReconstruction.pilotObject_negative",
        "SourceFGloballyRealifiedTimesMuPrimeStrip",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.trans",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.localPilotCharacter_compatible",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.pilotObjectIso",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.pilotObject_arithmeticDegree_compatible",
        "SourceMLFGaloisTMPairEquivalence.StructurallyEqual",
        "SplitFrobenioidEquivalence.NaturallyIsomorphic",
        "SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic",
        "SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic",
        "SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic",
        "SourceFTimesMuPrimeStripFullPolyIsomorphism",
        "SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc",
        "SourceFMonoAnalyticPrimeStripEquivalence",
        "SourceFMonoAnalyticPrimeStripFullPolyIsomorphism",
        "SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical",
        "SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical_inverse",
        "SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp_assoc",
        "SourceFTimesMuReconstructionObjects",
        "SourceFTimesMuReconstructionTransport",
        "SourceFTimesMuReconstructionFullness",
        "SourceFTimesMuReconstructionAlgorithm",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_id",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_comp",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_surjective",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_inverse",
        "SourceFrobenioidEquivalence.NaturallyIsomorphic",
        "SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic",
        "SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism",
        "SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism.comp_assoc",
        "SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism.nonempty_iff"]
      .partialImplementation
      "The Definition 4.9(vi)-(vii) local collection now selects the exact bad/good finite reconstruction at every selected finite place and the complete universe-polymorphic torsion-quotient Frobenioid system at every archimedean place. The kind equation prevents exchanging the bad and good constructions. The F-times and F-times-mu coarsifications are the actual wide subcategories cut out by divisor-zero isometries, and archimedean transitions are proved to preserve this condition. Every mono-analytic strip now retains structure-preserving maps both to and from the common source model together with two-sided Section 0 inverse laws. Lean therefore constructs canonical theta-link and Kummer members and proves that the reverse canonical member is an inverse. At a finite place, a structure-preserving isomorphism also retains the exact underlying split-Frobenioid equivalence, in addition to transporting the topological Galois group, arithmetic monoid action, unit-mod-torsion quotient, every open-subgroup invariant Kummer image, characteristic and unit product generators, reconstructed split Frobenioid, base, reference object, and rational monoid. The analogous archimedean map transports every torsion quotient, orientation and transition map, reconstructed stage, base, divisor, Frobenius degree, FSM morphism, split product, and rational transition. A functorial reconstruction boundary assembles its object from all exact finite and archimedean outputs, assembles its map componentwise with proofs that every lift projects to the supplied underlying equivalence, and respects natural isomorphism, identity, and composition. Corollary 4.10(iv) fullness is a separate representative-level law scoped to each actual adjacent horizontal pair; Lean proves quotient-level surjectivity from that law. The global isomorphism additionally carries the global Frobenioid, prime/place, rho, reconstruction, and arithmetic-degree data; pilot preservation is derived. Constructing the finite/archimedean outputs, proving the scoped reconstruction fullness laws from their unit-portion rigidity, and constructing the global pilot function and degree from the cited source theorems remain open.",
    clause "II.4.10(i)" .iutII "IUT II, Corollary 4.10(i)"
      ["ToyIUTIIQPilot"] .partialImplementation
      "The q-pilot numerical profile is present, but its categorical pilot object is not.",
    clause "II.4.10(ii)" .iutII "IUT II, Corollary 4.10(ii)"
      ["thetaPowerValueProfile", "thetaPowerGaussianMonoid",
        "ToyIUTIIThetaPilot"] .partialImplementation
      "Every q^(j^2) is now an actual monoid element on the source sign-label representatives and generates an actual Gaussian submonoid. The corresponding theta-pilot Frobenioid objects, evaluation isomorphisms, and global labels remain open; the real-degree projection remains toy.",
    clause "II.4.10(iii)" .iutII "IUT II, Corollary 4.10(iii)"
      ["SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_comp",
        "ToyIUTIIHodgeArakelovEvaluationData"] .partialImplementation
      "The exact componentwise Definition 4.9 functor now induces maps on Section 0 full poly-isomorphisms and preserves composition. Constructing the environment/Gaussian F-prime-strips and their theta evaluation isomorphism from Corollary 4.6 remains open.",
    clause "II.4.10(iv)" .iutII "IUT II, Corollary 4.10(iv)"
      ["SourceTheorem311TimesMuPrimeStripConstruction.toFamily",
        "SourceFTimesMuReconstructionFullness",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_surjective",
        "SourceTheorem311TimesMuPrimeStripConstruction.thetaLink_full",
        "SourceTheorem311TimesMuPrimeStripConstruction.toTriangleSquare",
        "SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily.toTimesMu",
        "SourceFTimesMuReconstructionAlgorithm.mapFullPolyIsomorphism_inverse",
        "ToyIUTIIHodgeArakelovEvaluationData"] .partialImplementation
      "One reconstruction algorithm computes every site, vertically coric, and environment times-mu endpoint and derives the environment comparisons from mono-analytic Proposition 2.1(vi) data. Corollary 4.10(iv) fullness is now a representative-level rigidity law for each actual adjacent horizontal pair, separate from functoriality; quotient surjectivity is proved from it. Every mono-analytic model comparison carries two-sided Section 0 inverse laws, so Lean derives the theta-link and both Theorem 1.5 Kummer directions through the common model, proves their cancellation, reconstructs all horizontal and vertical maps, and derives the complete clause (a) square. There is no arbitrary quotient-level fullness witness or chosen Kummer-source record. Constructing the local reconstruction outputs, their pairwise fullness proofs, and the coherent model comparisons from Corollaries 4.5, 4.6, and 4.10 remains open.",
    clause "II.4.10(v)" .iutII "IUT II, Corollary 4.10(v)"
      ["ToyIUTIIHodgeArakelovEvaluationData"] .unformalized
      "The coric-unit compatibility is not constructed.",
    clause "II.4.10(vi)" .iutII "IUT II, Corollary 4.10(vi)"
      ["ToyIUTIIGaussianFrobenioidObject"] .toyModel
      "The global Gaussian Frobenioids are not constructed.",
    clause "II.4.11" .iutII "IUT II, Corollary 4.11"
      ["ToyIUTIIHodgeArakelovEvaluationData"] .unformalized
      "The etale-picture compatibility is absent.",

    clause "III.1.1" .iutIII "IUT III, Definition 1.1"
      ["SourceSelectedPlace.LogFieldCarrier",
        "SourceSelectedLocalLogFieldRealization",
        "sourcePStar",
        "sourcePStar_pos",
        "SourceRationalPlace.residuePrime",
        "SourceRationalPlace.residuePrime_prime",
        "SourceGaloisFixedLocalUnits",
        "SourceGaloisLocalUnitData",
        "SourceNonarchimedeanLogShellDefinition",
        "SourceNonarchimedeanLogShellDefinition.invariantLocalUnits_fixed",
        "SourceNonarchimedeanLogShellDefinition.preLogShell_isCompact",
        "SourceArchimedeanLogShellDefinition.fundamentalSegment",
        "SourceArchimedeanLogShellDefinition.lowerEndpoint_mem",
        "SourceArchimedeanLogShellDefinition.upperEndpoint_mem",
        "SourceArchimedeanLogShellDefinition.upperEndpoint_sub_lowerEndpoint",
        "SourceArchimedeanLogShellDefinition.neg_mem_iff",
        "SourceArchimedeanLogShellDefinition.rotationOrbit",
        "SourceArchimedeanLogShellDefinition.rotationOrbit_eq_closedBall",
        "SourceArchimedeanLogShellDefinition.complexExponential_isCoveringMap",
        "SourceArchimedeanLogShellDefinition.complexExponential_eq_one_iff",
        "SourceArchimedeanLogShellDefinition.RootQuotient",
        "SourceArchimedeanLogShellDefinition.rootQuotient_deckGroup_eq_rootsOfUnity",
        "SourceArchimedeanLogShellDefinition.rootQuotientPowerLift_isQuotientMap",
        "SourceArchimedeanLogShellDefinition.rootQuotientHomeomorphUnits",
        "SourceArchimedeanLogShellDefinition.rootQuotientExponential_zero",
        "SourceArchimedeanLogShellDefinition.rootQuotientHomeomorphUnits_exponential",
        "SourceArchimedeanLogShellDefinition.rootQuotientExponential_isCoveringMap",
        "SourceArchimedeanLogShellDefinition.rootQuotientExponential_eq_one_iff_mem_periodLattice",
        "SourceArchimedeanLogShellDefinition.quotientFundamentalSegment",
        "SourceArchimedeanLogShellDefinition.quotientLowerEndpoint_mem",
        "SourceArchimedeanLogShellDefinition.quotientUpperEndpoint_mem",
        "SourceArchimedeanLogShellDefinition.quotientUpperEndpoint_sub_lowerEndpoint",
        "SourceArchimedeanLogShellDefinition.image_quotientFundamentalSegment",
        "SourceArchimedeanLogShellDefinition.exponential_isCoveringMap",
        "SourceArchimedeanLogShellDefinition.exponential_eq_one_iff",
        "SourceArchimedeanLogShellDefinition.principalLog",
        "SourceArchimedeanLogShellDefinition.exponential_principalLog",
        "SourceArchimedeanLogShellDefinition.principalLog_mem_unitBall",
        "SourceArchimedeanLogShellDefinition.image_unitBall_eq_rotationOrbit",
        "SourceMonoAnalyticLogShellDefinition",
        "SourceMonoAnalyticIntegralStructure.logShellCarrier",
        "SourceMonoAnalyticIntegralStructure.logShellCarrier_eq_lattice",
        "SourceMonoAnalyticIntegralStructure.logShellCarrier_eq_unitBall",
        "SourceMonoAnalyticLogShell",
        "SourceMonoAnalyticLogShellAlgorithm.carrierAddEquivAbove",
        "SourceSelectedLocalFullLogLink",
        "SourceSelectedLocalFullLogLink.NonarchimedeanRelated",
        "SourceSelectedLocalFullLogLink.ArchimedeanRelated",
        "SourceSelectedLocalFullLogLink.nonarchimedean_target_unique",
        "SourceSelectedLocalFullLogLink.archimedean_target_unique"]
      .partialImplementation
      "The additive log field is tied to the actual selected-place algebraic closure and its filtered field stages. At finite places the source log-shell is the additive lattice. At an infinite place Proposition 3.2(ii)'s Hermitian seminorm is normalized by pi, so its unit ball is exactly Definition 1.1(ii)'s raw complex radius-pi rotation orbit; there is no second radius-pi ball of the normalized metric. The source segment is sign-stable and its endpoints differ by 2*pi*i. The transported exponential is a covering with the exact period lattice, while arg in (-pi,pi] gives a principal logarithm of every genuine circle unit, proved to lie in the normalized unit ball and exponentiate back to that unit. The quotient coverings by mu_N retain their exact periods and endpoint segments. At finite places the residue prime, fixed local units, compact pre-log-shell, and p-adic logarithm are retained explicitly. A selected-place full log-link now consists of a continuous rational-linear post-composition compatible with an actual ring equivalence of logarithmic fields, plus continuous injective realizations of the adjacent target units. The finite and infinite relations are equality between the source logarithm and this target-unit realization, and their target is proved unique. Constructing these data from the cited Frobenioid poly-isomorphisms remains open.",
    clause "III.1.1.1(ii)" .iutIII "IUT III, Remark 1.1.1(ii)"
      ["SourceAutHolomorphicSemiGerm.neighborhoodSystem",
        "SourceAutHolomorphicSemiGerm.iInter_neighborhood_eq_unitCircle",
        "SourceAutHolomorphicSemiGerm.exists_neighborhood_subset_of_mem",
        "SourceAutHolomorphicSemiGerm.multiplication_holomorphicOn_levels",
        "SourceAutHolomorphicSemiGerm.multiplication_tendsto_unitNeighborhoodFilter",
        "SourceAutHolomorphicSemiGerm.inversion_holomorphicAtLevel",
        "SourceAutHolomorphicSemiGerm.inversion_tendsto_unitNeighborhoodFilter",
        "SourceAutHolomorphicSemiGerm.puncturedNeighborhood_eq_inner_union_outer",
        "SourceAutHolomorphicSemiGerm.innerSide_eq_connectedComponentIn",
        "SourceAutHolomorphicSemiGerm.outerSide_eq_connectedComponentIn",
        "SourceAutHolomorphicSemiGerm.levelConnectedOpen",
        "SourceAutHolomorphicSemiGerm.levelAutHolomorphic",
        "SourceAutHolomorphicSemiGerm.levelInclusion_hasAmbientHolomorphicLift",
        "SourceAutHolomorphicSemiGerm.restrictToLevel_mul",
        "SourceAutHolomorphicSemiGerm.restrictToLevel_inv",
        "SourceAutHolomorphicRigidity.Automorphism.exponentialLift_eq_exp_exponentCoefficient",
        "SourceAutHolomorphicRigidity.Automorphism.exponent_eq_one_or_neg_one",
        "SourceAutHolomorphicRigidity.Automorphism.toAutHolomorphic_eq_identity",
        "SourceAutHolomorphicRigidity.Automorphism.ambientGerm_eq_identity",
        "SourceArchimedeanLogShellDefinition.semiGermNeighborhoodSystem",
        "SourceArchimedeanLogShellDefinition.semiGermNeighborhoodSystem_cofinal",
        "SourceArchimedeanLogShellDefinition.semiGermSelectedSide_eq_connectedComponentIn",
        "SourceArchimedeanLogShellDefinition.semiGermAutHolomorphicAssignment",
        "SourceArchimedeanLogShellDefinition.restrictSemiGermAutomorphism",
        "SourceArchimedeanLogShellDefinition.SemiGermGroupAutomorphism.rigid",
        "SourceArchimedeanLogShellDefinition.semiGermMultiplication_tendsto",
        "SourceArchimedeanLogShellDefinition.semiGermInversion_tendsto",
        "SourceArchimedeanPacketUnitData.summandSemiGermNeighborhoodSystem",
        "SourceArchimedeanPacketUnitData.UnitTuple.semiGermUnit"]
      .partialImplementation
      "Lean constructs an explicit antitone projective system of open annuli around S1 in C-times, proves that their intersection is exactly S1 and that they are cofinal among all neighborhoods of S1, and assigns the derived group Aut_hol(U_n) to every connected annular level with holomorphic transition inclusions and proved restriction laws. Ambient multiplication and inversion preserve the corresponding neighborhood filters. Removing S1 splits each level into the two stated radial connected components, with the O-triangleright_C side selected by theorem. For groupification-induced holomorphic group automorphisms, Lean derives the integer exponent from the exponential covering, proves it is plus or minus one, rules out inversion by selected-side preservation, and proves equality of the induced filter germ with the identity. Each archimedean packet unit is canonically promoted to the actual semi-germ core. Extending the rigidity classification from groupification-induced automorphisms to every purely local group-germ automorphism, the general RC-holomorphic local-morphism category, and co-holomorphic/Kummer reconstruction remain open.",
    clause "III.1.2(vi-viii)" .iutIII
      "IUT III, Proposition 1.2(vi)-(viii)"
      ["SourceNonarchimedeanLogShellSymmetryCore",
        "SourceNonarchimedeanLogShellSymmetry",
        "SourceArchimedeanLogShellSymmetry",
        "SourceMonoAnalyticLogShellSymmetryData",
        "SourceMonoAnalyticLogShell",
        "SourceMonoAnalyticLogShellAlgorithm",
        "SourceNonarchimedeanLogShellDefinition.Transport",
        "SourceNonarchimedeanLogShellDefinition.Transport.preLogShell_image",
        "SourceMonoAnalyticLogShellAlgorithm.transport_preLogShell",
        "SourceMonoAnalyticLogShellAlgorithm.sourceLocalUnitsEquiv_id",
        "SourceMonoAnalyticLogShellAlgorithm.sourceLocalUnitsEquiv_comp",
        "SourceMonoAnalyticLogShellAlgorithm.transport_logShell",
        "SourceMonoAnalyticLogShellAlgorithm.transport_measuredRegion",
        "SourceMonoAnalyticLogShellAlgorithm.transport_logVolume"]
      .partialImplementation
      "A shell carries its actual ind-topological field realization, compact source-shaped shell, finite-place Ism or independent archimedean sign symmetry, and log-volume functional. At finite places, prime-strip morphisms also carry continuous local-unit equivalences commuting with the p-adic logarithm; exact preservation of the pre-log-shell is derived, and the unit equivalences satisfy identity and composition. The module and field transports satisfy the same category laws; preservation of the finite lattice and archimedean Hermitian seminorm derives preservation of the actual radius-pi log-shell and its measured value. Constructing these data functorially from the D-tilde and F-tilde-times-mu components via Absolute Anabelian Topics III, Proposition 5.8, and constructing the Proposition 1.2 poly-isomorphism orbits remain open.",

    clause "III.3.1" .iutIII "IUT III, Proposition 3.1"
      ["SourceRationalPlace", "SourceRationalPlace.Completion",
        "SourceSelectedPlaceAbove", "SourceSelectedPlaceFiberFiniteness",
        "SourceSelectedFinitePlace.toSelected",
        "SourceSelectedInfinitePlace.toSelected",
        "SourceSelectedPlace.LogFieldCarrier",
        "SourceIndTopologicalLocalModule",
        "ThetaFinitePlace.completionNontriviallyNormedField",
        "ThetaFinitePlace.completionSecondCountableTopology",
        "ThetaFinitePlace.rationalCompletionLocallyCompactSpace",
        "ThetaFinitePlace.underlyingPrime_comap_asIdeal",
        "ThetaFinitePlace.rationalValuation_isEquiv_restriction",
        "ThetaFinitePlace.rationalWithValMap_uniformContinuous",
        "ThetaFinitePlace.rationalDenseRingHom",
        "ThetaFinitePlace.continuous_rationalDenseRingHom",
        "ThetaFinitePlace.completionRingHom",
        "ThetaFinitePlace.continuous_completionRingHom",
        "ThetaFinitePlace.completionRingHom_ratCast",
        "ThetaFinitePlace.completionAlgebra",
        "ThetaFinitePlace.completionContinuousSMul",
        "ThetaFinitePlace.completionScalarTower",
        "ThetaFinitePlace.finiteDimensional",
        "ThetaFinitePlace.properSpace",
        "SourceTopologicalLocalField",
        "SourceTopologicalLocalField.ofFinitePlace",
        "SourceTopologicalLocalField.localDegree",
        "SourceTopologicalLocalField.LocalDegreeTower",
        "SourceTopologicalLocalField.LocalDegreeTower.relativeDegree",
        "SourceTopologicalLocalField.LocalDegreeTower.localDegree_eq_relativeDegree_mul_moduliDegree",
        "SourceLocalFieldStage",
        "SourceIndTopologicalLocalFieldPresentation",
        "SourceIndTopologicalLocalFieldPresentation.transition_id",
        "SourceIndTopologicalLocalFieldPresentation.transition_comp",
        "SourceFiniteLocalFieldStages.AlgebraicClosure",
        "SourceFiniteLocalFieldStages.StageIndex",
        "SourceFiniteLocalFieldStages.transitionLinearMap",
        "SourceFiniteLocalFieldStages.transitionContinuousLinearMap",
        "SourceFiniteLocalFieldStages.stageDiagram",
        "SourceFiniteLocalFieldStages.moduleCocone",
        "SourceFiniteLocalFieldStages.moduleIsColimit",
        "SourceFiniteLocalFieldStages.stageField",
        "SourceFiniteLocalFieldStages.module",
        "SourceFiniteLocalFieldStages.fieldPresentation",
        "SourceFiniteLocalFieldStages.toAlgebraicClosureLinearMap",
        "SourceFiniteLocalFieldStages.toAlgebraicClosureLinearMap_injective",
        "SourceFiniteLocalFieldStages.toAlgebraicClosureLinearMap_surjective",
        "SourceFiniteLocalFieldStages.carrierEquivAlgebraicClosure",
        "SourceFiniteLocalFieldStages.selectedCompletionEmbedding",
        "SourceFiniteLocalFieldStages.continuous_selectedCompletionEmbedding",
        "SourceFiniteLocalFieldStages.stage_fixingSubgroup_isOpen",
        "SourceFiniteLocalFieldStages.stage_fixedField_fixingSubgroup",
        "SourceFiniteLocalFieldStages.selectedCompletionBasis",
        "SourceFiniteLocalFieldStages.selectedStageGenerators",
        "SourceFiniteLocalFieldStages.selectedStage",
        "SourceFiniteLocalFieldStages.selectedCompletionEmbedding_mem_selectedStage",
        "SourceFiniteLocalFieldStages.stageEmbeddingUlift",
        "SourceFiniteLocalFieldStages.carrierEquivLogFieldCarrier",
        "SourceFiniteLocalFieldStages.localFieldRealization",
        "SourceInfiniteLocalFieldStages.rationalPlace_isReal",
        "SourceInfiniteLocalFieldStages.rationalCompletionEquivReal",
        "SourceInfiniteLocalFieldStages.rationalCompletionEmbedding",
        "SourceInfiniteLocalFieldStages.continuous_rationalCompletionEmbedding",
        "SourceInfiniteLocalFieldStages.complexFiniteDimensional",
        "SourceInfiniteLocalFieldStages.stageField",
        "SourceInfiniteLocalFieldStages.stageDiagram",
        "SourceInfiniteLocalFieldStages.module",
        "SourceInfiniteLocalFieldStages.fieldPresentation",
        "SourceInfiniteLocalFieldStages.selectedCompletionEmbedding",
        "SourceInfiniteLocalFieldStages.selectedBaseCompletionRingHom",
        "SourceInfiniteLocalFieldStages.selectedCompletionEmbedding_algebraMap",
        "SourceInfiniteLocalFieldStages.selectedCompletion_finiteDimensional",
        "SourceInfiniteLocalFieldStages.selectedCompletion_isAlgebraicClosure",
        "SourceInfiniteLocalFieldStages.stageEmbeddingUlift",
        "SourceInfiniteLocalFieldStages.carrierEquivLogFieldCarrier",
        "SourceInfiniteLocalFieldStages.localFieldRealization",
        "SourceSelectedLocalLogFieldRealization",
        "SourceMonoAnalyticLogShell",
        "SourceMonoAnalyticLogShell.fieldPresentation",
        "SourceMonoAnalyticLogShellAlgorithm",
        "SourceMonoAnalyticLogShellAlgorithm.integralAbove",
        "SourceMonoAnalyticLogShellAlgorithm.normalizedLogVolumeAbove"]
      .partialImplementation
      "Rational places are literal places of Q; selected fibers v above v_Q are derived and only those fibers are required finite. Local logarithmic modules are filtered colimits over the actual completion Q_(v_Q). A finite-place constructor now has the literal v-adic completion K_v as carrier. In accordance with Proposition 3.1 and the local-degree normalization of Remark 3.1.1(ii), the contracted rational valuation is proved equivalent to the restriction of the K-valuation, rather than equal to it. This equivalence and a cofinal uniformizer argument construct the uniformly continuous dense rational map and its unique continuous extension Q_p -> K_v. The resulting algebra, continuous scalar action, and Q -> Q_p -> K_v tower are derived, so no completion-extension structure is accepted as input. Mathlib's tensor-product/dense-range theorem then derives module-finiteness and finite-dimensionality. A global uniformizer proves the completion nontrivially normed; the rational completion is locally compact via its continuous equivalence with Q_p; finite-dimensional topological local compactness and the intrinsic norm prove K_v proper. Countability of the number field derives separability and second countability. Thus no independent topology, replacement field, or completion algebra obligation remains. At a nonarchimedean rational place, the finite Galois intermediate subfields of the spectral-normed algebraic closure form the actual filtered diagram. Its transitions are continuous field inclusions, its final TopModuleCat cocone is colimiting, and its direct limit is linearly equivalent to the algebraic closure. Open-subgroup invariants recover every stage, while an embedded basis puts each selected K_v inside one stage. At the infinite rational place, the completion is canonically R and the source log field is the constant filtered C diagram. The explicit basis {1,i} proves finite dimensionality over Q_infinity. Every actual selected archimedean completion embeds continuously and injectively into C, compatibly with Q_infinity; a real/complex case proof makes C finite over K_v and hence its algebraic closure. Both canonical diagrams now have realization certificates whose stage embeddings commute with transitions and whose colimit equivalence agrees with every cocone leg. Every mono-analytic shell must carry such a realization, and every prime-strip morphism must carry a compatible algebra automorphism satisfying identity and composition. Constructing these shell and transport choices from Proposition 1.2's source categories, constructing its integral log-shell algorithm, and proving Proposition 3.1's poly-isomorphisms remain open.",
    clause "III.3.2" .iutIII "IUT III, Proposition 3.2"
      ["SourceLocalLogDirectSum", "SourceMonoAnalyticTensorPacket",
        "SourceMonoAnalyticTensorPacket.PlaceTupleIndex",
        "SourceMonoAnalyticTensorPacket.placeTupleIndex_card",
        "SourceMonoAnalyticTensorPacket.distinguishedSubmodule",
        "SourceMonoAnalyticTensorPacketFieldPresentation",
        "SourcePacketFiniteFieldStage",
        "SourcePacketFiniteFieldStage.localTensor_finrank",
        "SourcePacketFiniteFieldStage.field_finrank_sum",
        "SourcePacketFiniteFieldStage.field_finrank_sum_eq_factor_finrank_product",
        "SourcePacketFiniteFieldDecomposition",
        "SourcePacketFiniteFieldDecomposition.FieldSummandIndex",
        "SourcePacketFiniteFieldDecomposition.fieldSummandIndex_card",
        "SourcePacketFiniteFieldDecomposition.placeTupleDecomposition",
        "SourcePacketFiniteFieldDecomposition.stageModule",
        "SourcePacketFiniteFieldDecomposition.stageEmbedding",
        "SourcePacketFiniteFieldDecomposition.stageEmbedding_injective",
        "SourcePacketFiniteMeasuredFieldDecomposition.BlockFieldCoordinates",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockFieldDecomposition",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockFieldDecomposition_image_integralRegion",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockIntegralRegion_iff",
        "SourcePacketFiniteStageLogVolume.Compatible",
        "SourcePacketFiniteStageLogVolume.Compatible.packetKummer_image_embeddedPacketIntegralRegion",
        "SourceMonoAnalyticLogShellAlgorithm.TensorTopology",
        "SourceMonoAnalyticLogShellAlgorithm.packetOfCapsule",
        "SourceNonarchimedeanPacketIntegralConstruction",
        "SourceArchimedeanPacketIntegralConstruction",
        "SourcePacketIntegralConstruction",
        "SourceIntegralRegionOn", "SourceTheorem311LocalData",
        "SourceAbsoluteLGPGaussianLogThetaLattice.PacketIntegralConstruction",
        "SourceAbsoluteLGPGaussianLogThetaLattice.LocalConstruction.toTheorem311LocalData"]
      .partialImplementation
      "Local packets are literal dependent tensor products of direct sums over the actual finite place fiber, with the tensor universal topology. The canonical tensor-of-direct-sums equivalence yields exactly #places^(j+1) place-tuple tensor blocks, not fields. A field-valued factor presentation and a chosen cofinal finite stage inject each stage tensor into its ind-block and decompose its tensor algebra as a finite product of actual complete local fields; the genuine field index is the dependent sum of these internal indices, and its cardinality is derived as a sum rather than conflated with the place-tuple count. The simultaneous product of finite stages has a proved injective rational-linear map into the actual ind-packet, not a false equivalence. Each stage field decomposition is retained as a homeomorphism and detects the fieldwise product integral structure. A finite-stage poly-isomorphism now carries actual field indices, continuous field maps, radial maps, and the stage embedding, and its commutation with the packet Kummer map is explicit. Constructing these presentations, CRT decompositions, and poly-isomorphisms from the cited prime strips remains open. The legacy whole-place-tuple measured object is expressly non-accepting.",
    clause "III.3.4" .iutIII "IUT III, Proposition 3.4"
      ["SourceLGPSplittingMonoidAction",
        "SourceLGPSplittingMonoidAction.targetMulAction"]
      .partialImplementation
      "A genuine commutative splitting monoid embeds into and acts multiplicatively on an actual distinguished tensor submodule. Construction of the LGP monoid, its Galois invariants, and this action from the Hodge theater remains open.",
    clause "III.3.5" .iutIII "IUT III, Proposition 3.5"
      ["SourcePacketIntegralConstruction.logShellRegion",
        "SourcePacketIntegralConstruction.logShellRegion_eq_packetLattice",
        "SourcePacketIntegralConstruction.logShellRegion_eq_unitBall",
        "SourceNonarchimedeanLogShellDefinition.preLogShell_le_lattice",
        "SourceNonarchimedeanPacketUnitLogData",
        "SourceNonarchimedeanPacketUnitLogData.pureLogTensorOfUnitTuple",
        "SourceNonarchimedeanPacketUnitLogData.packetUnitLogSubgroup",
        "SourceNonarchimedeanPacketUnitLogData.packetUnitLogSubgroup_le_packetLattice",
        "SourceNonarchimedeanPacketLogLinkStep",
        "SourceNonarchimedeanPacketLogLinkStep.graph_le_packetUnitLogSubgroup_prod",
        "SourceNonarchimedeanPacketLogLinkStep.related_of_unitTuplesRelated",
        "SourceAbsoluteLGPVerticalFullLogLinks",
        "SourceAbsoluteLGPVerticalFullLogLinks.nonarchimedeanPacketStep",
        "SourceAbsoluteLGPVerticalFullLogLinks.archimedeanPacketStep",
        "SourceAbsoluteLGPVerticalFullLogLinks.toVerticalUpperSemiData",
        "SourceForwardRelation",
        "SourceForwardDomain", "SourceForwardRange",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketUnitLogSubgroup_image",
        "SourceLGPSplittingMonoidKummerIso",
        "SourceTheorem311CoricContainer",
        "SourceTheorem311Ind3System",
        "SourceArchimedeanPacketUnitData",
        "SourceArchimedeanPacketUnitData.summandSemiGermNeighborhoodSystem",
        "SourceArchimedeanPacketUnitData.UnitTuple.semiGermUnit",
        "SourceArchimedeanPacketUnitData.principalLogTensor_mem_unitBall",
        "SourceArchimedeanPacketLogLinkStep",
        "SourceTheorem311Ind3System.logShellRegion_eq_unitBall",
        "SourceTheorem311Ind3System.archLogIterateRelation",
        "SourceTheorem311Ind3System.archLogIterateDomain",
        "SourceTheorem311Ind3System.archLogIterateRange",
        "SourceTheorem311Ind3System.archLogBallPreimage_subset_logShellRegion",
        "SourceTheorem311Ind3System.archLogBall_relationally_surjective",
        "SourceTheorem311Ind3System.arch_direct_units_contained",
        "SourceTheorem311Ind3System.arch_direct_localBalls_contained",
        "SourceTheorem311BadPrimeLogKummerData",
        "SourceTheorem311BadPrimeLogKummerData.AdmissibleAcrossLog",
        "SourceTheorem311BadPrimeLogKummerData.logarithm_eq_of_admissibleAcrossLog",
        "SourceTheorem311VerticalLogLink.rootsOfUnity_logarithm_eq_zero",
        "SourceTheorem311VerticalLogLinkFamily.adjacent_logarithm_eq_on_overlap"]
      .partialImplementation
      "The vertically coric n-circle packet is fixed while m varies, and every m-packet has an actual tensor Kummer isomorphism into it. At finite places Lean constructs the fixed-unit log direct sums, generated tensor subgroup, adjacent correspondence graph, all positive iterates, and final Kummer containment. At infinite places the local radius-pi disk is correctly the unit ball of the pi-normalized Hermitian metric. Genuine circle units receive principal logarithms via arg*i; selecting one place per tensor factor gives direct-sum and pure-tensor representatives whose packet unit-ball membership is derived from the summand, direct-sum, and tensor metric equations. Each unit is canonically a point of an explicit projective system of open-annulus neighborhoods with restricted ambient holomorphic and group germs and a proved selected connected component. Adjacent finite and archimedean packet relations are now derived componentwise from Definition 1.1 full local log-links: equality of the source logarithm with an injectively realized target unit. The target is unique, but existence is not assumed, so the relation remains correctly partial. Lean recursively derives its domains and ranges, the participating endpoint-ball subset, and relational surjectivity back onto the source domain. Direct Kummer containment for both circle-unit tensors and arbitrary selected local radius-pi tensors follows from vertical transport of the full packet unit ball. At bad primes the compatibility object no longer accepts an arbitrary cross-log predicate: admissibility is derived from membership in the adjacent log-link domains and an explicit root-of-unity quotient in the next domain. The restricted Aut_hol assignment and groupification-induced rigidity are constructed; extending rigidity to arbitrary purely local group-germ automorphisms remains open. Constructing the full local log-links from IUT II Corollaries 4.5-4.6 and the Gaussian log-theta lattice, together with the bad-prime Kummer maps and overlap theorem, also remains open.",
    clause "III.3.7" .iutIII "IUT III, Proposition 3.7"
      ["IUTIIITheorem311ConstructedSource"] .unformalized
      "The cited vertical compatibility input is not formalized.",
    clause "III.3.8(iii)" .iutIII "IUT III, Definition 3.8(iii)"
      ["SourceLGPGaussianLogThetaLattice",
        "SourceLGPGaussianLogThetaLattice.horizontalThetaLink",
        "SourceLGPGaussianLogThetaLattice.verticalProcessionHom"]
      .partialImplementation
      "The LGP Gaussian log-theta lattice is an actual Z x Z family of distinct source Hodge theaters carried by F-theta bridges, with a shared mono-analyticization functor, horizontal theta-links, and vertically coric procession maps. Constructing the lattice from IUT II Gaussian data and proving all log-link structure remain open.",
    clause "III.3.9" .iutIII "IUT III, Proposition 3.9"
      ["SourceNormalizedLogVolume",
        "SourceSelectedPlace.moduliLocalDegree",
        "SourceSelectedPlace.moduliRationalLocalDegree",
        "SourceNormalizedLogVolume.AdmissibleRegion",
        "SourceNormalizedLogVolume.valueOn",
        "SourceNormalizedLogVolume.value",
        "SourceNormalizedLogVolume.Compatible",
        "SourceNormalizedLogVolume.Compatible.valueOn_mapRegion",
        "SourceNormalizedLogVolume.PacketNormalization",
        "SourceNormalizedLogVolume.PacketNormalization.valueOn_dilateRegion",
        "SourceNonarchimedeanLocalFieldIntegers",
        "SourceTopologicalLocalField.finitePlaceIntegerRing",
        "SourceTopologicalLocalField.finitePlaceIntegerRing_mem_iff_norm_le_one",
        "SourceTopologicalLocalField.finitePlaceIntegerRing_isCompact",
        "SourceTopologicalLocalField.finitePlaceIntegerRing_isOpen",
        "SourceNonarchimedeanLocalFieldIntegers.ofFinitePlace",
        "SourceNonarchimedeanLocalFieldIntegers.positiveCompacts",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedHaarMeasure",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedLogVolume",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedLogVolume_value_eq_zero",
        "ThetaFinitePlace.residueCharacteristic_eq_natGenerator",
        "SourceNonarchimedeanLocalFieldIntegers.rationalPrime",
        "SourceNonarchimedeanLocalFieldIntegers.rationalPrime_eq_residueCharacteristic",
        "SourceNonarchimedeanLocalFieldIntegers.rationalPrime_prime",
        "SourceNonarchimedeanLocalFieldIntegers.localDegree",
        "SourceNonarchimedeanLocalFieldIntegers.rationalPrimeScale",
        "SourceNonarchimedeanLocalFieldIntegers.RationalPrimeQuotient",
        "SourceNonarchimedeanLocalFieldIntegers.rationalPrimeQuotientModule",
        "SourceNonarchimedeanLocalFieldIntegers.padicScalarFieldMap",
        "SourceNonarchimedeanLocalFieldIntegers.continuous_padicScalarFieldMap",
        "SourceNonarchimedeanLocalFieldIntegers.padicScalarFieldMap_mem_integerRing",
        "SourceNonarchimedeanLocalFieldIntegers.padicScalarMap",
        "SourceNonarchimedeanLocalFieldIntegers.continuous_padicScalarMap",
        "SourceNonarchimedeanLocalFieldIntegers.padicFieldRingHom",
        "SourceNonarchimedeanLocalFieldIntegers.continuous_padicFieldRingHom",
        "SourceNonarchimedeanLocalFieldIntegers.padicScalarMap_coe_eq_padicFieldRingHom",
        "SourceNonarchimedeanLocalFieldIntegers.padicIntegerFieldRingHom",
        "SourceNonarchimedeanLocalFieldIntegers.padicFieldBasis",
        "SourceNonarchimedeanLocalFieldIntegers.eventually_padicPrime_pow_smul_basis_mem",
        "SourceNonarchimedeanLocalFieldIntegers.padicIntegralScaleExponent",
        "SourceNonarchimedeanLocalFieldIntegers.padicIntegralScaleExponent_spec",
        "SourceNonarchimedeanLocalFieldIntegers.scaledPadicFieldBasis",
        "SourceNonarchimedeanLocalFieldIntegers.scaledPadicFieldBasis_apply",
        "SourceNonarchimedeanLocalFieldIntegers.integralBasisVector",
        "SourceNonarchimedeanLocalFieldIntegers.padicBasisLattice",
        "SourceNonarchimedeanLocalFieldIntegers.padicBasisLattice_fg",
        "SourceNonarchimedeanLocalFieldIntegers.padicBasisLattice_isOpen",
        "SourceNonarchimedeanLocalFieldIntegers.integerAddSubgroupModuleFinite",
        "SourceNonarchimedeanLocalFieldIntegers.integerSubringModuleFinite",
        "SourceNonarchimedeanLocalFieldIntegers.isIntegral_iff_mem_integerRing",
        "SourceNonarchimedeanLocalFieldIntegers.padicIsIntegralClosure",
        "SourceNonarchimedeanLocalFieldIntegers.padicIntegralBasis",
        "SourceNonarchimedeanLocalFieldIntegers.PAdicIntegralClosure.coefficientReduction",
        "SourceNonarchimedeanLocalFieldIntegers.PAdicIntegralClosure.coefficientReduction_ker",
        "SourceNonarchimedeanLocalFieldIntegers.PAdicIntegralClosure.quotientLinearEquiv",
        "SourceNonarchimedeanLocalFieldIntegers.PAdicIntegralClosure.quotient_finrank_eq",
        "SourceNonarchimedeanLocalFieldIntegers.PAdicIntegralClosure.toRationalPrimeResidueModule",
        "SourceNonarchimedeanLocalFieldIntegers.RationalPrimeResidueModule",
        "SourceNonarchimedeanLocalFieldIntegers.RationalPrimeResidueModule.quotientFintype",
        "SourceNonarchimedeanLocalFieldIntegers.RationalPrimeResidueModule.quotient_card_eq",
        "SourceNonarchimedeanLocalFieldIntegers.ResidueQuotientFormula.residueCosets_cover_integerRing",
        "SourceNonarchimedeanLocalFieldIntegers.ResidueQuotientFormula.residueCosets_pairwiseDisjoint",
        "SourceNonarchimedeanLocalFieldIntegers.ResidueQuotientFormula.scaledRing_measure_eq_scale",
        "SourceNonarchimedeanLocalFieldIntegers.HaarDegreeFormula",
        "SourceNonarchimedeanLocalFieldIntegers.ResidueQuotientFormula.toHaarDegreeFormula",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedHaarMeasure_rationalPrimeDilation",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedLogVolume_admissible_rationalPrimeDilation",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedLogVolume_rawLogVolume_rationalPrimeDilation",
        "SourceNonarchimedeanLocalFieldIntegers.normalizedLogVolume_valueOn_rationalPrimeDilation",
        "SourcePacketMeasuredField.NonarchimedeanPrimeDilation",
        "SourcePacketMeasuredField.NonarchimedeanPrimeDilation.ofIntegers",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockFieldProductAdmissibleRegion",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockVolume_valueOn_blockFieldProductAdmissibleRegion",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization.factor_localDegree",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization.block_degree_sum",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization.stageDilation",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization.stageDilation_image_packetAdmissibleRegion",
        "SourcePacketFiniteStageLogVolume.DirectProductPrimeNormalization.valueOn_dilatedPacketAdmissibleRegion",
        "SourceArchimedeanLocalFieldModel",
        "SourceArchimedeanLocalFieldModel.nnrealLengthMeasure",
        "SourceArchimedeanLocalFieldModel.radialLengthMeasure",
        "SourceArchimedeanLocalFieldModel.complexNorm_image_integralRegion",
        "SourceArchimedeanLocalFieldModel.radialLengthMeasure_unitRadialInterval",
        "SourceArchimedeanLocalFieldModel.completedRadialLengthMeasure_image_integralRegion",
        "SourceArchimedeanLocalFieldModel.normalizedLogVolume",
        "SourceArchimedeanLocalFieldModel.normalizedLogVolume_value_eq_zero",
        "SourceArchimedeanLocalFieldModel.addCircleVolume_image_of_injOn",
        "SourceArchimedeanLocalFieldModel.realVolume_abs_image_of_injOn",
        "SourceArchimedeanLocalFieldModel.angularLengthMeasure",
        "SourceArchimedeanLocalFieldModel.angularLengthMeasure_univ",
        "SourceArchimedeanLocalFieldModel.angularLengthMeasure_mul_image",
        "SourceArchimedeanLocalFieldModel.complexAngularProjection",
        "SourceArchimedeanLocalFieldModel.continuous_complexAngularProjection",
        "SourceArchimedeanLocalFieldModel.AngularRegion",
        "SourceArchimedeanLocalFieldModel.AngularRegion.angularVolume_pos",
        "SourceArchimedeanLocalFieldModel.AngularRegion.angularVolume_lt_top",
        "SourceArchimedeanLocalFieldModel.AngularRegion.mulLeft",
        "SourceArchimedeanLocalFieldModel.AngularRegion.angularVolume_mulLeft",
        "SourceArchimedeanLocalFieldModel.AngularRegion.angularLogVolume_mulLeft",
        "SourceArchimedeanLocalFieldModel.ExponentialRegion",
        "SourceArchimedeanLocalFieldModel.ExponentialRegion.angularLengthMeasure_angularImage",
        "SourceArchimedeanLocalFieldModel.ExponentialRegion.completedRadialLengthMeasure_fieldCarrier_eq_angular",
        "SourceArchimedeanLocalFieldModel.ExponentialRegion.normalizedLogVolume_valueOn_eq_angularLogVolume",
        "SourceArchimedeanLocalFieldModel.packetScale",
        "SourceArchimedeanLocalFieldModel.nnrealLengthMeasure_packetScale",
        "SourceArchimedeanLocalFieldModel.radialLengthMeasure_packetScale",
        "SourceArchimedeanLocalFieldModel.radialization_image_packetDilation",
        "SourceArchimedeanLocalFieldModel.completedRadialLengthMeasure_packetDilation",
        "SourceArchimedeanLocalFieldModel.packetNormalization",
        "SourcePacketMeasuredField",
        "SourcePacketMeasuredField.ofNonarchimedean",
        "SourcePacketMeasuredField.ofArchimedean",
        "SourcePacketFiniteMeasuredFieldDecomposition",
        "SourcePacketFiniteMeasuredFieldDecomposition.BlockRadialCoordinates",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockRadializedRegion_integralRegion",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockProductMeasure_integralRegion",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockVolume",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockVolume_normalizationOffset_eq_zero",
        "SourcePacketFiniteMeasuredFieldDecomposition.blockVolume_value_eq_zero",
        "SourcePacketFiniteMeasuredFieldDecomposition.packetRadializedRegion_productRegion",
        "SourcePacketFiniteMeasuredFieldDecomposition.stageEmbedding_preimage_embeddedPacketIntegralRegion",
        "SourcePacketFiniteStageLogVolume",
        "SourcePacketFiniteStageLogVolume.weightChoiceEquiv",
        "SourcePacketFiniteStageLogVolume.weightChoice_card_factor",
        "SourcePacketFiniteStageLogVolume.normalizedReplicaSum_eq_inverseMultiplicitySum",
        "SourcePacketFiniteStageLogVolume.weightedLift_productRegion",
        "SourcePacketFiniteStageLogVolume.weightedContent_productRegion",
        "SourcePacketFiniteStageLogVolume.normalized_log_weightedContent_productRegion",
        "SourcePacketFiniteStageLogVolume.toNormalizedLogVolume",
        "SourcePacketFiniteStageLogVolume.toNormalizedLogVolume_valueOn_admissibleProductRegion_eq_weightedSum",
        "SourcePacketFiniteStageVolume",
        "SourcePacketFiniteStageVolume.normalizedLogVolume_value_eq_zero",
        "SourcePacketFiniteStageLogVolume.Compatible.blockRadial_measurePreserving",
        "SourcePacketFiniteStageLogVolume.Compatible.stageKummer_image_packetIntegralRegion",
        "SourcePacketFiniteStageLogVolume.Compatible.packetRadialEquiv_image_radializedRegion",
        "SourcePacketFiniteStageLogVolume.Compatible.replica_measurePreserving",
        "SourcePacketFiniteStageLogVolume.Compatible.replicaEquiv_image_weightedLift",
        "SourcePacketFiniteStageLogVolume.Compatible.weightedContent_image",
        "SourcePacketFiniteStageLogVolume.Compatible.toNormalizedLogVolume_compatible",
        "SourcePacketFiniteStageLogVolume.Compatible.normalizedLogVolume_value_eq",
        "SourceTheorem311LocalData.processionLogVolume",
        "SourceMonoAnalyticLogShellAlgorithm.transport_logVolume",
        "SourceTheorem311LocalData.logVolume"] .partialImplementation
      "Normalized log-volume is a functional on admissible regions, not generally the logarithm of a measure on packet space. The accepted field interface is indexed by genuine finite-stage local fields and models a complete measurable extension containing the Borel sets. At a finite component, the integer ring is the norm unit ball and is compact-open; for a canonical finite-place field it is now definitionally the valuation subring of the actual completion, and the norm bound, compactness, and openness are proved from the completion. It derives normalized additive Haar measure, its completion, the full measurable finite-region log-volume, and zero volume of the integer ring, as in Topics in Absolute Anabelian Geometry III, Proposition 5.7(i)(a). The rational prime is proved equal to both the height-one-prime generator and the residue characteristic. Mathlib's continuous equivalence between the rational adic completion and Q_p is transported through the actual continuous local-field algebra map. Continuity plus density of the natural numbers in Z_p proves that this map lands in the closed norm-unit ball O_L; no norm-nonincreasing algebra assumption is used. Its Z_p restriction is proved equal to the canonical continuous map Z_p -> O_L, and the transported Q_p basis retains the actual local degree. Powers of p acting through the continuous Q_p-action put a scaled basis inside O_L. Its finite Z_p-span is open by a coordinate unit-ball neighborhood; compactness of O_L makes the quotient finite, hence O_L is module-finite over Z_p. A monic-polynomial valuation argument proves that an element is integral over Z_p exactly when it lies in O_L, yielding the canonical integral-closure theorem. Mathlib's integral-closure theorems then derive finite generation, freeness, rank [L:Q_p], and the integral basis; no basis is accepted as presentation data. Following Proposition 5.7(i), the actual additive quotient O_L/pO_L carries a canonical F_p = ZMod p module action. Coefficientwise reduction is proved surjective with kernel pO_L and yields a linear equivalence O_L/pO_L = (F_p)^[L:Q_p]. Thus the quotient finrank, Fintype instance, and p^[L:Q_p] cardinality are derived, followed by the finite coset cover, pairwise disjointness, equal translated masses, mass p^(-[L:Q_p]) of pO_L, and the distributive Haar character. Consequently the raw Haar scaling, preservation of the complete admissible domain, and the exact negative-local-degree-times-log-p shift are proved without assuming the measure formula. The E/W layer constructs explicit field, tensor-block, and packet-stage dilations on the direct-product regions singled out in Remark 3.1.1(iii). Every local-field tower now carries one coherent continuous algebra action. A Q_(v_Q)-linear tensor presentation proves that a stage has dimension equal to the product of its factor degrees; its algebra decomposition proves that the same dimension is the sum of the degrees of the actual field summands. Each factor carries an actual local-field tower Q_(v_Q) subset (F_mod)_v subset K_v, and finrank multiplicativity derives the factor degree formula. Thus the tensor-block degree identity is a theorem, and the E/W calculation proves that division by each N_v and the final denominator cancel all local degrees, leaving exactly -log(p). At an infinite component, a complex local-field model derives complex-norm radialization, completed radial length, and zero normalized log-volume. Angular length is transported from Haar length on AddCircle(2*pi), has total mass 2*pi, and is proved invariant under circle rotation. The polar projection from the actual multiplicative group C-times is a continuous monoid homomorphism. The source domain M-check(k) is implemented as nonempty compact regions whose angular projection is the closure of its interior; its angular volume is positive and finite, multiplication by every x in k-times preserves the domain, and both angular volume and angular log-volume are invariant. This derives the angular assertion of Proposition 5.7(ii)(b). A decomposition over every translated fundamental interval proves length preservation without imposing a single exponential branch; radial absolute-value preservation, admissibility, and the exact radial/angular log-volume identity then derive Proposition 5.7(ii)(c). Multiplication by e is an actual transported field-carrier equivalence whose completed-length scaling law and unit log shift derive the radial portion of Proposition 5.7(ii)(b) and IUT III Proposition 3.9(i). For each outer place tuple v, M_v, its integral block, and its product measure are derived fieldwise. The outer E/W construction derives E, E_{not v}, W, M_V, M_W, S_E, mu_E, and the exact reciprocal-weight formula. A finite-stage Proposition 3.2 poly-isomorphism equipped only with fieldwise measure preservation derives preservation of block products, S_E, mu_E, admissibility, the complete normalized functional, its integral value, and the embedded packet integral region. This finite-stage functional supplies the local-data, vertical-container, and Ind3 path; the legacy arbitrary block calculation is non-accepting. Instantiating every tower field and weight with the canonical selected-place completion constructors, constructing their measured-field identifications, extending the explicit packet dilation beyond direct-product regions, constructing both local-field models from the log-shells and field presentations, and proving the mono-analytic adjustment and global product-formula comparison remain open.",
    clause "III.3.10" .iutIII "IUT III, Proposition 3.10"
      ["SourceKappaLocalizationDiagram",
        "SourceKappaLocalizationDiagramIso",
        "SourceTheorem311LabeledData",
        "SourceTheorem311LabeledKummerIso"] .partialImplementation
      "The labeled kappa-solvable/global M-infinity-kappa objects are actual topological group/pseudo-monoid action pairs, not total-monoid surrogates or collapsed profinite groups. Their localization diagrams retain every selected-place local M-infinity-kappa object, its topologically embedded inclusion into M-infinity-kappa-times, and both naturality squares under vertical Kummer transport. Number fields and all four non-realified/realified MOD/mod split-Frobenioids are also source-shaped objects, and both MOD/mod comparison routes carry natural isomorphisms. Constructing these data from the cited Kummer and localization algorithms and proving the mutual log-link compatibility distinction between MOD and mod remain open.",
    clause "III.3.11.setup" .iutIII "IUT III, Theorem 3.11: setup"
      ["SourceAbsoluteLGPGaussianLogThetaLattice",
        "SourceAbsoluteLGPGaussianLogThetaLattice.commonMonoAnalyticProcession",
        "SourceAbsoluteLGPGaussianLogThetaLattice.capsuleAtLabel",
        "SourceAbsoluteLGPGaussianLogThetaLattice.packetIndexEquiv",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalProcessionHomToCommonMember",
        "SourceAbsoluteLGPGaussianLogThetaLattice.localPacket",
        "SourceTheorem311ColumnBoundary"]
      .partialImplementation
      "The setup uses an actual Z x Z collection of distinct Hodge theaters and full absolute-label F-theta bridges. Every site has a compatible member to a fixed n-circle bridge, giving the correct l-plus-minus mono-analytic procession; the capsule at |j| has j+1 factors and constructs the local packet. The older nonzero l-star lattice is explicitly excluded from source constructions. Constructing the lattice and all coricity members from the preceding IUT II Gaussian data remains open.",
    clause "III.3.11(i).objects" .iutIII "IUT III, Theorem 3.11(i): processions and objects"
      ["SourceAbsoluteLGPGaussianLogThetaLattice.monoAnalyticProcession",
        "SourceAbsoluteLGPGaussianLogThetaLattice.commonMonoAnalyticProcession",
        "SourceTheorem311LocalData",
        "SourceLGPSplittingMonoidAction",
        "SourceTheorem311LabeledData",
        "SourceTheorem311MultiradialPresentation",
        "SourceTheorem311MultiradialPresentation.AuxiliaryRealization",
        "SourceAbsoluteLGPGaussianLogThetaLattice.PresentationConstruction",
        "SourceAbsoluteLGPGaussianLogThetaLattice.PresentationConstruction.toMultiradialPresentation",
        "SourceTheorem311ColumnBoundary.procession",
        "SourceTheorem311ColumnBoundary.localData",
        "SourceTheorem311ColumnBoundary.presentation"] .partialImplementation
      "The complete unquotiented presentation is assembled on the full absolute-label procession from actual tensor packets, integral structures, measured log-volumes, the literal bad-place fiber, splitting actions on distinguished submodules, jointly embedded number fields, and all four split-Frobenioid families. The column boundary forces the horizontal presentation and vertical family to share one definitionally identical common local construction. Constructing its labeled and splitting inputs functorially from the preceding paper propositions remains open.",
    clause "III.3.11(i).Ind1" .iutIII "IUT III, Theorem 3.11(i): Ind1"
      ["CategoryCapsule.FullMemberMorphism",
        "CategoryProcession.MemberHom",
        "CategoryProcession.MemberHom.componentSelf",
        "CategoryProcession.MemberAutomorphismGroup",
        "SourceMonoAnalyticLogShellAlgorithm.factorTransport_comp",
        "SourceMonoAnalyticLogShellAlgorithm.TensorTopology.reindexLinearEquiv_trans",
        "SourceMonoAnalyticLogShellAlgorithm.packetMemberTransport",
        "SourceMonoAnalyticLogShellAlgorithm.packetMemberTransport_id",
        "SourceMonoAnalyticLogShellAlgorithm.packetMemberTransport_comp",
        "SourceMonoAnalyticLogShellAlgorithm.packetInd1Action",
        "SourceTheorem311Ind1Action",
        "SourceTheorem311Ind1Action.ofProcessionFunctor",
        "SourceAbsoluteLGPGaussianLogThetaLattice.localInd1PacketAction",
        "SourceAbsoluteLGPGaussianLogThetaLattice.LocalConstruction.toLocalInd1Action",
        "SourceTheorem311MultiradialPresentation.ind1Action",
        "SourceAbsoluteLGPGaussianLogThetaLattice.PresentationConstruction.toInd1Action",
        "SourceTheorem311MultiradialAlgorithm",
        "SourceTheorem311MultiradialAlgorithm.ind1Action",
        "SourceTheorem311ColumnBoundary.ind1Action",
        "SourceTheorem311ColumnBoundary.quotient_sound_ind1",
        "SourceTheorem311MultiradialAlgorithm.Quotient",
        "sourceTheorem311IndeterminacySetoid",
        "SourceTheorem311IndeterminacyQuotient"] .partialImplementation
      "Ind1 uses the automorphism group of the member-carrying procession category: every group element retains the component D-tilde-prime-strip isomorphisms needed to transport log shells. Strictly monotone procession endomorphisms fix every label position. Their within-capsule permutations and component isomorphisms induce functorial continuous transports of the actual direct sums and literal tensor packets, with identity and composition proved from log-shell functoriality. This yields the actual action on every packet, the dependent product of all places and labels, and the full presentation with auxiliary coordinates fixed; the exact quotient is generated jointly with Ind2. Constructing the complete presentation functor on arbitrary source processions, and constructing all local, splitting, and labeled inputs from the preceding paper propositions, remain open.",
    clause "III.3.11(i).Ind2" .iutIII "IUT III, Theorem 3.11(i): Ind2"
      ["SourceNonarchimedeanLogShellSymmetryCore.Ism",
        "SourceNonarchimedeanLogShellSymmetryCore.ismAction",
        "SourceArchimedeanLogShellSymmetry",
        "SourceMonoAnalyticLogShellAlgorithm.ind2ActionAbove",
        "SourceMonoAnalyticTensorPacket.Ind2CoordinateIndex",
        "SourceMonoAnalyticTensorPacket.ind2CoordinateIndex_card",
        "SourceTheorem311Ind2SummandAction.packetAction_on_tensor",
        "SourceTheorem311Ind2Action",
        "SourceTheorem311LocalInd2Action",
        "SourceTheorem311LocalInd2Action.action",
        "SourceAbsoluteLGPGaussianLogThetaLattice.localInd2Action",
        "SourceAbsoluteLGPGaussianLogThetaLattice.LocalConstruction.toLocalInd2Action",
        "SourceTheorem311ColumnBoundary.localInd2Action",
        "SourceTheorem311ColumnBoundary.ind2Action",
        "SourceTheorem311ColumnBoundary.quotient_sound_ind2"] .partialImplementation
      "Every packet summand now receives the source group from its actual log shell: nonarchimedean Ism consists of G-equivariant continuous automorphisms preserving every open-subgroup lattice, while archimedean places use independent order-two sign choices. The direct-sum, genuine PiTensorProduct, and complete local-family actions and their laws are derived. Constructing the log-shell symmetry inputs, including compactness and continuity proofs, from Proposition 1.2 and IUT II Example 1.8 remains open.",
    clause "III.3.11(i).functoriality" .iutIII "IUT III, Theorem 3.11(i): permutation and bi-coric functoriality"
      ["SourceDThetaBridgeCore.IsomorphismMember.monoAnalyticProcessionObjectIso",
        "SourceTheorem311TwoActionEquivalence.quotientEquiv",
        "SourceTheorem311PermutationBiCoricCompatibility",
        "SourceTheorem311PermutationBiCoricCompatibility.quotientEquiv"]
      .partialImplementation
      "A bi-coric bridge member induces an actual procession isomorphism. Equivariance for both Ind1 and Ind2 is proved to preserve the generated relation in both directions and hence induces the required quotient equivalence. Constructing the bi-coric member and equivariance from the source etale-picture permutation remains open.",
    clause "III.3.11(ii).Kummer" .iutIII "IUT III, Theorem 3.11(ii): vertical Kummer isomorphisms"
      ["SourceTensorPacketKummerIso",
        "SourceMonoAnalyticLogShellAlgorithm.tensorPacketKummerIso",
        "SourceAbsoluteLGPGaussianLogThetaLattice.siteLocalPacket",
        "SourceAbsoluteLGPGaussianLogThetaLattice.SitePacketIntegralConstruction",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalStripIsoToCommon",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketKummerIso",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalSummandLattice_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFactorLattice_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPureIntegralTensors_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketLattice_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFactorUnitLogSubgroup_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPureUnitLogTensors_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketUnitLogSubgroup_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedLattice_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFullNonarchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedNonarchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalSummandSeminorm_compatible",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalSummandInner_compatible",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFactorInner_compatible",
        "SourceTensorPacketKummerIso.packetInner_compatible",
        "SourceTensorPacketKummerIso.packetSeminorm_compatible",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketInner_compatible",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketSeminorm_compatible",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFullArchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedArchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFullIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedIntegral_image",
        "SourcePacketFiniteStageVolume",
        "SourcePacketFiniteStageLogVolume.Compatible",
        "SourcePacketFiniteStageLogVolume.Compatible.blockRadial_measurePreserving",
        "SourcePacketFiniteStageLogVolume.Compatible.packetRadialEquiv_image_radializedRegion",
        "SourcePacketFiniteStageLogVolume.Compatible.replica_measurePreserving",
        "SourcePacketFiniteStageLogVolume.Compatible.weightedContent_image",
        "SourcePacketFiniteStageLogVolume.Compatible.toNormalizedLogVolume_compatible",
        "SourcePacketFiniteStageLogVolume.Compatible.packetKummer_image_embeddedPacketIntegralRegion",
        "SourceAbsoluteLGPGaussianLogThetaLattice.VerticalLocalConstruction.toTheorem311VerticalLocalKummer",
        "SourceTheorem311VerticalLocalKummer",
        "SourceTheorem311ColumnBoundary.verticalLocalKummer",
        "SourceTheorem311ColumnBoundary.vertical_logVolume_compatible",
        "SourceTheorem311LabeledKummerIso"] .partialImplementation
      "For every actual `(n,m)` absolute-label capsule, vertical coricity constructs the placewise, direct-sum, and continuous tensor-packet Kummer maps to the fixed `(n,circle)` packet. Finite-place transport passes through shell lattices, tensor generation, closure, distinguished intersections, and the generated tensor subgroup of invariant-unit logarithms; infinite-place transport preserves the rationalized packet seminorm. Full and distinguished ind-packet region images hold for both place kinds. Separately, each packet carries a genuine finite-stage field presentation. The Kummer place map reindexes its field stages, and fieldwise radial measure preservation derives transport of E, W, M_W, weighted lifts, weighted content, the normalized functional, and the embedded finite-stage integral product. The local-data, vertical-container, and Ind3 APIs use this finite-stage path and expose no legacy whole-packet decomposition. Labeled vertical Kummer data now preserve the complete Corollary 4.8 localization diagram of action pairs. Constructing the summand unit/log data, field-stage radial maps, and labeled localization/Frobenioid maps from the cited paper algorithms remains open.",
    clause "III.3.11(ii).objects" .iutIII "IUT III, Theorem 3.11(ii): tensor and Frobenioid compatibility"
      ["SourceTensorPacketKummerIso.distinguishedSubmodule_map",
        "SourceMonoAnalyticLogShellAlgorithm.TensorTopology.congr_distinguishedSubmodule",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFullNonarchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedNonarchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalFullArchimedeanIntegral_image",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalDistinguishedArchimedeanIntegral_image",
        "SourceTheorem311VerticalLocalKummer.fullIntegral_image",
        "SourceTheorem311VerticalLocalKummer.distinguishedIntegral_image",
        "SourceLGPSplittingMonoidKummerIso",
        "SourceTheorem311LabeledKummerIso",
        "SourceTheorem311ColumnBoundary.siteSplitting",
        "SourceTheorem311ColumnBoundary.labeledKummer",
        "SourceTheorem311ColumnBoundary.badPrimeLogKummer"] .partialImplementation
      "Distinguished-submodule compatibility is derived from equality of generating pure-tensor sets and `map_span`. Finite-place full and distinguished integral-region compatibility is derived from the actual log-shell lattices, including both closures. Infinite-place full and distinguished integral-region compatibility is derived from transported Hermitian pairings on arbitrary packet tensors. The assembled column boundary requires each site splitting action, its Kummer maps, a multiplicative realization of its actual unit group in the vertical log-link domain, and the roots-only adjacent-overlap theorem, but accepts no arbitrary bad-prime relation. Its labeled Kummer input preserves the global and every local arrow of the Corollary 4.8 localization diagram, as well as the number-field and Frobenioid maps against the same common presentation. Constructing these inputs from IUT II Corollaries 4.6 and 4.8, together with the MOD/mod comparison squares, remains open.",
    clause "III.3.11(ii).logLink" .iutIII "IUT III, Theorem 3.11(ii): mutual log-link compatibility"
      ["SourceTheorem311VerticalLogLink",
        "SourceTheorem311VerticalLogLink.DiffersByRootOfUnity",
        "SourceTheorem311VerticalLogLink.logarithm_eq_of_differsByRootOfUnity",
        "SourceTheorem311VerticalLogLinkFamily.adjacent_logarithm_eq_on_overlap",
        "SourceTheorem311VerticalLogLinkFamily.adjacent_logarithm_eq_of_differsByRootOfUnity",
        "SourceTheorem311ColumnBoundary.badPrime_logarithm_eq"]
      .partialImplementation
      "A multiplicative log-link into an actual rational module kills every root of unity. Bad-prime cross-log admissibility is the derived conjunction of current-domain membership, adjacent-overlap membership, next-domain membership, and an explicit root-of-unity quotient lying in the next domain; it is no longer an arbitrary predicate with proof fields. Admissible values have equal additive logarithms. Proving the overlap criterion from Propositions 3.5 and 3.10 and deriving the MOD comparison remain open.",
    clause "III.3.11(ii).Ind3" .iutIII "IUT III, Theorem 3.11(ii): Ind3 and log-volume"
      ["SourcePacketIntegralConstruction.logShellRegion",
        "SourcePacketIntegralConstruction.logShellRegion_eq_unitBall",
        "SourceNonarchimedeanPacketUnitLogData.packetUnitLogSubgroup_le_packetLattice",
        "SourceNonarchimedeanPacketLogLinkStep",
        "SourceForwardRelation",
        "SourceAbsoluteLGPGaussianLogThetaLattice.siteNonarchimedeanUnitLogData",
        "SourceAbsoluteLGPGaussianLogThetaLattice.verticalPacketUnitLogSubgroup_image",
        "SourceTheorem311CoricContainer",
        "SourceTheorem311Ind3System",
        "SourceTheorem311Ind3System.nonarchLogIterateRelation",
        "SourceTheorem311Ind3System.nonarchLogIterateDomain",
        "SourceTheorem311Ind3System.nonarchLogIterateRange",
        "SourceTheorem311Ind3System.nonarch_logKummer_contained",
        "SourceTheorem311Ind3System.nonarch_logKummer_contained_of_mem_range",
        "SourceTheorem311Ind3System.logShellRegion_eq_unitBall",
        "SourceAutHolomorphicSemiGerm.neighborhoodSystem",
        "SourceAutHolomorphicSemiGerm.iInter_neighborhood_eq_unitCircle",
        "SourceAutHolomorphicSemiGerm.exists_neighborhood_subset_of_mem",
        "SourceAutHolomorphicSemiGerm.innerSide_eq_connectedComponentIn",
        "SourceArchimedeanPacketUnitData.UnitTuple.semiGermUnit",
        "SourceTheorem311Ind3System.archLogIterateRelation",
        "SourceTheorem311Ind3System.archLogIterateDomain",
        "SourceTheorem311Ind3System.archLogIterateRange",
        "SourceTheorem311Ind3System.archLogBallPreimage_subset_logShellRegion",
        "SourceTheorem311Ind3System.archLogBall_relationally_surjective",
        "SourceTheorem311Ind3System.arch_direct_units_contained",
        "SourceTheorem311Ind3System.arch_direct_localBalls_contained",
        "SourcePacketFiniteStageVolume",
        "SourcePacketFiniteStageLogVolume.Compatible.normalizedLogVolume_value_eq",
        "SourceAbsoluteLGPGaussianLogThetaLattice.VerticalFamilyConstruction",
        "SourceAbsoluteLGPGaussianLogThetaLattice.VerticalUpperSemiData",
        "SourceAbsoluteLGPVerticalFullLogLinks.toVerticalUpperSemiData",
        "SourceAbsoluteLGPGaussianLogThetaLattice.VerticalFamilyConstruction.toTheorem311Ind3System",
        "SourceTheorem311ColumnBoundary.verticalUpperSemi",
        "SourceTheorem311ColumnBoundary.ind3System",
        "SourceTheorem311ColumnBoundary.ind3_logVolume_independent",
        "SourceTheorem311Ind3System.logVolume_eq_common",
        "SourceTheorem311Ind3System.logVolume_eq_logVolume"]
      .partialImplementation
      "Ind3 is expressed relative to one fixed vertically coric n-circle container. A concrete vertical family derives every packet, direct Kummer isomorphism, integral-region image, finite-stage volume, normalized functional, and source log-shell region. At finite places it derives the genuine invariant-unit tensor subgroup, adjacent graph, every positive iterate, the m-r to m equation, and Kummer containment. At infinite places the Definition 1.1 radius-pi disk is the unit ball of the pi-normalized Hermitian metric. Actual circle units, their arg*i principal logarithms, selected-place direct sums, and pure tensors are constructed. The units are canonically promoted to the exact S1 core of an antitone open-annulus projective system whose restricted Aut_hol group assignment, ambient group germs, and selected connected component are constructed. For groupification-induced holomorphic automorphisms, the exponential-cover classification proves the selected-side-preserving semi-germ is the identity. The column boundary no longer accepts VerticalUpperSemiData: it accepts full selected-place log-links and derives the finite and archimedean packet relations, then every iterate, domain/range, endpoint-ball subset, relational surjectivity, containment, and vertical normalized-value independence. Extending rigidity to every purely local group-germ automorphism remains open, as do construction of the full local log-links from Psi_cns and the Gaussian log-theta lattice, the Galois-invariant tensor actions, and the remaining bad-prime data.",
    clause "III.3.11(iii).horizontal" .iutIII "IUT III, Theorem 3.11(iii): horizontal theta link"
      ["SourceFPrimeStripHom.NaturallyIsomorphic",
        "sourceFPrimeStripHomSetoid",
        "SourceFPrimeStripFullPolyIsomorphism",
        "SourceFPrimeStripFullPolyIsomorphism.comp_assoc",
        "SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc",
        "SourceFTimesMuPrimeStripFullPolyIsomorphism",
        "SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism",
        "SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism.comp_assoc",
        "SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc",
        "SourceFPrimeStripPolyIsomorphismSquare",
        "SourceFPrimeStripPolyIsomorphismSquare.upperToLower",
        "SourceFPrimeStripPolyIsomorphismSquare.lowerToUpper",
        "SourceIndexedHorizontalKummerSquare",
        "SourceIndexedHorizontalKummerSquare.toArrowCompatibility",
        "SourceTheorem311TrianglePrimeStripSquare",
        "SourceTheorem311EnvironmentPrimeStripFamily",
        "SourceTheorem311EnvironmentPrimeStripSquare",
        "SourceTheorem311EnvironmentPrimeStripSquare.ofTriangle",
        "SourceFTimesMuPrimeStripPolyIsomorphismSquare",
        "SourceTheorem311TimesMuPrimeStripFamily",
        "SourceTheorem311TimesMuPrimeStripConstruction",
        "SourceTheorem311TimesMuPrimeStripConstruction.toFamily",
        "SourceTheorem311TimesMuPrimeStripConstruction.thetaLink_full",
        "SourceTheorem311TimesMuPrimeStripConstruction.toCommon",
        "SourceTheorem311TimesMuPrimeStripConstruction.fromCommon",
        "SourceTheorem311TimesMuPrimeStripConstruction.toTriangleSquare",
        "SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily",
        "SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily.toTimesMu",
        "SourceTheorem311TimesMuTrianglePrimeStripSquare",
        "SourceTheorem311EnvironmentTimesMuPrimeStripFamily",
        "SourceTheorem311EnvironmentTimesMuPrimeStripSquare",
        "SourceTheorem311EnvironmentTimesMuPrimeStripSquare.ofTriangle",
        "SourceMonoThetaProjectiveSystemIso",
        "SourceTheorem311MonoThetaProjectiveSystemFamily",
        "SourceTheorem311MonoThetaProjectiveSystemSquare",
        "SourceKappaLocalizationDiagram",
        "SourceKappaLocalizationDiagramIso",
        "SourceKappaLocalizationDiagramIso.localizationSquare",
        "SourceKappaLocalizationDiagramIso.inclusionSquare",
        "SourceTheorem311LabeledHorizontalKummerSquare",
        "SourceTheorem311LabeledHorizontalKummerSquare.localizationAutomorphismEquiv",
        "SourceTheorem311LabeledHorizontalKummerSquare.inclusionAutomorphismEquiv",
        "SourceTheorem311HorizontalCorridorBoundary",
        "SourceTheorem311HorizontalCorridorBoundary.horizontalThetaLink",
        "SourceTheorem311HorizontalCorridorBoundary.right_theater_eq",
        "SourceTheorem311HorizontalCorridorBoundary.primeStripClauseA_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.environmentPrimeStripClauseB_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.monoThetaClauseC_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.siteKappaClauseD_localization_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.siteKappaClauseD_inclusion_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.commonKappaClauseD_localization_commutes",
        "SourceTheorem311HorizontalCorridorBoundary.commonKappaClauseD_inclusion_commutes"]
      .partialImplementation
      "The active boundary is an adjacent-column corridor, not a field of one column. It proves that the columns use the same lattice and have indices n and n+1. Following IUT I Section 0, the ordinary F, mono-analytic F, and Definition 4.9 F-turnstile-times-mu full poly-isomorphisms are quotients of all complete componentwise equivalence maps by structured natural isomorphism, not strict categorical Iso records. Clauses (a) and (b) use only times-mu corners computed by one reconstruction algorithm. The corridor accepts neither a clause (a) square, a chosen theta-link class, an arbitrary quotient-level fullness witness, nor chosen Kummer maps. Representative-level reconstruction fullness, scoped to every actual adjacent site pair, proves surjectivity onto every horizontal times-mu class. Certified two-sided model comparisons derive the canonical horizontal and Theorem 1.5 Kummer members and both cancellation laws. Lean maps these data through reconstruction, defines the lower horizontal class by Kummer conjugation, and proves commutativity and both directions of full-poly compatibility; clause (b) is then derived by environment conjugation. Constructing the local pairwise reconstruction fullness and coherent model comparisons from the preceding local theorems remains open. Clause (c) is still supplied as a square of actual mono-theta projective systems for every m and selected bad place. Clause (d) no longer uses a collapsed kappa-sol/M-infinity-kappa profinite square: every site/common label carries the complete Corollary 4.8 localization diagram of topological group/pseudo-monoid action pairs, all selected-place localization and topologically embedded inclusion arrows, horizontal naturality, vertical Kummer naturality, and diagram-level site/common coherence. The two arrow-category squares derive equivariance under arbitrary automorphisms. Constructing these horizontal diagrams from the permutation symmetry/cyclotomic-rigidity algorithms and proving evaluation equivariance up to Ind1-Ind3 remain open.",
    clause "III.3.11(iii).equivariance" .iutIII "IUT III, Theorem 3.11(iii): automorphism equivariance"
      ["SourceIndexedHorizontalKummerSquare.automorphismEquiv",
        "SourceTheorem311HorizontalEvaluationCompatibility",
        "SourceTheorem311HorizontalEvaluationCompatibility.descend"]
      .partialImplementation
      "An arrow isomorphism transports the full automorphism group, and evaluations satisfying the three generator laws descend to the exact Ind1-Ind3 quotient. Proving these laws for every prime-strip, mono-theta-environment, Kummer, Frobenioid, and evaluation construction in clauses (a)-(d) remains open.",
    clause "III.3.11.1(iii)" .iutIII "IUT III, Remark 3.11.1(iii): IPL and SHE"
      ["IUTIIITheorem311ConstructedSource"] .unformalized
      "The Ind1-permutation and simultaneous-holomorphic-envelope algorithms are not formalized.",
    clause "III.3.11.1(iv)" .iutIII "IUT III, Remark 3.11.1(iv): APT"
      ["IUTIIITheorem311ConstructedSource"] .unformalized
      "The alien-prime transport algorithm is not formalized.",

    clause "EtTh.2.pre-2.1" .etaleTheta
      "Etale Theta, construction preceding Definition 2.1"
      ["EtaleTheta.ThetaQuotient", "EtaleTheta.ModLThetaQuotient",
        "EtaleTheta.ModLEllipticAbelianization",
        "EtaleTheta.ArithmeticThetaQuotientData",
        "EtaleTheta.ArithmeticEllipticQuotientData",
        "EtaleTheta.OncePuncturedEllipticThetaRealization",
        "EtaleTheta.ProfiniteLagrangianQuotient"] .partialImplementation
      "The lower-central and exponent-l theta quotient, its rank-two arithmetic elliptic quotient, the cuspidal sequence, and the continuous Lagrangian quotient are distinct and linked by exact maps. Deriving the rank equivalences from geometric freeness and realizing the groups by orbicurve covers remain open.",
    clause "EtTh.2.1" .etaleTheta "Etale Theta, Definition 2.1"
      ["EtaleTheta.TypeOneLTorsionQuotient",
        "EtaleTheta.ProfiniteLagrangianQuotient",
        "OrbicurveSignAction", "OrbicurveSignQuotientWitness",
        "GlobalLTorsionCoverInput",
        "TypeOneLTorsionStackRealization",
        "TypeOneCuspidalAtlas"]
      .partialImplementation
      "The quotient has the source subgroup properties and open kernel; the cover/sign-quotient stacks, coherent invariant map, bicategorical quotient, full two-pullback, sign action on fundamental groups, and complete Q/sign-orbit cusp atlas are explicit with the arithmetic cover group fixed by that kernel. Derivation as finite-etale compactified orbicurve covers remains open.",
    clause "EtTh.2.2" .etaleTheta "Etale Theta, Proposition 2.2"
      ["EtaleTheta.InversionEigenspaceSplitting",
        "EtaleTheta.ArithmeticEllipticConjugationAction",
        "EtaleTheta.InversionEigenspaceSplitting.negativeSection",
        "EtaleTheta.ThetaRootSplittingData",
        "EtaleTheta.ThetaRootSplittingData.quotientByNegativeEigenspaceEquivCusp",
        "NormalizesProfiniteEmbeddingImage",
        "ThetaRootStackRealization"]
      .partialImplementation
      "The rank-two arithmetic elliptic quotient is separated from the class-two theta quotient. Its direct-product (-1)/(+1) eigenspace decomposition, actual conjugation compatibility, derived s_iota section, cusp quotient, Galois splitting, theta-root subgroup, and quotient equivalence are exact interfaces. The stack realization records the normalizing order-two lift, its unique admissible coset criterion, actual conjugation action, and generation statement of Proposition 2.2(iii). Constructing these witnesses from the source geometry remains open.",
    clause "EtTh.2.3" .etaleTheta "Etale Theta, Definition 2.3"
      ["EtaleTheta.ThetaRootSplittingData.thetaRootSubgroup",
        "GlobalLTorsionCoverInput.thetaRoot",
        "ThetaRootStackRealization",
        "SourceThetaBadLocalThetaRootStackRealization"] .partialImplementation
      "The fundamental-group subgroup associated to a splitting of the cuspidal decomposition group is derived and proved open. Global and bad-local type-(1,l-torsTheta) stack realization interfaces include sign quotient, full two-pullback, arithmetic-group identification, and both open inclusions. Construction and finite-etale representability from Proposition 2.2 remain open.",
    clause "EtTh.2.5(i)" .etaleTheta "Etale Theta, Definition 2.5(i)"
      ["EtaleTheta.profiniteTateGroup",
        "EtaleTheta.TateFactorizedLagrangian",
        "EtaleTheta.CuspidalSignStructure",
        "EtaleTheta.SignCompatibleThetaRootSplitting",
        "EtaleTheta.canonicalTateSignLabel",
        "SourceThetaBadLocalStandardData",
        "SourceThetaBadLocalThetaRootStackRealization"] .partialImplementation
      "The Tate direction is the actual profinite completion of Z, the local Lagrangian map factors through canonical reduction mod l, the cuspidal involution fixes inertia and the Galois quotient, and the selected splitting is invariant. The bad cusp is the localized global cuspidal decomposition datum, and its derived label is proved to be the sign orbit of 1. A source-shaped local theta-root stack realization is present; its source construction, finite-etale representability, and tempered-characteristic consequences remain open." ]

/-- Paper clauses currently claimed to be source-faithful. -/
def sourceFaithfulClauseIds : List String :=
  m1m3PaperLedger.filterMap fun entry =>
    if entry.status = .sourceFaithful then some entry.id else none

/-- Clause identifiers at a particular implementation status. -/
def clauseIdsWithStatus (status : ClauseStatus) : List String :=
  m1m3PaperLedger.filterMap fun entry =>
    if entry.status = status then some entry.id else none

/-- The source-closure ledger contains 114 separately audited clauses. -/
theorem m1m3PaperLedger_count : m1m3PaperLedger.length = 114 :=
  rfl

/-- No source clause occurs twice in the direct-citation ledger. -/
theorem m1m3PaperLedger_ids_nodup :
    (m1m3PaperLedger.map PaperClause.id).Nodup := by
  decide

/-- Eighty-eight clauses currently have a genuine but incomplete implementation. -/
theorem partialImplementation_count :
    (clauseIdsWithStatus .partialImplementation).length = 88 :=
  rfl

/-- Four clauses currently point only to explicitly classified toy models. -/
theorem toyModel_count :
    (clauseIdsWithStatus .toyModel).length = 4 :=
  rfl

/-- Sixteen source-closure clauses remain wholly unformalized. -/
theorem unformalized_count :
    (clauseIdsWithStatus .unformalized).length = 16 :=
  rfl

/-- Six clauses currently pass the clause-level source audit. -/
theorem sourceFaithfulClauseIds_eq :
    sourceFaithfulClauseIds =
      ["FrdI.2.7", "FrdI.4.4", "FrdI.5.2(i)", "FrdI.5.2(ii)",
        "I.0.pseudo-monoid", "I.4.10"] :=
  rfl

end Iut.SourceTrace
