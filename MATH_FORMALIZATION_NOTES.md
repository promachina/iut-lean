# Math Formalization Notes

Date started: 2026-05-27

This file starts the second phase of the project: the transition from Stage 1
infrastructure into the mathematical content behind Mochizuki's Theorem 3.11 to
Corollary 3.12 passage.

The previous diary, `FORMALIZATION_NOTES.md`, records the infrastructure phase:
real-line copies, toy models, source obligations, endpoint packaging, payload
routes, public audits, and structured endpoint audit summaries. It remains the
record for those milestones. New milestones that implement non-inert IUT
mathematics should be recorded here.

## Review Checkpoint: End of Infrastructure Phase

The current Lean scaffold verifies the route:

```text
structured Theorem 3.11 inputs
+ side-condition hypotheses
-> source obligations
-> source audit
-> comparison payload inputs
-> comparison data
-> ComparisonDataEndpoint
-> StructuredEndpointAuditSummary
```

The main current entry point is:

```lean
package.structuredEndpointAuditSummary inputs hypotheses
```

It proves that the public endpoint, comparison data, payload route, and source
audit are tied to one coherent structured route. This prevents endpoint drift,
but it does not prove Mochizuki's hard mathematical claim.

## First Math Boundary

The next phase begins with the currently inert Theorem 3.11 ingredients:

```lean
IUTStage1Theorem311StructuredInputs.hasStructuredIPL
IUTStage1Theorem311StructuredInputs.hasStructuredSHE
IUTStage1Theorem311StructuredInputs.hasStructuredAPT
IUTStage1Theorem311StructuredInputs.algorithmOutputCertified
IUTStage1Theorem311StructuredInputs.hodgeTheaterSHEAlignment
```

These names currently expose structured bookkeeping data only. They do not yet
imply common-container comparison data, log-volume bounds, real-line-copy
identifications, or the Corollary 3.12 endpoint.

## Source Alignment

IUT III, Remark 3.11.1, identifies the key qualitative ingredients of Theorem
3.11:

* IPL: input prime-strip linkage;
* SHE: simultaneous holomorphic expressibility;
* APT: algorithmic parallel transport;
* HIS: hidden internal structures, where one reasons about qualitative output
  data without carrying all theta-function internals.

Mochizuki's 2026 formalization report isolates the final `3.11.5 -> 3.12`
portion as the simultaneous comparison around `(HDD) o (SHE)`, while the
second/third triangles concern APT plus IPL.

The Scholze-Stix diagnostic constraint remains active: any formal bridge from
structured source data to a real-valued endpoint must expose the real-line-copy
identifications and must not silently erase Hodge-theater/ring-history data.

## Phase 2 Starting Decision

The first non-inert mathematical target should be SHE.

Reason:

* SHE already appears in the current scaffold as the alignment between the
  common-container SHE arrow and the structured certificate.
* It is local enough to strengthen without claiming the full multiradial
  algorithm.
* It is directly relevant to the contested question of simultaneous comparison
  without collapse of histories.

The first planned math milestone should introduce a record tentatively named:

```lean
StructuredSHEContext
```

It should be strong enough to recover the existing inert `SHEDatum`, but weak
enough that it does not by itself imply the Corollary 3.12 endpoint.

## Guardrail

No theorem in this phase may turn IPL, SHE, APT, HIS, or any single qualitative
name into the endpoint unless every required transport, comparison target,
real-line-copy identification, and Hodge-theater history condition appears in
the theorem statement or an explicit dependency.

## Math Milestone 1: Conservative Structured SHE Context

Lean files:

* `Iut/Foundations/QualitativeData.lean`
* `Iut/Stage1/ToyQualitativeOutput.lean`

### Source Check

IUT III, Remark 3.11.1 describes SHE as simultaneous holomorphic
expressibility: the relevant construction and output data should be expressed in
terms that are valid relative to both the domain and codomain arithmetic
holomorphic structures. Mochizuki's 2026 report identifies `(HDD) o (SHE)` as
the final Stage 1 comparison focus. Scholze-Stix's criticism remains the
guardrail: simultaneous expression must not silently become identification of
the two histories or of their real-line copies.

### Purpose

The existing `SHEDatum` only stored a shared context. This milestone introduces
a first stronger SHE object, `QualitativeData.StructuredSHEContext`, without
making SHE prove any comparison endpoint.

The new context records:

* domain and codomain holomorphic structures;
* a common language;
* q-pilot and Theta-pilot holomorphic structures;
* explicit placement of the q-pilot in the codomain theater;
* explicit placement of the Theta-pilot in the domain theater;
* a proposition witnessing simultaneous validity;
* an explicit proof that the domain and codomain Hodge-theater sides are not
  identified.

### Lean Declarations

In `QualitativeData.lean`:

```text
QualitativeData.StructuredSHEContext
QualitativeData.StructuredSHEContext.sharedContext
QualitativeData.StructuredSHEContext.sheDatum
QualitativeData.StructuredSHEContext.hasStructuredSHE
QualitativeData.StructuredSHEContext.qPilotTheater_eq_codomain
QualitativeData.StructuredSHEContext.thetaPilotTheater_eq_domain
QualitativeData.StructuredSHEContext.simultaneousValid
QualitativeData.StructuredSHEContext.domainHistory_ne_codomainHistory
QualitativeData.StructuredSHEContext.sheDatum_sharedContext
```

In `ToyQualitativeOutput.lean`:

```text
thetaToyStructuredSHEContext
thetaToyStructuredSHEContext_sheDatum
thetaToyStructuredSHEContext_hasStructuredSHE
thetaToyStructuredSHEContext_histories_not_identified
```

### What This Tests

The toy example satisfies the stronger SHE context while proving only the
conservative projections:

* it recovers the old inert `SHEDatum`;
* it recovers `HasStructuredSHE`;
* it records that the toy domain and codomain histories are not identified.

It does not prove a common-target bound, payload route, public audit, or
Corollary-3.12-shaped endpoint.

### Design Trap Avoided

The trap would be to let "SHE" become a magic theorem producing the comparison
payload. This milestone does the opposite: it strengthens the data shape while
only projecting back to existing inert evidence. The extra fields make future
bridges state exactly what simultaneous validity and history separation mean.

### Next Step

The next milestone should connect `StructuredSHEContext` to the source-facing
`IUTStage1Theorem311SHEAlignment` field, again as a conservative projection
rather than as an endpoint theorem.

## Math Milestone 2: Source-Facing Structured SHE Alignment

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

Milestone 1 strengthened SHE at the qualitative-data layer. The next source
boundary is the existing Theorem 3.11 SHE-alignment field, which states that the
common-container SHE arrow datum agrees with the structured certificate's SHE
datum. This corresponds to the role of SHE in the fourth triangle described in
Mochizuki's 2026 report: the SHE arrow supplies the q-pilot-side data used in
the restricted `(HDD) o (SHE)` composite.

The Scholze-Stix guardrail remains: this alignment is not a theorem that
identifies histories or real lines. It is only a named equality between the SHE
datum used by the common container and the SHE datum stored in the structured
certificate.

### Purpose

This milestone adds a source-facing structure:

```text
IUTStage1Theorem311StructuredSHE
```

It contains:

* a `QualitativeData.StructuredSHEContext`;
* an equality from the context's `sheDatum` to the package certificate's SHE
  datum;
* an equality from the common-container SHE arrow datum to the context's
  `sheDatum`.

From these fields we recover the existing `IUTStage1Theorem311SHEAlignment`.
No endpoint, payload route, common-target bound, or Corollary 3.12 statement is
derived.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311StructuredSHE
IUTStage1Theorem311StructuredSHE.hasStructuredSHE
IUTStage1Theorem311StructuredSHE.sheDatumMatchesCertificate
IUTStage1Theorem311StructuredSHE.sheArrowMatchesContext
IUTStage1Theorem311StructuredSHE.hodgeTheaterSHEAlignment
IUTStage1Theorem311StructuredSHE.sheAlignment
IUTStage1Theorem311StructuredSHE.sheAlignment_hodgeTheaterSHEAlignment_eq
IUTStage1Theorem311StructuredSHE.domainHistory_ne_codomainHistory
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_structured_she_input_example
unitThetaToy_source_theorem311_structured_she_input_hasStructuredSHE_example
unitThetaToy_source_theorem311_structured_she_input_alignment_example
unitThetaToy_source_theorem311_structured_she_input_history_example
```

### What This Tests

The toy source package constructs a strengthened source-facing SHE input and
checks that it recovers:

* the old inert `HasStructuredSHE`;
* the existing source-facing SHE alignment equality;
* the explicit non-identification of domain and codomain Hodge-theater sides.

### Design Trap Avoided

The trap would be to strengthen SHE and immediately let it discharge the final
comparison. Instead, this milestone connects stronger SHE data only to the
pre-existing SHE alignment field. This keeps the next bridge honest: any future
payload construction must state additional HDD/common-container and real-chart
requirements explicitly.

### Next Step

The next milestone should expose a structured SHE input through
`IUTStage1Theorem311StructuredInputs`, so the strengthened SHE context can be
carried alongside the existing algorithmic-output and side-condition routes.

## Math Milestone 3: Structured Inputs with Strengthened SHE

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

Milestones 1 and 2 introduced a stronger SHE context and connected it to the
existing source-facing SHE alignment. The next issue is routing: strengthened
SHE should be available alongside `IUTStage1Theorem311StructuredInputs`, but it
should not replace or redefine the older structured-input route.

This follows the same source discipline as IUT III, Remark 3.11.1: SHE is one
ingredient in the Theorem 3.11 package, not a standalone proof of the final
Corollary 3.12 comparison.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311StructuredInputsWithSHE
```

The bundle contains:

* the existing `IUTStage1Theorem311StructuredInputs`;
* a strengthened `IUTStage1Theorem311StructuredSHE`.

It exposes both routes and proves their SHE-alignment components agree by proof
irrelevance. It also exposes the history-separation guard from the strengthened
SHE context.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311StructuredInputsWithSHE
IUTStage1Theorem311StructuredInputsWithSHE.theorem311StructuredInputs
IUTStage1Theorem311StructuredInputsWithSHE.structuredSHE
IUTStage1Theorem311StructuredInputsWithSHE.hasStructuredIPL
IUTStage1Theorem311StructuredInputsWithSHE.hasStructuredSHE
IUTStage1Theorem311StructuredInputsWithSHE.hasStructuredSHE_from_context
IUTStage1Theorem311StructuredInputsWithSHE.hasStructuredAPT
IUTStage1Theorem311StructuredInputsWithSHE.algorithmOutputCertified
IUTStage1Theorem311StructuredInputsWithSHE.hodgeTheaterSHEAlignment
IUTStage1Theorem311StructuredInputsWithSHE.hodgeTheaterSHEAlignment_from_context
IUTStage1Theorem311StructuredInputsWithSHE.sheAlignment_eq_context_sheAlignment
IUTStage1Theorem311StructuredInputsWithSHE.domainHistory_ne_codomainHistory
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_structured_inputs_with_she_example
unitThetaToy_source_theorem311_structured_inputs_with_she_hasSHE_example
unitThetaToy_source_theorem311_structured_inputs_with_she_alignment_eq_example
unitThetaToy_source_theorem311_structured_inputs_with_she_history_example
```

### What This Tests

The toy source package now carries both the older structured-input route and the
strengthened SHE route in one bundle. The examples check:

* the bundle recovers `HasStructuredSHE` from the strengthened context;
* the old and strengthened SHE-alignment components agree;
* the domain/codomain history separation remains visible.

### Design Trap Avoided

The trap would be to mutate `IUTStage1Theorem311StructuredInputs` itself and
silently strengthen every old theorem. Instead, this milestone introduces an
explicit stronger bundle. Downstream code must opt in to the stronger SHE
context, which makes the new assumption visible in theorem statements.

### Next Step

The next milestone should define the first small SHE-to-common-container
compatibility checklist: it should mention the SHE context, the common
container's shared context, and the certificate SHE datum, but still avoid any
real-valued endpoint conclusion.

## Math Milestone 4: SHE/Common-Container Compatibility

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

Mochizuki's formalization report describes the final triangle in the
`3.11.5 => 3.12` route as the composite `(HDD) o (SHE)`, with SHE supplying the
input situation in which HDD is applied. IUT III, Remark 3.11.1 describes SHE as
the condition that the output data can be expressed in a form valid relative to
both arithmetic holomorphic structures.

For our purposes, the immediate formal question is not whether this already
proves Corollary 3.12. The immediate question is whether the strengthened SHE
context is the same SHE context used by the existing common-container/HDD-SHE
composite. This is exactly the kind of bookkeeping where Lean is useful: it
forces the shared-context equality to be proved from recorded fields, rather
than silently assumed.

### Purpose

This milestone adds a proof-level compatibility checklist:

```text
IUTStage1Theorem311StructuredSHECommonContainerCompatibility
```

The checklist records four facts:

* the common-container SHE arrow datum is the strengthened SHE datum;
* the strengthened SHE datum is the certificate SHE datum;
* the common-container shared context is the strengthened SHE shared context;
* the domain and codomain histories are still not identified.

The third item is derived, not postulated. It follows from:

```text
CommonContainerData.she_context_matches
IUTStage1Theorem311StructuredSHE.sheArrowMatchesContext
StructuredSHEContext.sheDatum_sharedContext
```

This is intentionally only a compatibility statement. It does not bind a
comparison endpoint, does not assert a target bound, and does not identify the
two arithmetic histories.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311StructuredSHE.commonContainerContextMatches
IUTStage1Theorem311StructuredSHECommonContainerCompatibility
IUTStage1Theorem311StructuredSHECommonContainerCompatibility.ofStructuredSHE
IUTStage1Theorem311StructuredSHECommonContainerCompatibility.sheArrowMatchesContext
IUTStage1Theorem311StructuredSHECommonContainerCompatibility.sheDatumMatchesCertificate
IUTStage1Theorem311StructuredSHECommonContainerCompatibility.commonContainerContextMatches
IUTStage1Theorem311StructuredSHECommonContainerCompatibility.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.commonContainerCompatibility
IUTStage1Theorem311StructuredInputsWithSHE.commonContainerContextMatches
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_structured_she_common_container_compatibility_example
unitThetaToy_source_theorem311_structured_she_common_context_example
unitThetaToy_source_theorem311_structured_inputs_with_she_common_context_example
```

### What This Tests

The toy source package now instantiates the compatibility checklist and proves
that its charted common container uses the same shared context as the structured
SHE context. In the toy model this is by definitional equality, but the
source-level theorem is not `rfl`: it composes the equality stored in the
common-container record with the equality stored in the structured SHE input.

### Design Trap Avoided

The tempting but dangerous shortcut would be to treat the common container as
if it already supplied a global endpoint comparison. We did not do that. The
new theorem merely aligns names and contexts. This keeps the Scholze-Stix
diagnostic issue visible: a later theorem must still explain what is being
compared, under which history discipline, and why the formal route is not a
hidden collapse of the two structures.

### Next Step

The next milestone should expose the first audited entry point from this
compatibility checklist into the existing `HDD o SHE` boundedness machinery.
That step should remain proof-level and should explicitly state which
certificate and common-container object are being used before any bound is
transported.

## Math Milestone 5: Audited HDD-after-SHE Bound Entry

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The formalization report isolates the fourth triangle as `(HDD) o (SHE)`: HDD is
restricted to the case where its input data is obtained via the SHE arrow. The
previous milestone checked that our strengthened SHE context is the same context
seen by the common container. The present milestone asks the next narrower
question: once that audit is present, what target-volume bound is already
available from the existing `HDD o SHE` machinery?

This is also where the Scholze-Stix caution remains relevant. Producing a
target-volume upper bound is not yet the Corollary 3.12 comparison. The q-side
membership inequality, chart readings, positivity, normalization, and final
signed packaging are still separate pieces of the formal route.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311AuditedHDDSHEBound
```

The record packages:

* the SHE/common-container compatibility checklist from Milestone 4;
* the chosen output target-volume bound obtained from the charted common
  container applied to the pre-ledger certificate;
* the all-targets version of the same common-container bound;
* the history-separation guard from the strengthened SHE context.

The chosen bound has the form:

```text
RegionMeasure.targetVolume package.preLedger.measure
    (package.preLedger.output.comparison
      package.preLedger.chosenOutput.choice)
  <= package.preLedger.thetaSigned
```

It is proved by:

```text
package.preLedger.chartedContainer.choice_targetVolume_le
  package.preLedger.certificate
  package.preLedger.chosenOutput.choice
```

Thus the certificate and common-container object are explicit in the proof term.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311AuditedHDDSHEBound
IUTStage1Theorem311AuditedHDDSHEBound.ofStructuredInputsWithSHE
IUTStage1Theorem311AuditedHDDSHEBound.commonContainerCompatibility
IUTStage1Theorem311AuditedHDDSHEBound.commonContainerContextMatches
IUTStage1Theorem311AuditedHDDSHEBound.chosenTargetVolume_le_theta
IUTStage1Theorem311AuditedHDDSHEBound.allTargetsAtMost_theta
IUTStage1Theorem311AuditedHDDSHEBound.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.auditedHDDSHEBound
IUTStage1Theorem311StructuredInputsWithSHE.auditedHDDSHE_chosenTargetVolume_le_theta
IUTStage1Theorem311StructuredInputsWithSHE.auditedHDDSHE_allTargetsAtMost_theta
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_hdd_she_bound_example
unitThetaToy_source_theorem311_audited_hdd_she_choice_bound_example
unitThetaToy_source_theorem311_audited_hdd_she_all_targets_example
```

### What This Tests

The toy model verifies that the audited route can recover:

* the selected target-volume bound for the chosen output;
* the all-targets upper bound for the transported output family.

Both are obtained through the common-container API. The examples do not use
q-side membership and do not conclude the signed q-to-Theta inequality.

### Design Trap Avoided

The dangerous shortcut would be to identify this upper bound with Corollary 3.12
itself. We did not do that. The new record is an entry into the boundedness
machinery, not an endpoint theorem. In particular, it does not mention
`Corollary312Inequality`, `ComparisonPayloadInputs`, or q-positivity.

### Next Step

The next milestone should relate this audited `HDD o SHE` bound to the existing
charted target-volume middle term. That bridge should state only that the
target-volume field used in the final comparison is the same chosen target
volume bounded here; it should still keep q-side membership and final
Corollary 3.12 packaging separate.

## Math Milestone 6: Audited Target-Volume Middle Term

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The proof of Corollary 3.12 ultimately uses a middle real-valued target-volume
term between the q-side quantity and the Theta-side bound. The previous
milestone recovered the upper bound on the chosen target volume from the
audited `HDD o SHE` route. This milestone connects that chosen target volume to
the named charted target-volume field in the pre-ledger.

This remains below the disputed endpoint. It does not assert that the q-side
quantity lies below the target-volume middle term, and it does not package the
signed q-to-Theta inequality.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311AuditedTargetVolumeMiddle
```

The record packages:

* the audited `HDD o SHE` bound from Milestone 5;
* the equality identifying `targetVolume.targetSigned` with the chosen target
  volume;
* the resulting upper bound `targetVolume.targetSigned <= thetaSigned`;
* the history-separation guard.

The key proof is:

```text
rw [package.preLedger.targetSigned_eq_choiceTargetVolume]
exact audited.chosenTargetVolume_le_theta
```

So the middle-term inequality is not independent data. It is derived from the
existing pre-ledger equality and the audited `HDD o SHE` target-volume bound.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311AuditedTargetVolumeMiddle
IUTStage1Theorem311AuditedTargetVolumeMiddle.ofAuditedHDDSHEBound
IUTStage1Theorem311AuditedTargetVolumeMiddle.ofStructuredInputsWithSHE
IUTStage1Theorem311AuditedTargetVolumeMiddle.auditedHDDSHEBound
IUTStage1Theorem311AuditedTargetVolumeMiddle.targetSigned_eq_chosenTargetVolume
IUTStage1Theorem311AuditedTargetVolumeMiddle.chosenTargetVolume_eq_targetSigned
IUTStage1Theorem311AuditedTargetVolumeMiddle.targetSigned_le_theta
IUTStage1Theorem311AuditedTargetVolumeMiddle.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.auditedTargetVolumeMiddle
IUTStage1Theorem311StructuredInputsWithSHE.auditedTargetSigned_eq_chosenTargetVolume
IUTStage1Theorem311StructuredInputsWithSHE.auditedTargetSigned_le_theta
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_target_middle_example
unitThetaToy_source_theorem311_audited_target_middle_eq_example
unitThetaToy_source_theorem311_audited_target_middle_le_theta_example
```

### What This Tests

The toy model verifies that the charted middle term is definitionally the target
volume of the chosen output comparison and inherits the audited upper bound.
The proof goes through the same source-facing API as the non-toy scaffold.

### Design Trap Avoided

The trap would be to combine this with q-side membership immediately and present
the result as the Corollary 3.12 inequality. We did not do that. The record only
covers the upper half of the eventual chain:

```text
targetSigned <= thetaSigned
```

The lower half,

```text
qSigned <= targetSigned
```

is still a separate membership/charting obligation.

### Next Step

The next milestone should add an audited lower-middle bridge for
`qSigned <= targetSigned`, explicitly sourced from the charted membership datum.
Only after both middle bridges are present should we consider a separate
packaging theorem that assembles the signed q-to-Theta inequality.

## Math Milestone 7: Audited q-to-Target Membership Bridge

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The previous milestone covered the upper half of the eventual real inequality
chain, namely `targetSigned <= thetaSigned`. The lower half,
`qSigned <= targetSigned`, has a different source: it comes from the charted
membership datum for the selected output comparison, not from `HDD o SHE`.

This distinction matters for the Corollary 3.12 dispute. If the lower bound,
upper bound, chart identifications, and final packaging are collapsed into one
opaque theorem, then Lean would no longer help us locate the exact mathematical
move being used. This milestone therefore isolates the lower-middle bridge.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311AuditedMembershipMiddle
```

The record packages:

* the audited target-volume middle term from Milestone 6;
* the q-side chart reading;
* the fact that the selected output comparison holds at the q-point;
* the lower-middle inequality `qSigned <= targetSigned`;
* the history-separation guard.

The lower-middle inequality is sourced from:

```text
package.preLedger.qSigned_le_targetSigned
```

and the chart/membership facts are sourced from:

```text
package.preLedger.qSigned_eq_chartedQ
package.preLedger.chosenComparisonHoldsQ
```

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311AuditedMembershipMiddle
IUTStage1Theorem311AuditedMembershipMiddle.ofTargetVolumeMiddle
IUTStage1Theorem311AuditedMembershipMiddle.ofStructuredInputsWithSHE
IUTStage1Theorem311AuditedMembershipMiddle.targetVolumeMiddle
IUTStage1Theorem311AuditedMembershipMiddle.qCharted
IUTStage1Theorem311AuditedMembershipMiddle.chosenHolds
IUTStage1Theorem311AuditedMembershipMiddle.qSigned_le_targetSigned
IUTStage1Theorem311AuditedMembershipMiddle.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.auditedMembershipMiddle
IUTStage1Theorem311StructuredInputsWithSHE.auditedQCharted
IUTStage1Theorem311StructuredInputsWithSHE.auditedChosenHolds
IUTStage1Theorem311StructuredInputsWithSHE.auditedQSigned_le_targetSigned
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_membership_middle_example
unitThetaToy_source_theorem311_audited_membership_q_charted_example
unitThetaToy_source_theorem311_audited_membership_chosen_holds_example
unitThetaToy_source_theorem311_audited_membership_q_le_target_example
```

### What This Tests

The toy model verifies that the lower-middle bridge recovers the q-side chart
identity, the selected-output membership fact, and `qSigned <= targetSigned`.
These are intentionally tested without invoking the final signed inequality.

### Design Trap Avoided

The dangerous shortcut would be to immediately compose:

```text
qSigned <= targetSigned
targetSigned <= thetaSigned
```

and call this Corollary 3.12. We did not do that. The lower and upper bridges
now exist as separate audited objects, which lets us review exactly which source
datum supports each half of the chain.

### Next Step

The next milestone may add a deliberately named chain-composition record that
derives only the raw real inequality `qSigned <= thetaSigned` from the two
middle bridges. It should still avoid `Corollary312Inequality` until
q-positivity and source normalization are explicitly present.

## Math Milestone 8: Audited Raw Inequality Chain

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

IUT III, Corollary 3.12 ultimately concerns a log-volume estimate comparing the
q-pilot side to the Theta-pilot side. The introduction to IUT III describes this
as a computation of an upper bound for the q-pilot log-volume via the
Theta-pilot/hull computation. Mochizuki's later formalization report separates
the final `3.11.5 => 3.12` portion into the simultaneous-comparison step around
`(HDD) o (SHE)`.

Our current code now has two audited middle bridges:

```text
qSigned <= targetSigned
targetSigned <= thetaSigned
```

This milestone composes exactly these two inequalities and nothing more.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311AuditedRawInequality
```

The record packages:

* the audited membership middle from Milestone 7;
* the lower inequality `qSigned <= targetSigned`;
* the upper inequality `targetSigned <= thetaSigned`;
* the composed raw inequality `qSigned <= thetaSigned`;
* the history-separation guard.

The composed inequality is proved by:

```text
le_trans middle.qSigned_le_targetSigned
  middle.targetVolumeMiddle.targetSigned_le_theta
```

Thus the composition point is explicit and reviewable.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311AuditedRawInequality
IUTStage1Theorem311AuditedRawInequality.ofMembershipMiddle
IUTStage1Theorem311AuditedRawInequality.ofStructuredInputsWithSHE
IUTStage1Theorem311AuditedRawInequality.membershipMiddle
IUTStage1Theorem311AuditedRawInequality.qSigned_le_targetSigned
IUTStage1Theorem311AuditedRawInequality.targetSigned_le_theta
IUTStage1Theorem311AuditedRawInequality.qSigned_le_thetaSigned
IUTStage1Theorem311AuditedRawInequality.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.auditedRawInequality
IUTStage1Theorem311StructuredInputsWithSHE.auditedRaw_qSigned_le_thetaSigned
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_raw_inequality_example
unitThetaToy_source_theorem311_audited_raw_q_le_theta_example
unitThetaToy_source_theorem311_audited_raw_explicit_q_le_theta_example
```

### What This Tests

The toy model verifies that the raw chain produces:

```text
(Transport.map unitQToTheta (qAssignment h)).coord <= -(2 * h) + epsilonBound
```

through the source-facing audited route. This gives us a concrete sanity check
that the lower and upper middle bridges compose as intended.

### Design Trap Avoided

The trap would be to make this theorem return `Corollary312Inequality`, or to
silently use q-positivity and normalization. We did not do that. This milestone
returns only a plain real inequality:

```text
package.preLedger.qSigned <= package.preLedger.thetaSigned
```

The signed pilot objects, q-positivity, source normalization, and public
comparison packaging remain outside this record.

### Next Step

The next milestone should introduce an audited packaging boundary that states
exactly which extra side conditions are needed to turn the raw real inequality
into the existing signed comparison payload. That step should mention
q-positivity and normalization explicitly and should remain separate from the
SHE/HDD/membership derivation.

## Math Milestone 9: Audited Signed Payload Boundary

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The previous milestone produced only the raw real inequality
`qSigned <= thetaSigned`. The existing Stage 1 schema represents the signed
Corollary-3.12-style data by `Corollary312ComparisonData`, which additionally
stores q-positivity. Separately, the source route tracks normalization as a
promotion side condition.

This milestone marks the boundary where those side conditions are attached. It
does not alter the audited SHE/HDD/membership derivation of the raw inequality.

### Purpose

This milestone adds:

```text
IUTStage1Theorem311AuditedSignedPayloadBoundary
```

The boundary packages:

* the audited raw inequality from Milestone 8;
* q-pilot positivity from `IUTStage1SourceSideConditions`;
* source normalization from `IUTStage1SourceSideConditions`;
* the raw inequality again as the field used by the signed comparison payload;
* the history-separation guard.

It also exposes:

```text
comparisonData : Corollary312ComparisonData
```

This construction uses q-positivity and the raw inequality. Normalization is
kept as an explicit boundary proof even though `Corollary312ComparisonData`
does not currently consume it.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1Theorem311AuditedSignedPayloadBoundary
IUTStage1Theorem311AuditedSignedPayloadBoundary.ofRawInequality
IUTStage1Theorem311AuditedSignedPayloadBoundary.ofStructuredInputsWithSideConditions
IUTStage1Theorem311AuditedSignedPayloadBoundary.rawInequality
IUTStage1Theorem311AuditedSignedPayloadBoundary.qPilotPositive
IUTStage1Theorem311AuditedSignedPayloadBoundary.sourceNormalization
IUTStage1Theorem311AuditedSignedPayloadBoundary.qSigned_le_thetaSigned
IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData
IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData_qSigned
IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData_thetaSigned
IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData_qSigned_le_thetaSigned
IUTStage1Theorem311AuditedSignedPayloadBoundary.comparisonData_corollary312
IUTStage1Theorem311AuditedSignedPayloadBoundary.domainHistory_ne_codomainHistory
IUTStage1Theorem311StructuredInputsWithSHE.auditedSignedPayloadBoundary
IUTStage1Theorem311StructuredInputsWithSHE.auditedComparisonData
IUTStage1Theorem311StructuredInputsWithSHE.auditedComparisonData_qSigned_le_thetaSigned
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_signed_payload_boundary_example
unitThetaToy_source_theorem311_audited_comparison_data_example
unitThetaToy_source_theorem311_audited_comparison_data_q_le_theta_example
unitThetaToy_source_theorem311_audited_payload_normalization_example
```

### What This Tests

The toy model verifies that the audited route can construct
`Corollary312ComparisonData` only after explicit side conditions are supplied.
It also checks that the comparison data stores the raw inequality and that
source normalization remains separately visible.

### Design Trap Avoided

The trap would be to let q-positivity or normalization appear as implicit
consequences of SHE, HDD, or membership. We did not do that. They enter only
through `IUTStage1SourceSideConditions`, at the named signed-payload boundary.

### Next Step

The next milestone should compare this audited signed payload with the older
public-audit route already present in `IUTStage1Source.lean`. The goal is not a
new endpoint, but a theorem saying that the newly audited payload agrees with
the existing comparison-data packaging when supplied the same side conditions.

## Math Milestone 10: Audited Payload Route Equality

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The source file already had an older packaging route:

```text
comparisonPayloadInputs
comparisonDataFromPayloadInputs
```

The new audited route starts earlier, at the structured SHE context, and passes
through the explicit SHE/HDD bound, target middle term, membership middle term,
raw inequality, and signed-payload boundary. This milestone checks that the new
audited payload is not a parallel endpoint: when supplied the same side
conditions, it agrees with the older comparison-data packaging.

### Purpose

This milestone adds package-level route comparison declarations:

```text
IUTStage1SourcePackage.auditedComparisonSourceObligations
IUTStage1SourcePackage.auditedComparisonData_eq_payloadInputs
IUTStage1SourcePackage.auditedComparisonData_stage1Comparison_eq_payloadInputs
```

The source obligations used for the old route are built from:

```text
IUTStage1SourceObligations.ofStructuredInputsAndSideConditions
  bundle.inputs sideConditions
```

The equality then states that:

```text
bundle.auditedComparisonData sideConditions
=
package.comparisonDataFromPayloadInputs
  (package.auditedComparisonSourceObligations bundle sideConditions)
```

### What This Tests

The toy model verifies both comparison-data equality and stage-comparison
equality:

```text
unitThetaToy_source_theorem311_audited_comparison_data_eq_payload_inputs_example
unitThetaToy_source_theorem311_audited_stage_comparison_eq_payload_inputs_example
```

This confirms that the audited route integrates with the existing Stage 1
comparison-data API.

### Design Trap Avoided

The trap would be to leave two independent ways to manufacture signed comparison
data. That would make later reviews ambiguous: a theorem could use the older
payload path while appearing to rely on the audited SHE/HDD/membership path. The
route-equality theorem makes the relationship explicit.

### Next Step

The next milestone should decide how much of the public audit route should be
re-exposed through the newly audited path. A conservative step would prove only
that the public audit obtained from the audited comparison data has the same
Corollary 3.12 proof term up to proof irrelevance, while keeping the route
checklist visible.

## Math Milestone 11: Audited Public-Audit Wrapper

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

At this point the formal route contains two layers:

* the audited derivation layer, which starts at structured SHE and passes through
  `HDD o SHE`, the charted target-volume middle term, q-membership, the raw
  inequality, and the signed-payload boundary;
* the older public-audit layer, which packages `Corollary312ComparisonData` for
  the Stage 1 endpoint API.

This milestone exposes the public-audit tuple through the audited derivation
layer without making a new endpoint theorem.

### Purpose

This milestone adds:

```text
IUTStage1SourcePackage.AuditedPublicAudit
```

The wrapper records:

* the signed-payload boundary from Milestone 9;
* the equality with the older payload-input route from Milestone 10;
* the public-audit raw inequality;
* the public-audit Corollary 3.12-shaped proposition;
* the stage-comparison recovery proof;
* equality of the audited and payload-input stage comparisons;
* source normalization;
* history separation.

It also adds projections:

```text
AuditedPublicAudit.qSigned_le_thetaSigned
AuditedPublicAudit.corollary312Endpoint
AuditedPublicAudit.publicAudit
AuditedPublicAudit.comparisonDataEqPayloadInputs
AuditedPublicAudit.sourceNormalization
AuditedPublicAudit.domainHistory_ne_codomainHistory
IUTStage1SourcePackage.auditedPublicAudit
```

### What This Tests

The toy model verifies:

```text
unitThetaToy_source_theorem311_audited_public_audit_example
unitThetaToy_source_theorem311_audited_public_audit_tuple_example
unitThetaToy_source_theorem311_audited_public_audit_route_example
unitThetaToy_source_theorem311_audited_public_audit_history_example
```

These examples check that the wrapper can recover the public-audit tuple, the
route equality, and the history-separation guard.

### Design Trap Avoided

The trap would be to replace the existing public-audit endpoint with a second
endpoint under a more audited-looking name. We did not do that. The new wrapper
is explicitly a consistency layer: it exposes the existing public-audit facts
while keeping the full audited route checklist available for review.

### Next Step

The next milestone should add a compact route summary for the audited
structured-SHE path, similar in spirit to earlier endpoint summaries, so a human
reader can inspect the major checkpoints without expanding every proof field.

## Math Milestone 12: Audited Structured-SHE Route Summary

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

The formal path from structured SHE to the public-audit tuple is now deliberately
long. That length is useful for auditability, but a human reader also needs a
compact checkpoint view that lists the major stages of the route without hiding
which route is being used.

This milestone mirrors earlier endpoint-summary patterns in the file while
remaining attached to the newer structured-SHE audit path.

### Purpose

This milestone adds:

```text
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary
```

The summary records:

* structured SHE availability;
* SHE/common-container compatibility;
* the audited `HDD o SHE` bound;
* the target-volume middle term;
* the q-membership middle term;
* the raw real inequality;
* the signed-payload boundary;
* the audited public-audit wrapper;
* equality with the older payload-input route;
* the q-to-Theta inequality in comparison data;
* source normalization;
* history separation.

It also exposes projection theorems for the public audit, signed-payload
boundary, raw inequality, payload-route equality, q-to-Theta inequality,
normalization, and history separation.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.ofStructuredInputsWithSHE
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.publicAudit
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.signedPayloadBoundary
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.rawInequality
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.comparisonDataEqPayloadInputs
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.qSigned_le_thetaSigned
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.sourceNormalization
IUTStage1SourcePackage.AuditedStructuredSHERouteSummary.domainHistory_ne_codomainHistory
IUTStage1SourcePackage.auditedStructuredSHERouteSummary
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_audited_route_summary_example
unitThetaToy_source_theorem311_audited_route_summary_raw_example
unitThetaToy_source_theorem311_audited_route_summary_public_example
unitThetaToy_source_theorem311_audited_route_summary_q_le_theta_example
```

### What This Tests

The toy examples verify that the compact route summary can be built and that it
recovers the raw inequality, the audited public-audit wrapper, and the
q-to-Theta inequality in the audited comparison data.

### Design Trap Avoided

The trap would be to introduce a summary that obscures the route by replacing
the checkpoint records. We did not do that. The summary contains the checkpoint
records as fields, so it is a review aid rather than a shortcut around the
audit path.

### Next Step

The next milestone should start separating this audited route into a smaller
module if the source file becomes unwieldy, or else add source-facing naming for
which checkpoint corresponds to the debated Theorem 3.11 to Corollary 3.12
transition.

## Math Milestone 13: Named Theorem 3.11 to Corollary 3.12 Checkpoints

Lean files:

* `Iut/Stage1/IUTStage1Source.lean`
* `Iut/Stage1/IUTStage1SourceExample.lean`

### Source Check

Mochizuki's formalization report names the final reorganized portion as
`3.11.5 => 3.12` and identifies the fourth triangle as the composite
`(HDD) o (SHE)`. The same passage says this triangle concerns simultaneous
comparison inside a common container. IUT III, Remark 3.11.1 also stresses that
SHE and APT are not ordinary set-theoretic transport, and that later comparison
work remains necessary.

This milestone adds source-facing names for the checkpoints we have formalized,
so a reviewer can see which proof object corresponds to which part of that
discussion.

### Purpose

This milestone adds inert checkpoint identifiers:

```text
TransitionCheckpointId
fourthTriangleHDDSHECheckpoint
simultaneousComparisonCheckpoint
theorem3115ToCorollary312Checkpoint
```

It also adds:

```text
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints
```

The checkpoint record ties together:

* the audited structured-SHE route summary;
* the source input label;
* the Corollary 3.12 comparison label;
* the fourth-triangle `HDD o SHE` bound;
* the simultaneous common-container compatibility proof;
* the raw target-volume chain;
* the signed-payload boundary;
* the audited public audit;
* history separation.

### Lean Declarations

In `IUTStage1Source.lean`:

```text
TransitionCheckpointId
fourthTriangleHDDSHECheckpoint
simultaneousComparisonCheckpoint
theorem3115ToCorollary312Checkpoint
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.ofStructuredInputsWithSHE
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.routeSummary
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.theorem311InputLabel
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.corollary312ComparisonLabel
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.fourthTriangleHDDSHE
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.simultaneousCommonContainer
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.targetVolumeChain
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.signedPayloadBoundary
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.publicAudit
IUTStage1SourcePackage.AuditedTheorem311ToCorollary312Checkpoints.domainHistory_ne_codomainHistory
IUTStage1SourcePackage.auditedTheorem311ToCorollary312Checkpoints
```

In `IUTStage1SourceExample.lean`:

```text
unitThetaToy_source_theorem311_transition_checkpoints_example
unitThetaToy_source_theorem311_transition_checkpoints_input_label_example
unitThetaToy_source_theorem311_transition_checkpoints_hdd_she_example
unitThetaToy_source_theorem311_transition_checkpoints_common_container_example
unitThetaToy_source_theorem311_transition_checkpoints_history_example
```

### What This Tests

The toy model verifies that the named checkpoint record can be instantiated and
that it exposes the input label, the fourth-triangle `HDD o SHE` checkpoint, the
simultaneous common-container checkpoint, and history separation.

### Design Trap Avoided

The trap would be to name the entire route "Corollary 3.12" and thereby obscure
which part of the proof corresponds to which mathematical claim. The new record
keeps the checkpoints separate. In particular, the `HDD o SHE` bound, the
common-container compatibility, the raw inequality, and the signed-payload
boundary remain distinct fields.

### Next Step

The source file is now large. The next milestone should split the audited
Theorem 3.11 to Corollary 3.12 route into a dedicated module, preserving public
imports and avoiding any change to theorem statements.

## Math Milestone 14: First Initial Theta Data Layer

Lean files:

* `Iut/Foundations/InitialThetaData.lean`
* `Iut/Foundations/InitialThetaDataExample.lean`
* `Iut/Basic.lean`

### Source Check

This milestone starts the actual mathematical implementation from IUT I,
Definition 3.1. The source defines initial theta data as

```text
(Fbar/F, X_F, l, C_K, V, Vbad_mod, epsilon)
```

subject to conditions (a)-(f): `F` is a number field containing `sqrt(-1)`,
`Fbar` is an algebraic closure, `X_F` is a once-punctured elliptic curve over
`F`, `l` is a prime at least `5`, `K/F` is the finite Galois extension
determined by the `l`-torsion representation, `V -> Vmod` is a valuation
section, `Vbad_mod` is a nonempty bad nonarchimedean set of odd residue
characteristic prime to `l`, `C_K` is the associated hyperbolic orbicurve, and
`epsilon` is a specified cusp.

### Lean Decisions

The formalization now uses mathlib for the mathematical objects that are
available:

```text
NumberField F
NumberField Fmod
AlgebraicClosure F
FiniteDimensional Fmod F
IsGalois Fmod F
FiniteDimensional F K
IsGalois F K
Nat.Prime l.value
WeierstrassCurve F
WeierstrassCurve.IsElliptic
```

This is a deliberate shift away from pure labels. In particular,
`PuncturedEllipticCurve.ofJ` uses mathlib's `WeierstrassCurve.ofJ`, and Lean
checks the theorem that its `j`-invariant is the chosen input.

The pieces not yet implemented in full IUT form are kept as explicit named
obligations rather than hidden inside an opaque label:

```text
stableReductionOverNonarchimedean
torsion23RationalOverF
lTorsionImageContainsSL2
qParameterOrdersPrimeToL
HyperbolicOrbicurveModel
CuspData
```

This lets the next milestones replace each obligation with real definitions
without changing the outer shape of initial theta data.

### Lean Declarations

```text
PrimeGeFive
SqrtMinusOneData
ThetaFieldTower
ThetaFieldTower.degreePrimeToL
PuncturedEllipticCurve
PuncturedEllipticCurve.jInvariant
PuncturedEllipticCurve.ofJ
PuncturedEllipticCurve.jInvariant_ofJ
ThetaValuationData
ThetaValuationData.bad
ThetaValuationData.goodMod
ThetaValuationData.good
ThetaValuationData.bad_nonempty
ThetaValuationData.badLift_has_multiplicative_reduction
HyperbolicOrbicurveModel
CuspData
InitialThetaData
InitialThetaData.algebraicClosure_isAlgClosure
InitialThetaData.moduli_extension_is_finiteDimensional
InitialThetaData.moduli_extension_is_galois
InitialThetaData.degree_F_over_Fmod_prime_to_l
InitialThetaData.prime_is_prime
InitialThetaData.prime_ge_five
InitialThetaData.badValuations_nonempty
InitialThetaData.badValuation_has_multiplicative_reduction
InitialThetaData.sqrtMinusOne_square
InitialThetaData.fmodFieldOfModuli
InitialThetaData.kIsLTorsionKernelField
InitialThetaData.cusp_arisesFromNonzeroQuotientElement
```

### What This Tests

The example file verifies:

* the prime `5` satisfies the IUT lower-bound wrapper;
* a small two-point model has a bijective valuation section `V -> Vmod`;
* the bad set is nonempty and bad lifts have the recorded multiplicative
  reduction property;
* a full abstract `InitialThetaData` constructor works under the exact field
  typeclass assumptions;
* mathlib's `ofJ` elliptic curve model supplies a checked `j`-invariant theorem.

### Design Trap Avoided

The trap here would be to keep "initial theta data" as a single inert label and
thereby postpone all mathematical pressure. We did not do that. The prime,
number-field, Galois-extension, algebraic-closure, elliptic-curve, and valuation
section components are real Lean data. The still-missing IUT-specific geometry
is isolated as named obligations that must be discharged or refined in later
milestones.

### Next Step

The next milestone should expand one obligation from Definition 3.1 instead of
adding more audit infrastructure. The most natural target is the field condition
`sqrt(-1) in F`, either by constructing concrete examples via a cyclotomic or
Gaussian number field, or by defining the field-of-moduli/extension layer that
will later support `Fmod`, `F`, and `K`.

## Math Milestone 15: Field Tower for Initial Theta Data

Lean files:

* `Iut/Foundations/InitialThetaData.lean`
* `Iut/Foundations/InitialThetaDataExample.lean`

### Source Check

This milestone tightens the field portion of IUT I, Definition 3.1(b),(c). The
source introduces `Fmod ⊆ F` as the field of moduli of `X_F`, assumes that
`F/Fmod` is Galois of degree prime to `l`, and then defines `K ⊆ Fbar` as the
finite Galois extension of `F` determined by the kernel of the `l`-torsion
outer representation.

The previous Lean layer had `F` and `K`, but not `Fmod`. That was too weak for
the actual definition, since the bad valuation set lives over `Fmod` and the
prime-to-`l` degree condition concerns `F/Fmod`, not `K/F`.

### Lean Decisions

The formalization now has a separate field-tower record:

```text
ThetaFieldTower l Fmod F K
```

It requires the following mathlib typeclass hypotheses:

```text
NumberField Fmod
NumberField F
NumberField K
Algebra Fmod F
Algebra F K
Algebra Fmod K
IsScalarTower Fmod F K
FiniteDimensional Fmod F
IsGalois Fmod F
FiniteDimensional F K
IsGalois F K
```

The condition that `F/Fmod` has degree prime to `l` is recorded as:

```text
Nat.Coprime (Module.finrank Fmod F) l.value
```

This uses mathlib's `Module.finrank` for finite-dimensional field extensions,
which is the right Lean-level replacement for extension degree at this stage.

The facts that `Fmod` is the field of moduli of `X_F` and that `K` is the
kernel field of the `l`-torsion representation remain explicit obligations in
`InitialThetaData`; they depend on elliptic-curve/moduli and Galois
representation definitions that we have not yet formalized.

### Lean Declarations

```text
ThetaFieldTower
ThetaFieldTower.sqrtMinusOne_square
ThetaFieldTower.degreePrimeToL
ThetaFieldTower.f_over_fmod_is_finiteDimensional
ThetaFieldTower.f_over_fmod_is_galois
ThetaFieldTower.k_over_f_is_finiteDimensional
ThetaFieldTower.k_over_f_is_galois
InitialThetaData.moduli_extension_is_finiteDimensional
InitialThetaData.moduli_extension_is_galois
InitialThetaData.degree_F_over_Fmod_prime_to_l
InitialThetaData.fmodFieldOfModuli
InitialThetaData.kIsLTorsionKernelField
```

### What This Tests

The example file now verifies:

* construction of a `ThetaFieldTower` from a square root of `-1` and a
  prime-to-`l` degree proof;
* construction of `InitialThetaData Fmod F K` rather than only
  `InitialThetaData F K`;
* projection of the `F/Fmod` prime-to-`l` condition;
* projection of the field-of-moduli and `l`-torsion-kernel-field obligations.

### Design Trap Avoided

The trap would be to continue treating `Fmod` as implicit prose. That would
make the valuation data look formally well typed while hiding the field over
which `Vbad_mod` is supposed to live. The Lean record now exposes the three
fields and the two extension layers, so future valuation and moduli definitions
must attach to the correct field.

### Next Step

The next math milestone should continue with Definition 3.1 itself. A good
target is to replace the field-of-moduli obligation with a more structured
record relating `X_F`, its quotient `C_F`, and `Fmod`, or to replace the current
valuation index placeholders with mathlib finite places of `Fmod` and `K` if
the available API is strong enough.

## Math Milestone 16: Curve and Moduli Data for Definition 3.1(b)

Lean files:

* `Iut/Foundations/InitialThetaData.lean`
* `Iut/Foundations/InitialThetaDataExample.lean`

### Source Check

IUT I, Definition 3.1(b) starts with a once-punctured elliptic curve `X_F`
over `F`, writes `E_F` for the elliptic curve determined by `X_F`, forms the
hyperbolic orbicurve `C_F` as the quotient of `X_F` by the unique order-two
involution `-1`, and then introduces `Fmod` as the field of moduli of `X_F`.
The same clause assumes stable reduction over nonarchimedean valuations and
rationality over `F` of the `2 * 3` torsion points of `E_F`.

### Lean Decisions

These clauses now live in:

```text
ThetaCurveModuliData Fmod F
```

The record contains:

```text
xF : PuncturedEllipticCurve F
cF : HyperbolicOrbicurveModel F
cF_is_quotient_by_neg_one : Prop
fmod_is_fieldOfModuli : Prop
stableReductionOverNonarchimedean : Prop
torsion23RationalOverF : Prop
```

The quotient, field-of-moduli, stable-reduction, and torsion-rationality
clauses remain explicit propositions with proofs. This is intentional: mathlib
does not yet provide the exact IUT objects for hyperbolic orbicurves and their
stack-theoretic quotients, so the formalization records the source obligations
without pretending they are already derived.

`InitialThetaData` now contains `curveModuli : ThetaCurveModuliData Fmod F`
instead of carrying those obligations as unrelated fields. This makes the
dependency on `X_F` and `Fmod` visible to later definitions.

### Lean Declarations

```text
ThetaCurveModuliData
ThetaCurveModuliData.quotientByNegOne
ThetaCurveModuliData.fmodFieldOfModuli
ThetaCurveModuliData.stableReduction
ThetaCurveModuliData.torsion23Rational
InitialThetaData.quotientByNegOne
InitialThetaData.stableReductionOverNonarchimedean
InitialThetaData.torsion23RationalOverF
```

### What This Tests

The example file now verifies:

* construction of the curve/moduli data from `X_F`, `C_F`, and the four named
  source obligations;
* construction of initial theta data using the curve/moduli bundle;
* projection of the quotient-by-`-1`, field-of-moduli, stable-reduction, and
  `2 * 3` torsion-rationality obligations.

### Design Trap Avoided

The trap would be to let the field-of-moduli condition float as an unstructured
field of the final initial-theta record. The new bundle ties that condition to
the specific `X_F` and `C_F` data it is about. This does not solve the moduli
problem yet, but it prevents the next layers from using a moduli assertion that
is detached from the curve.

### Next Step

The next Definition 3.1 target should be the valuation layer: `Vmod = V(Fmod)`,
`V ⊆ V(K)`, the section `V -> Vmod`, and the distinction between bad valuation
sets and good valuation sets. We should first inspect mathlib's finite-place API
for number fields and decide how much of the current placeholder
`ThetaValuationData` can be replaced by actual place types.

## Math Milestone 17: Finite-Place Valuation Layer

Lean files:

* `Iut/Foundations/InitialThetaData.lean`
* `Iut/Foundations/InitialThetaDataExample.lean`

### Source Check

IUT I, Definition 3.1(b),(e) uses `Vmod = V(Fmod)`, a nonempty set
`Vbad_mod` of nonarchimedean valuations of `Fmod`, and a subset
`V ⊆ V(K)` inducing a bijection `V -> Vmod`, i.e. a section of the natural
surjection from valuations of `K` to valuations of `Fmod`. It then defines
bad and good parts by pulling back the bad and good moduli-level sets.

The source also assumes that the residue characteristics of elements of
`Vbad_mod` are odd and prime to `l`, and that `X_F` has bad/multiplicative
reduction at valuations over `Vbad_mod`.

### Lean/API Check

Mathlib has:

```text
NumberField.FinitePlace K
NumberField.FinitePlace.maximalIdeal
NumberField.FinitePlace.add_le
NonarchimedeanHomClass (NumberField.FinitePlace K) K R
```

The finite-place API represents finite places as absolute values associated to
height-one spectra of `𝓞 K`. It gives a real nonarchimedean finite-place type,
so our old arbitrary valuation index types were too weak.

I did not find a ready-made canonical restriction map
`FinitePlace K -> FinitePlace Fmod` with the exact section data needed by IUT
Definition 3.1(e). Therefore the map and section remain explicit fields.

### Lean Decisions

`ThetaValuationData` now has the shape:

```text
ThetaValuationData l Fmod K
```

and uses actual mathlib finite places:

```text
toModuli : NumberField.FinitePlace K -> NumberField.FinitePlace Fmod
chosenLift : NumberField.FinitePlace Fmod -> NumberField.FinitePlace K
toModuli_chosenLift : forall w, toModuli (chosenLift w) = w
badMod : Set (NumberField.FinitePlace Fmod)
```

The selected set `V ⊆ V(K)` is represented as:

```text
ThetaValuationData.selected = Set.range chosenLift
```

The bad and good selected valuations are:

```text
bad  = {v | v in selected and toModuli v in badMod}
good = {v | v in selected and toModuli v notin badMod}
```

Residue characteristic is still a function
`NumberField.FinitePlace Fmod -> Nat`. We record the source obligations that it
is prime, odd, and coprime to `l` on the bad moduli set. A later milestone can
try to derive this from maximal ideals/residue fields.

### Lean Declarations

```text
ThetaValuationData
ThetaValuationData.selected
ThetaValuationData.goodMod
ThetaValuationData.bad
ThetaValuationData.good
ThetaValuationData.chosenLift_mem_selected
ThetaValuationData.toModuli_chosenLift_eq
ThetaValuationData.chosenLift_mem_bad_iff
ThetaValuationData.bad_nonempty
ThetaValuationData.badLift_has_multiplicative_reduction
InitialThetaData.badValuations_nonempty
InitialThetaData.badValuation_has_multiplicative_reduction
```

### What This Tests

The example file now constructs valuation data abstractly over number fields
using `NumberField.FinitePlace Fmod` and `NumberField.FinitePlace K`. It also
verifies that initial theta data consumes this finite-place valuation bundle,
not arbitrary placeholder types.

### Design Trap Avoided

The trap would be to keep proving facts about a polymorphic `Valuation` type
that had no connection to number fields. This milestone forces the valuation
layer to use finite places of the actual fields in the initial theta-data
tower. The remaining explicit map/section fields are not drift: they correspond
to the source's section `V -> Vmod` and to API that is not yet provided by
mathlib in the exact form needed here.

### Next Step

The next target should refine one of the valuation obligations: either connect
`residueCharacteristic` to the maximal ideal/residue field attached to a
finite place, or add the `CK`/`CF` base-change relation from Definition 3.1(d)
so the local bad-reduction and cusp conditions have the right geometric target.
