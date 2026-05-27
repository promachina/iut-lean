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
