# Formalization Notes

These notes are the project diary and the seed of a later paper. Each Lean
milestone should be documented here in ordinary mathematical language: what was
formalized, why the definitions were chosen, what the Lean theorem actually says,
and what trap the design is meant to avoid.

## Method

We are treating Lean as a verification and disambiguation engine. The main rule
is that a Lean theorem should not contain the desired conclusion as a structure
field unless the theorem is explicitly marked as an interface placeholder. When
we introduce a placeholder, the research task is to replace it later by smaller
data and proofs.

This mirrors the "blueprint" style used in large Lean formalization projects:
human-readable mathematical text is kept synchronized with formal declarations.
Examples worth tracking are the Liquid Tensor Experiment blueprint
<https://leanprover-community.github.io/liquid/>, the Fermat's Last Theorem
blueprint <https://imperialcollegelondon.github.io/FLT/blueprint/>, and recent
work on extracting blueprint data from Lean code in LeanArchitect
<https://arxiv.org/abs/2601.22554>.

## Milestone 1: Labeled Real-Line Copies

Lean file: `Iut/Foundations/RealLineCopy.lean`

### Purpose

The Scholze-Stix objection around IUT III, Corollary 3.12 is partly about
identifying several copies of one-dimensional ordered real vector spaces. Their
claim is that consistent identifications leave no room for the required `j^2`
scalings on the Theta side; inserting those scalars produces monodromy. Mochizuki's
position is that the Hodge-theater/log-link/multiradial apparatus makes some
comparisons legitimate precisely because the ring/scheme histories are not
silently identified.

Before formalizing log-volumes or pilot objects, we need a tiny discipline for
copies of the real line:

* a copy has a label;
* a point has a coordinate only relative to its copy;
* a comparison between copies is an explicit transport;
* a transport carries a positive scale, so it preserves the order orientation;
* a loop transport is trivial exactly when its scale is `1`.

This is intentionally much smaller than the IUT situation. Its job is to prevent
the first possible mistake: silently treating all real-number targets as the same
object.

### Lean Declarations

`RealLineCopy.Copy` is a labeled copy of the real line. Its only field is a
string label. This is not mathematically rich, but the label creates an explicit
place where later q-side, Theta-side, abstract-pilot, concrete-pilot, and
holomorphic-hull targets can differ.

`RealLineCopy.Point line` is a coordinate in a specific copy. The coordinate is a
plain real number, but the type records the copy to which the coordinate belongs.
This means a point of the q-copy is not definitionally a point of the Theta-copy.

`RealLineCopy.PositiveScale` is a real scalar with proof that it is positive. We
use positive scalars because the ordered real lines relevant to log-volume
comparisons should not be allowed to reverse order.

`RealLineCopy.Transport source target` is currently just a positive scaling from
one copy to another. Later this may be generalized to affine or abstract ordered
line isomorphisms if the mathematics requires it. For the first milestone,
positive scaling is exactly the structure needed to model identity comparison
versus scalar insertion.

`Transport.PointwiseEqual f g` means two transports induce the same coordinate
map on every point. The theorem
`Transport.pointwiseEqual_iff_scale_eq` proves that, for this model, pointwise
equality is equivalent to equality of scale factors.

`Transport.TrivialMonodromy f` means a loop transport is pointwise equal to the
identity transport. The theorem
`Transport.trivialMonodromy_iff_scale_eq_one` proves the core fact:

```text
a loop has trivial monodromy iff its scale is 1.
```

`Transport.scalarLoop_nontrivial_of_scale_ne_one` is the first formal expression
of the Scholze-Stix-style warning: if a scalar loop has scale not equal to `1`,
then it is not a trivial identification.

### What This Does Not Prove

This milestone does not prove anything about IUT, Corollary 3.12, q-pilots,
Theta-pilots, Frobenioids, Hodge theaters, or log-volumes.

It only proves a small control theorem for a future model: if we later insert a
`j^2` scaling into a closed comparison diagram, then we must either show that the
resulting loop is not meant to be trivial, or prove that the relevant
indeterminacy/hull operation changes the comparison relation. We cannot call it
an ordinary identity unless the scale is `1`.

### Design Trap Avoided

The dangerous shortcut would be to represent every log-volume target simply as
`Real`. That would erase the distinction between q-side and Theta-side real
coordinates before we have proved that such erasure is legitimate. This file does
the opposite: it makes every erasure or comparison pass through an explicit
transport.

## Milestone 2: Coherent Transport Diagrams

Lean file: `Iut/Foundations/TransportDiagram.lean`

### Source Check

Before implementing this milestone, we rechecked the local primary texts.

Scholze-Stix say that, because the argument compares real numbers and several
ordered one-dimensional real vector spaces arise, it is critical to spell out all
identifications of copies of real numbers. In their diagnosis, adding `j^2`
scalars to the left side of the diagram produces monodromy; with consistent
identifications, those scalars must be omitted.

Mochizuki's IUT III, Remark 3.12.2, gives a toy model with two distinct labeled
copies `qR` and `ThetaR` of the real numbers. He emphasizes that forgetting the
distinct labels makes the assignments incompatible, while the labels and the
abstract symbol make simultaneous logical consideration possible. Later, an
assignment with indeterminacies is supposed to be intrinsically associated to the
q-side assignment even after the copies are identified.

Mochizuki's April 2026 progress report says that the Stage 1 Lean target should
focus on the simultaneous comparison of the q-pilot and Theta-pilot, with SHE
and IPL as part of the `3.11.5 => 3.12` package.

The formal move below captures only the elementary "consistent identification"
side of this discussion. It does not model the claimed indeterminacy/hull escape
route yet.

### Purpose

Milestone 1 handled a single loop. Milestone 2 handles two parallel comparison
paths between the same labeled real-line copies. This is closer to the diagrams
in the Scholze-Stix discussion: one path is a baseline comparison, while another
path is the same comparison with an extra scalar inserted.

The intended control theorem is:

```text
if a transport and its scalar-rescaled version form a coherent parallel diagram,
then the inserted scalar is 1.
```

Equivalently:

```text
if the inserted scalar is not 1, the parallel diagram is not coherent.
```

### Lean Declarations

`Transport.rescale s f` takes a transport `f` and multiplies its scale by the
positive scale `s`.

`Transport.ParallelPair source target` is a pair of parallel transports between
the same labeled copies.

`Transport.ParallelPair.Coherent p` means that the two paths are pointwise equal
as maps on coordinates.

`Transport.ParallelPair.coherent_iff_scale_eq` proves that, in this model,
coherence of parallel paths is equivalent to equality of their scale factors.

`Transport.coherent_rescale_iff_scale_eq_one` proves the central theorem of this
milestone:

```text
Coherent(f, rescale s f) iff s = 1.
```

`Transport.incoherent_rescale_of_scale_ne_one` packages the contrapositive:
nontrivial scalar insertion prevents coherence.

### Design Trap Avoided

The trap would be to define a "commutative diagram" as a proposition field and
then freely use it without understanding what it forces. Here we define
coherence as pointwise equality of transports, then prove Lean's reduction of
that condition to equality of scales. This keeps the mathematical content small
and inspectable.

### Next Step

The next milestone should introduce q-side and Theta-side log-volume assignments
as points in labeled real-line copies. Then we can express Mochizuki's toy model
directly:

```text
star |-> q(-h) in qR
star |-> Theta(-2h) in ThetaR
```

and separately express the indeterminacy version:

```text
star |-> Theta(R_{<= -2h + epsilon}) in ThetaR.
```

That will let us distinguish three things in Lean: labeled simultaneous
assignments, forced unlabeled identification, and comparison through an explicit
transport or indeterminacy relation.

## Milestone 3: The IUT III Toy Model

Lean file: `Iut/Stage1/ToyModel.lean`

### Source Check

This milestone is tied directly to IUT III, Remark 3.12.2, especially the
subparagraphs `(atoy)` through `(ftoy)`. Mochizuki describes two distinct labeled
copies `qR` and `ThetaR`, an abstract symbol `*`, and assignments

```text
lambda_q     : * |-> q(-h)        in qR
lambda_Theta : * |-> Theta(-2h)   in ThetaR.
```

He then says that if the labels `q` and `Theta` are forgotten, the assignments
become incompatible because `-h != -2h` for `h > 0`. He replaces the second
assignment by an indeterminacy version

```text
lambda_Theta^Ind : * |-> Theta(R_{<= -2h + epsilon})
```

and concludes formally that membership of `-h` in this region gives
`-h <= -2h + epsilon`, hence `h <= epsilon`.

This is also responsive to Scholze-Stix, who emphasize that all identifications
between the ordered one-dimensional real vector spaces must be spelled out. The
toy model is where we can spell out the smallest possible version of that issue.

### Lean Declarations

`ToyModel.qLine` and `ToyModel.thetaLine` are the two labeled copies.

`ToyModel.qAssignment h` is the point with coordinate `-h` in `qLine`.

`ToyModel.thetaAssignment h` is the point with coordinate `-2h` in `thetaLine`.

`ToyModel.ForcedUnlabeledEquality h` is the proposition obtained by forgetting
the two labels and asserting equality of the resulting coordinates in one
ambient copy of `Real`.

The theorem

```text
forcedUnlabeledEquality_iff_eq_zero
```

proves that this forced equality is equivalent to `h = 0`. The theorem

```text
forcedUnlabeledEquality_contradicts_positive
```

packages the expected contradiction for `h > 0`.

`ToyModel.thetaIndeterminacyRegion h epsilon x` is the coordinate predicate
`x <= -2h + epsilon`.

`ToyModel.QInThetaIndeterminacyAfterForgetting h epsilon` says that the
q-coordinate `-h` lies in this region after labels are forgotten.

The theorem

```text
qInThetaIndeterminacy_iff_bound
```

proves the exact arithmetic equivalence:

```text
-h in R_{<= -2h + epsilon}  iff  h <= epsilon.
```

### What This Tests

This milestone tests both sides of the toy-model passage.

First, the naive forced identification of the exact assignments is impossible
for positive `h`. This matches Mochizuki's own warning in `(atoy)` and the
Scholze-Stix insistence that identifications of real-line copies must be
tracked.

Second, the indeterminacy-region replacement has the advertised arithmetic
effect: once one has justified membership of `-h` in `R_{<= -2h + epsilon}`,
Lean confirms that the formal bound `h <= epsilon` follows.

### Design Trap Avoided

The trap would be to make the indeterminacy step a field such as
`bound : h <= epsilon`. We do not do that. We define the region membership
predicate and prove that the bound is equivalent to membership. The hard future
mathematics is therefore isolated: one must justify the membership, not the
bound directly.

### Next Step

The next milestone should connect this toy model back to explicit transports:
instead of "forgetting labels" by immediately reading both coordinates in `Real`,
we should express comparison through a named transport from `qLine` to
`thetaLine`. This will let us ask whether a proposed comparison path is exact,
scalar-rescaled, or indeterminacy-valued.

## Milestone 4: Toy Model Through Named Transports

Lean file: `Iut/Stage1/ToyModel.lean`

### Source Check

This milestone continues the same source check as Milestone 3. The relevant
mathematical tension is:

* Mochizuki's toy model begins with distinct labeled copies `qR` and `ThetaR`.
* Forgetting the labels directly makes the exact assignments `-h` and `-2h`
  incompatible when `h > 0`.
* Scholze-Stix stress that every identification between ordered one-dimensional
  real vector spaces must be made explicit.

Milestone 4 implements the explicit-identification version: instead of simply
forgetting labels, we compare the q-assignment to the Theta-assignment through a
named positive-scale transport from `qLine` to `thetaLine`.

### Lean Declarations

`ToyModel.TransportedExactEquality f h` says that applying the named transport
`f : Transport qLine thetaLine` to the q-point `q(-h)` gives the exact Theta
point `Theta(-2h)`.

The theorem

```text
transportedExactEquality_iff_scale_eq_two
```

proves that, for `h != 0`, exact transported equality is equivalent to the
transport scale being `2`.

This is a useful normalization check. In the raw coordinate-forgetting model,
equality of `-h` and `-2h` forced `h = 0`. Once a named transport is allowed,
exact equality can be recovered, but only by making the transport carry the
nontrivial scale `2`.

`ToyModel.unitQToTheta` is the unit-scale transport from the q-line to the
Theta-line. The theorem

```text
unitQToTheta_not_transportedExactEquality
```

shows that this unit comparison cannot send `q(-h)` to `Theta(-2h)` when
`h > 0`.

The more general theorem

```text
transportedUnitEquality_contradicts_positive
```

says the same thing for any transport whose scale is `1`.

`ToyModel.TransportedQInThetaIndeterminacy f h epsilon` is the
transport-sensitive version of the indeterminacy-region membership. It says that
the transported q-coordinate lies in the Theta-side region
`R_{<= -2h + epsilon}`.

The theorem

```text
unitTransportedQInThetaIndeterminacy_iff_bound
```

checks that the unit-transport version recovers the arithmetic equivalence from
Milestone 3: membership is equivalent to `h <= epsilon`.

### What This Tests

The milestone separates three notions that must remain distinct in later work:

1. Raw label-forgetting.
2. Exact comparison through a named transport.
3. Indeterminacy-region comparison through a named transport.

This matters because a proof may legitimately compare two labeled copies only
after specifying the comparison map. The formal result here says that the
comparison map itself carries mathematical content: exact comparison of the toy
assignments forces a nontrivial scale.

### Design Trap Avoided

The trap would be to say "identify qR and ThetaR" without recording whether the
identification has scale `1`, scale `2`, scale `j^2`, or is not an exact
identification at all but an indeterminacy-valued relation. This milestone
forces that choice into Lean data.

### Next Step

The next milestone should stop treating indeterminacy as just a predicate on
coordinates and introduce a small abstract interface for indeterminacy-valued
relations between labeled real-line copies. The immediate goal is to distinguish
"pointwise equality" from "membership in a hull/region after transport" at the
type level.
