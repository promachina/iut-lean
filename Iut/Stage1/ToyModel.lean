/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportDiagram
import Mathlib.Tactic

/-!
The real-valued toy model from IUT III, Remark 3.12.2.

This file formalizes only the elementary arithmetic in Mochizuki's toy model:

* with distinct labels, `q(-h)` and `Theta(-2h)` are assignments into different
  copies of the real line;
* if one forgets those labels and forces the coordinates to agree, then `h = 0`;
* replacing `Theta(-2h)` by the indeterminacy region `R_{<= -2h + epsilon}` turns
  membership of `-h` in that region into the bound `h <= epsilon`.

This is not yet a formalization of the IUT indeterminacy mechanism. It is the
small real-arithmetic target that the later mechanism must justify.
-/

namespace Iut
namespace Stage1
namespace ToyModel

open RealLineCopy

/-- The q-side labeled copy in the toy model. -/
def qLine : Copy :=
  { label := "q" }

/-- The Theta-side labeled copy in the toy model. -/
def thetaLine : Copy :=
  { label := "Theta" }

/-- The toy q-assignment `* |-> q(-h)`. -/
def qAssignment (h : Real) : Point qLine :=
  point qLine (-h)

/-- The toy Theta-assignment `* |-> Theta(-2h)`. -/
def thetaAssignment (h : Real) : Point thetaLine :=
  point thetaLine (-(2 * h))

/--
The proposition obtained by forgetting the distinct labels and forcing the two
coordinates to be equal in a single ambient copy of `Real`.
-/
def ForcedUnlabeledEquality (h : Real) : Prop :=
  (qAssignment h).coord = (thetaAssignment h).coord

theorem forcedUnlabeledEquality_iff_eq_zero (h : Real) :
    ForcedUnlabeledEquality h ↔ h = 0 := by
  unfold ForcedUnlabeledEquality qAssignment thetaAssignment point
  constructor
  · intro hcoord
    linarith
  · intro hz
    linarith

theorem forcedUnlabeledEquality_contradicts_positive {h : Real} (hh : 0 < h) :
    ¬ ForcedUnlabeledEquality h := by
  intro hforced
  have hz : h = 0 := (forcedUnlabeledEquality_iff_eq_zero h).mp hforced
  linarith

/--
The toy indeterminacy region `R_{<= -2h + epsilon}`.

We keep the region as a predicate on coordinates; the label of the ambient copy
will be supplied by the assignment using it.
-/
def thetaIndeterminacyRegion (h epsilon x : Real) : Prop :=
  x <= -(2 * h) + epsilon

/-- After forgetting labels, the q-coordinate `-h` lies in the Theta indeterminacy region. -/
def QInThetaIndeterminacyAfterForgetting (h epsilon : Real) : Prop :=
  thetaIndeterminacyRegion h epsilon (-h)

theorem qInThetaIndeterminacy_iff_bound (h epsilon : Real) :
    QInThetaIndeterminacyAfterForgetting h epsilon ↔ h <= epsilon := by
  unfold QInThetaIndeterminacyAfterForgetting thetaIndeterminacyRegion
  constructor
  · intro hmem
    linarith
  · intro hbound
    linarith

theorem bound_of_qInThetaIndeterminacy {h epsilon : Real}
    (hmem : QInThetaIndeterminacyAfterForgetting h epsilon) : h <= epsilon :=
  (qInThetaIndeterminacy_iff_bound h epsilon).mp hmem

theorem qInThetaIndeterminacy_of_bound {h epsilon : Real} (hbound : h <= epsilon) :
    QInThetaIndeterminacyAfterForgetting h epsilon :=
  (qInThetaIndeterminacy_iff_bound h epsilon).mpr hbound

/--
Exact comparison through a named transport from the q-line to the Theta-line.

This is the transport-sensitive replacement for immediately forgetting labels.
-/
def TransportedExactEquality (f : Transport qLine thetaLine) (h : Real) : Prop :=
  (Transport.map f (qAssignment h)).coord = (thetaAssignment h).coord

theorem transportedExactEquality_iff_scale_eq_two (f : Transport qLine thetaLine)
    {h : Real} (hh : h ≠ 0) :
    TransportedExactEquality f h ↔ f.scale.val = 2 := by
  unfold TransportedExactEquality qAssignment thetaAssignment point Transport.map
  constructor
  · intro hcoord
    have hmul : f.scale.val * h = 2 * h := by
      linarith
    exact mul_right_cancel₀ hh hmul
  · intro hscale
    simp [hscale]

/-- The unit-scale transport from q-line coordinates to Theta-line coordinates. -/
def unitQToTheta : Transport qLine thetaLine :=
  { scale := PositiveScale.one }

@[simp]
theorem unitQToTheta_scale_val : unitQToTheta.scale.val = 1 :=
  rfl

theorem unitQToTheta_not_transportedExactEquality {h : Real} (hh : 0 < h) :
    ¬ TransportedExactEquality unitQToTheta h := by
  intro htransport
  have hscale :
      unitQToTheta.scale.val = 2 :=
    (transportedExactEquality_iff_scale_eq_two unitQToTheta (ne_of_gt hh)).mp htransport
  norm_num at hscale

theorem transportedUnitEquality_contradicts_positive {h : Real} (hh : 0 < h)
    {f : Transport qLine thetaLine} (hunit : f.scale.val = 1) :
    ¬ TransportedExactEquality f h := by
  intro htransport
  have hscale :
      f.scale.val = 2 :=
    (transportedExactEquality_iff_scale_eq_two f (ne_of_gt hh)).mp htransport
  linarith

/--
Indeterminacy-region comparison through a named transport.

This says that the transported q-coordinate lands in the Theta-side region
`R_{<= -2h + epsilon}`.
-/
def TransportedQInThetaIndeterminacy (f : Transport qLine thetaLine)
    (h epsilon : Real) : Prop :=
  thetaIndeterminacyRegion h epsilon (Transport.map f (qAssignment h)).coord

theorem transportedQInThetaIndeterminacy_iff (f : Transport qLine thetaLine)
    (h epsilon : Real) :
    TransportedQInThetaIndeterminacy f h epsilon ↔
      f.scale.val * (-h) <= -(2 * h) + epsilon := by
  rfl

theorem unitTransportedQInThetaIndeterminacy_iff_bound (h epsilon : Real) :
    TransportedQInThetaIndeterminacy unitQToTheta h epsilon ↔ h <= epsilon := by
  unfold TransportedQInThetaIndeterminacy thetaIndeterminacyRegion
    unitQToTheta qAssignment point Transport.map PositiveScale.one
  constructor
  · intro hmem
    linarith
  · intro hbound
    linarith

end ToyModel
end Stage1
end Iut
