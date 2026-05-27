/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.RealLineCopy
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

end ToyModel
end Stage1
end Iut
