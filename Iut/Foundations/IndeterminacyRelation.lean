/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportDiagram

/-!
Region-valued comparisons between labeled real-line copies.

This file separates exact equality from indeterminacy-valued membership. In the
IUT III toy model, the exact target `Theta(-2h)` is replaced by the region
`Theta(R_{<= -2h + epsilon})`. Later IUT formalization work will need a richer
notion of hulls and regions; for now, a region is simply a predicate on points of
a labeled real-line copy.
-/

namespace Iut
namespace RealLineCopy

/-- A region in a labeled real-line copy. -/
structure Region (line : Copy) where
  Contains : Point line -> Prop

namespace Region

variable {line : Copy}

/-- The singleton region containing exactly one point. -/
def singleton (x : Point line) : Region line :=
  { Contains := fun y => y.coord = x.coord }

/-- The upper ray consisting of points whose coordinate is at most `bound`. -/
def upperRay (line : Copy) (bound : Real) : Region line :=
  { Contains := fun y => y.coord <= bound }

@[simp]
theorem singleton_contains {x y : Point line} :
    (singleton x).Contains y ↔ y.coord = x.coord :=
  Iff.rfl

@[simp]
theorem upperRay_contains {line : Copy} {bound : Real} {y : Point line} :
    (upperRay line bound).Contains y ↔ y.coord <= bound :=
  Iff.rfl

end Region

/-- A named transport together with a target-side region. -/
structure RegionComparison (source target : Copy) where
  transport : Transport source target
  targetRegion : Region target

namespace RegionComparison

variable {source target : Copy}

/-- A source point satisfies a region comparison when its transported image lies in the region. -/
def Holds (comparison : RegionComparison source target) (x : Point source) : Prop :=
  comparison.targetRegion.Contains (Transport.map comparison.transport x)

/-- Exact comparison is region comparison against a singleton target. -/
def exact (transport : Transport source target) (targetPoint : Point target) :
    RegionComparison source target :=
  { transport := transport, targetRegion := Region.singleton targetPoint }

/-- Upper-ray comparison is region comparison against a coordinate upper bound. -/
def upperRay (transport : Transport source target) (bound : Real) :
    RegionComparison source target :=
  { transport := transport, targetRegion := Region.upperRay target bound }

theorem exact_holds_iff (transport : Transport source target)
    (targetPoint : Point target) (sourcePoint : Point source) :
    Holds (exact transport targetPoint) sourcePoint ↔
      (Transport.map transport sourcePoint).coord = targetPoint.coord :=
  Iff.rfl

theorem upperRay_holds_iff (transport : Transport source target)
    (bound : Real) (sourcePoint : Point source) :
    Holds (upperRay transport bound) sourcePoint ↔
      (Transport.map transport sourcePoint).coord <= bound :=
  Iff.rfl

end RegionComparison

end RealLineCopy
end Iut
