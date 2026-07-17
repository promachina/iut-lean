/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1StepXI
import Iut.Stage1.IUTStage1Experiments.AdditiveHaar

/-!
Bridge from the additive-Haar/Theorem 1.10 formula-matching tower to the
canonical Step (xi) p-adic arithmetic-degree boundary.

`IUTStage1Experiments.AdditiveHaar` sits below the Step (xi) core in the import
graph, so the projections from its source-backed formula-matching records to
the canonical Step (xi) records live here.
-/

namespace Iut
namespace Stage1
namespace Experiments

open RealLineCopy
open scoped BigOperators
open scoped NormedField
open scoped Valued

universe u v w x y z

namespace IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource

variable {ι : Type u} [Fintype ι]
variable {localPrime : ι -> Nat}
variable [∀ place : ι, Fact (Nat.Prime (localPrime place))]
variable {localField : ι -> Type v}
variable [(place : ι) -> NontriviallyNormedField (localField place)]
variable [∀ place : ι, ProperSpace (localField place)]
variable [∀ place : ι, IsUltrametricDist (localField place)]
variable [(place : ι) -> MeasurableSpace (localField place)]
variable [∀ place : ι, BorelSpace (localField place)]
variable [∀ place : ι, LocallyCompactSpace (localField place)]
variable [∀ place : ι, IsTopologicalAddGroup (localField place)]
variable [(place : ι) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : ι,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {α : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
/--
Project the experiment-layer p-adic Haar-index source to the canonical
Step~(xi) p-adic Haar-index source.
-/
noncomputable def toCorePadicUnitBallHaarIndexDefectSource
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
      ι localPrime localField α hullSystem :=
  { unitBallHaarSource := source.unitBallHaarSource,
    normalizedPlace := source.normalizedPlace }

theorem localHaarNormalizationDefect_eq_core
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem)
    (place : ι) :
    source.localHaarNormalizationDefect place =
      source.toCorePadicUnitBallHaarIndexDefectSource.localHaarNormalizationDefect
        place := by
  rfl

theorem toCorePadicUnitBallHaarIndexDefectSource_endpoint
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem) :
    source.toCorePadicUnitBallHaarIndexDefectSource.Endpoint :=
  source.toCorePadicUnitBallHaarIndexDefectSource.endpoint

end IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource

namespace IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project additive-Haar formula matching to the canonical p-adic
Step~(xi) arithmetic formula matching source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.localizedStepXISource :=
  { padicUnitBallHaarDefectSource :=
      source.iutIVArithmeticDefectSource.padicHaarDefectSource
        |>.toCorePadicUnitBallHaarIndexDefectSource,
    localStepXI_eq_arithmeticDegreePart :=
      source.localStepXI_eq_arithmeticDegreePart,
    localPrimeErrorContribution_eq_padicIndex_main := by
      intro place
      have hprime :=
        source.localPrimeErrorContribution_eq_iutIVDefect_main place
      have hdefect :=
        source.iutIVArithmeticDefectSource.localIUTIVArithmeticDefect_eq_padicHaarIndex place
      have hcore :=
        source.iutIVArithmeticDefectSource.padicHaarDefectSource
          |>.localHaarNormalizationDefect_eq_core place
      rw [hprime, hdefect, hcore] }

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource

namespace IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the stricter p-adic prime-error formula-matching source to the
canonical Step~(xi) p-adic arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.primeErrorPadicDefectMainSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.localizedStepXISource :=
  source.toIUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource

namespace IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the fully split additive-Haar formula source to the canonical p-adic
Step~(xi) arithmetic formula source.

Here the Step~(xi) arithmetic-degree equality is no longer primitive: it is
derived inside `arithmeticDegreeCalibrationSource` from local determinant
weights and adjusted raw log-volumes.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.primeErrorPadicDefectMainSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toIUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource

set_option linter.style.longLine false

namespace IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the formula-gap matched, arithmetic-degree calibrated p-adic source to
the canonical p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

namespace IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the valuation-ball formula-gap matched arithmetic-degree/p-adic source
to the canonical p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

set_option linter.style.longLine true

namespace IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the valuation-ball arithmetic-degree controlled source to the
canonical p-adic Step~(xi) arithmetic formula matching source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toAdditiveHaarArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

end IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource

end Experiments
end Stage1
end Iut
