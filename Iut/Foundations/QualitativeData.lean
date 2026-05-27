/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportedRegionFamily

/-!
Structured but inert qualitative data for algorithmic outputs.

These records give more shape to the names IPL, SHE, and APT without assigning
any mathematical consequences to them. They are bookkeeping objects; bridge
theorems must still be supplied separately.
-/

namespace Iut
namespace RealLineCopy

namespace QualitativeData

variable {source target : Copy} {index : Type u}

/-- Inert identifier for a prime strip or prime-strip-like bookkeeping object. -/
structure PrimeStripId where
  label : String

/-- Which side of a Hodge-theater comparison an identifier belongs to. -/
inductive HodgeTheaterSide where
  | domain
  | codomain
  | intermediate
deriving DecidableEq, Repr

/-- Inert identifier for a Hodge theater in the qualitative bookkeeping layer. -/
structure HodgeTheaterId where
  side : HodgeTheaterSide
  label : String

/-- Inert identifier for a language/common-expression context. -/
structure CommonLanguageId where
  label : String

/-- Inert identifier for an APT-style construction mechanism. -/
structure TransportMechanismId where
  label : String

/-- Inert relation record for an IPL-style link between prime strips. -/
structure PrimeStripLink where
  source : PrimeStripId
  target : PrimeStripId
  linkLabel : String

/-- Inert record for input-prime-strip-link style data. -/
structure IPLDatum (family : TransportedRegionFamily source target index) where
  inputPrimeStrip : PrimeStripId
  outputPrimeStrip : PrimeStripId
  choicePrimeStrip : index -> PrimeStripId
  link : PrimeStripLink

/-- A named arithmetic holomorphic structure in the toy bookkeeping layer. -/
structure HolomorphicStructure where
  theater : HodgeTheaterId
  structureLabel : String

/-- Inert relation record for simultaneous expression in a common context. -/
structure SharedHolomorphicContext where
  domainStructure : HolomorphicStructure
  codomainStructure : HolomorphicStructure
  commonLanguage : CommonLanguageId

/-- Inert record for simultaneous-holomorphic-expressibility style data. -/
structure SHEDatum (family : TransportedRegionFamily source target index) where
  sharedContext : SharedHolomorphicContext

def HasStructuredSHE (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (SHEDatum family)

/--
First non-inert local context for simultaneous holomorphic expressibility.

This still does not produce a comparison bound or an endpoint. It records the
two holomorphic structures, the common expression language, the q- and
Theta-side pilot structures, a validity proposition for simultaneous expression,
and an explicit guard that the two Hodge-theater histories are not being
identified.
-/
structure StructuredSHEContext
    (family : TransportedRegionFamily source target index) where
  domainStructure : HolomorphicStructure
  codomainStructure : HolomorphicStructure
  commonLanguage : CommonLanguageId
  qPilotStructure : HolomorphicStructure
  thetaPilotStructure : HolomorphicStructure
  q_pilot_in_codomain :
    qPilotStructure.theater = codomainStructure.theater
  theta_pilot_in_domain :
    thetaPilotStructure.theater = domainStructure.theater
  simultaneous_valid : Prop
  simultaneous_valid_holds : simultaneous_valid
  histories_not_identified :
    domainStructure.theater.side ≠ codomainStructure.theater.side

namespace StructuredSHEContext

variable {family : TransportedRegionFamily source target index}

def sharedContext (context : StructuredSHEContext family) :
    SharedHolomorphicContext :=
  { domainStructure := context.domainStructure,
    codomainStructure := context.codomainStructure,
    commonLanguage := context.commonLanguage }

def sheDatum (context : StructuredSHEContext family) : SHEDatum family :=
  { sharedContext := context.sharedContext }

theorem hasStructuredSHE (context : StructuredSHEContext family) :
    HasStructuredSHE family :=
  ⟨context.sheDatum⟩

theorem qPilotTheater_eq_codomain
    (context : StructuredSHEContext family) :
    context.qPilotStructure.theater =
      context.codomainStructure.theater :=
  context.q_pilot_in_codomain

theorem thetaPilotTheater_eq_domain
    (context : StructuredSHEContext family) :
    context.thetaPilotStructure.theater =
      context.domainStructure.theater :=
  context.theta_pilot_in_domain

theorem simultaneousValid (context : StructuredSHEContext family) :
    context.simultaneous_valid :=
  context.simultaneous_valid_holds

theorem domainHistory_ne_codomainHistory
    (context : StructuredSHEContext family) :
    context.domainStructure.theater.side ≠
      context.codomainStructure.theater.side :=
  context.histories_not_identified

theorem sheDatum_sharedContext
    (context : StructuredSHEContext family) :
    context.sheDatum.sharedContext = context.sharedContext :=
  rfl

end StructuredSHEContext

/-- Inert record for algorithmic-parallel-transport style data. -/
structure APTDatum (family : TransportedRegionFamily source target index) where
  mechanism : TransportMechanismId
  outputFamily : TransportedRegionFamily source target index
  output_eq_family : outputFamily = family

def HasStructuredIPL (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (IPLDatum family)

def HasStructuredAPT (family : TransportedRegionFamily source target index) : Prop :=
  Nonempty (APTDatum family)

/-- Structured evidence for all three qualitative properties of an output family. -/
structure StructuredCertificate (family : TransportedRegionFamily source target index) where
  ipl : IPLDatum family
  she : SHEDatum family
  apt : APTDatum family

namespace StructuredCertificate

variable {family : TransportedRegionFamily source target index}

theorem hasStructuredIPL (certificate : StructuredCertificate family) :
    HasStructuredIPL family :=
  ⟨certificate.ipl⟩

theorem hasStructuredSHE (certificate : StructuredCertificate family) :
    HasStructuredSHE family :=
  ⟨certificate.she⟩

theorem hasStructuredAPT (certificate : StructuredCertificate family) :
    HasStructuredAPT family :=
  ⟨certificate.apt⟩

end StructuredCertificate

theorem apt_output_eq_family {family : TransportedRegionFamily source target index}
    (hapt : HasStructuredAPT family) :
    ∃ datum : APTDatum family, datum.outputFamily = family := by
  rcases hapt with ⟨datum⟩
  exact ⟨datum, datum.output_eq_family⟩

end QualitativeData

end RealLineCopy
end Iut
