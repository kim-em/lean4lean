import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! Pure row operations preserve the annotations of the exact certificates
which they retain or rebuild. These operations do not open original proofs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace ControlledStoredQuery
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint}

def certPad (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (.pad certificate)) where
  annotation := .pad ready.annotation
  within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within
  sponsored := ready.sponsored

def certDown {certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (highProfile : Profile (n + 1)) footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (.down certificate)) where
  annotation := .down ready.annotation
  within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within
  sponsored := ready.sponsored

def certMap (change : AtomView env U registry target a b)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (.map change certificate)) where
  annotation := .map change ready.annotation
  within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within
  sponsored := ready.sponsored

def certSupport (action : SupportAction env U registry target n)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (.support action certificate)) where
  annotation := .support action ready.annotation
  within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within
  sponsored := ready.sponsored

def certRetag (formed : profile.HasType (.sort next))
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (.observe (.code certificate) formed)) where
  annotation := .observe (.code ready.annotation) formed
  within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichObs.headDepth] using ready.within
  sponsored := ready.sponsored

 theorem codeAction
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (action : SortableCodeAction env U registry target relevant profile next output)
    (resources : footprint.Available available) :
    ∃ outputFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next output outputFootprint,
      outputFootprint.Available available ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate result)) := by
  obtain ⟨fp, result, annotation, resources, worlds, depth⟩ :=
    certificate.codeAction_worlds_depth ready.annotation action resources
  refine ⟨fp, result, resources, ⟨annotation, ?_, ?_⟩⟩
  · intro control active
    exact Nat.le_trans (depth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (worlds member)
end ControlledStoredQuery

namespace RichPiRowCertificate.Controlled
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (key : Key n) result}

def atFlag (ready : row.Controlled controls frontier) (formed : result.HasType (.sort next)) :
    (row.atFlag formed).Controlled controls frontier :=
  ⟨ready.domain, ready.body.certRetag formed⟩

def pad (ready : row.Controlled controls frontier) (henv : env.Ordered) :
    (row.pad henv).Controlled controls frontier :=
  ⟨ready.domain.certPad, ready.body.certPad⟩

def mapOutput (ready : row.Controlled controls frontier)
    (change : AtomView env U registry target old new) :
    (row.map_output change).Controlled controls frontier :=
  ⟨ready.domain, ready.body.certMap change⟩

def domainRekey (ready : row.Controlled controls frontier)
    (henv : env.Ordered) (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    (row.domainRekey henv path typed formed related).Controlled controls frontier :=
  ⟨ready.domain, ready.body⟩

theorem codeAction (ready : row.Controlled controls frontier)
    (action : SortableCodeAction env U registry target relevant result next output) :
    ∃ changed : RichPiRowCertificate env U registry target locals σ available next domainNode bodyNode key output,
      Nonempty (changed.Controlled controls frontier) := by
  obtain ⟨footprint, certificate, resources, ⟨certificateReady⟩⟩ :=
    ready.body.codeAction action (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, covered, outsideAvailable⟩ := Footprint.pack_available resources
    (fun need member => (row.pack.atomized_localNeeds need member).1)
    (fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present))
  exact ⟨{ row with
    bodyFootprint := footprint
    body := certificate
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable }, ⟨⟨ready.domain, certificateReady⟩⟩⟩
end RichPiRowCertificate.Controlled

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
