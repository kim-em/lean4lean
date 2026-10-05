import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction

/-! Select the actual one-domain Pi and its original children from a genuine
constant header. All prefix, location, and context evidence is computed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem singleHeaderDomain_eq
    (signature : ConstantTelescope expression) (domains : signature.domains = [C]) :
    expression = .forallE C signature.result := by
  simpa only [domains, wrapForalls, List.foldr_cons, List.foldr_nil]
    using signature.type_eq

structure HeaderSinglePi
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C]) where
  cu : VLevel
  dv : VLevel
  hcu : cu.WF U
  hdv : dv.WF U
  domain : EndpointRef origin.source U [] C (.sort cu)
  body : EndpointState origin.source U [C] signature.result (.sort dv)
  location : Located (origin.familyHeader levelsWF).reference (.ref domain)
  lineage : location.contextDerivation .nil = .nil
  route : PrefixRoute origin.source U [] (.forallE C signature.result)
    ((EndpointState.ref (origin.familyHeader levelsWF).reference).cast
      (singleHeaderDomain_eq signature domains) rfl)
    (.pi hcu hdv (.ref domain) body)

private theorem singleHeaderPiExists
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C]) :
    Nonempty (HeaderSinglePi origin levelsWF signature domains) := by
  let selected := piPrefix ((Located.here (root := (origin.familyHeader levelsWF).reference)).castExpression
    (singleHeaderDomain_eq signature domains))
  obtain ⟨domain, domainEq⟩ := selected.view.location.originalDomains.1
  let location : Located (origin.familyHeader levelsWF).reference (.ref domain) :=
    domainEq ▸ .piDomain selected.view.location
  have lineage : location.contextDerivation .nil = .nil := by
    cases location.contextDerivation .nil
    rfl
  exact ⟨⟨selected.view.domainLevel, selected.view.bodyLevel, selected.view.domainWF,
    selected.view.bodyWF, domain, selected.view.body, location, lineage, domainEq ▸ selected.route⟩⟩

/-- No domain/body/prefix witness is a caller input. The selected source is
literally the source retained by this genuine header origin. -/
noncomputable def _root_.Lean4Lean.VEnv.ConstantHeaderOrigin.singlePiSyntax
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C]) :
    HeaderSinglePi origin levelsWF signature domains :=
  Classical.choice (singleHeaderPiExists origin levelsWF signature domains)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
