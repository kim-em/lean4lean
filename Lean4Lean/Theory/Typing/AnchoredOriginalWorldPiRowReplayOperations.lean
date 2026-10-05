import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableReplay

/-! Input adaptation rebuilds the actual body certificate and its annotation
jointly. The finite binder pack belongs to that same output certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private repeated_available from Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace ControlledStoredQuery
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}

noncomputable def certUnion
    {first : RichCert sourceEnv env U registry target node locals σ relevant (left : Profile n) firstFootprint}
    {second : RichCert sourceEnv env U registry target node locals σ relevant right secondFootprint}
    (firstReady : ControlledStoredQuery controls frontier (.certificate first))
    (secondReady : ControlledStoredQuery controls frontier (.certificate second)) :
    ControlledStoredQuery controls frontier (.certificate (.union first second)) where
  annotation := .union firstReady.annotation secondReady.annotation
  within := by
    intro control active
    simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using
      Nat.max_le.mpr ⟨firstReady.within control active, secondReady.within control active⟩
  sponsored := by
    intro world member
    rcases List.mem_append.mp member with member | member
    · exact firstReady.sponsored world member
    · exact secondReady.sponsored world member

theorem mapProfileView
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant (support : Profile n) footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (change : ProfileView env U registry target (input : Profile n) output) :
    ∃ changed : RichCert sourceEnv env U registry target node locals σ relevant
      (change.mapType support) (List.replicate (input.length + 1) footprint).flatten,
      Nonempty (ControlledStoredQuery controls frontier (.certificate changed)) := by
  match input, output, change with
  | _, _, .nil =>
    simp only [ProfileView.mapType, List.length_nil, Nat.zero_add, List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
    change ∃ changed : RichCert sourceEnv env U registry target node locals σ relevant support (footprint ++ []),
      Nonempty (ControlledStoredQuery controls frontier (.certificate changed))
    rw [List.append_nil]
    exact ⟨certificate, ⟨ready⟩⟩
  | _, _, .cons head tail =>
    obtain ⟨changed, ⟨changedReady⟩⟩ := ready.mapProfileView tail
    simp only [ProfileView.mapType, List.length_cons, List.replicate_succ, List.flatten_cons]
    exact ⟨.union (.map head certificate) changed, ⟨(ready.certMap head).certUnion changedReady⟩⟩
termination_by sizeOf change

end ControlledStoredQuery

namespace RichPiRowCertificate.Controlled
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (key : Key n) result}

theorem inputView (ready : row.Controlled controls frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input) :
    ∃ changed : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (inputKey key input) result,
      Nonempty (changed.Controlled controls frontier) := by
  obtain ⟨bodyFootprint, outside, packed, body, ⟨bodyReady⟩, pack, covered, outsideAvailable⟩ :=
    row.body.rebind_local_controlled ready.body
      (variableProfileView forward (Locals.push locals) (σ.cons key.anchor))
      (variableProfileView_available input available) row.pack row.covered row.outsideAvailable closed
  obtain ⟨domain, ⟨domainReady⟩⟩ := ready.domain.mapProfileView backward
  exact ⟨{
    domainSupport := backward.mapType row.domainSupport
    domainFootprint := _
    domain := domain
    domainAvailable := repeated_available row.domainAvailable _
    inputTyped := backward.mapType_typed row.inputTyped
    alignment := row.alignment.mapInput henv hscoped backward
    anchor := (AdapterSeed.view .same backward).admission henv hscoped formed row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable }, ⟨⟨domainReady, bodyReady⟩⟩⟩

theorem unpad
    {result : Profile (n + 1)}
    {row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (key : Key n).pad result}
    (ready : row.Controlled controls frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed) :
    ∃ changed : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result.down,
      Nonempty (changed.Controlled controls frontier) := by
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need member
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, body, ⟨bodyReady⟩, pack, covered, outsideAvailable⟩ :=
    (RichCert.down row.body).rebind_local_controlled ready.body.certDown
      (Obs.pad (.var (Locals.push locals) (σ.cons key.anchor) 0 key.input))
      resources row.pack row.covered row.outsideAvailable closed
  exact ⟨{
    domainSupport := row.domainSupport.down
    domainFootprint := row.domainFootprint
    domain := .down row.domain
    domainAvailable := row.domainAvailable
    inputTyped := row.inputTyped.pad_inv
    alignment := row.alignment.unpad henv
    anchor := Admitted.unpad henv formed row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable }, ⟨⟨ready.domain.certDown, bodyReady⟩⟩⟩

end RichPiRowCertificate.Controlled
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
