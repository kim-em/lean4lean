import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureInterpretation
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction

/-! Terminal family captures use the actual rich frame lookup. Their finite
legacy variable wrappers require no original-domain callback: nonempty value
semantics supplies its assigned support code, while empty demands use empty
support. Frozen request domains remain connected by their retained chains. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private structure VariableSemantic (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (left right type : VExpr) (profile : Profile n) where
  support : Profile n
  typed : profile.HasType support
  code : TypeRelated env U registry target type type support
  related : Related env U registry target left right type profile support

private def VariableSemantic.empty : VariableSemantic env U registry target left right type (.empty : Profile n) where
  support := .empty
  typed := Profile.HasType.empty Profile.WF.empty
  code := TypeRelated.of_singletons (fun _ h => nomatch h)
  related := Related.of_singletons (fun _ h => nomatch h)

private theorem variableSemantic
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (lookup : Lookup headerSource index A)
    (query : Obs env U registry target locals σ (.bvar index) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (VariableSemantic env U registry target (σ index) (τ index) (A.subst σ) profile) := by
  match query with
  | .var _ _ _ demand =>
    by_cases empty : demand = .empty
    · subst demand; exact ⟨.empty⟩
    · obtain ⟨entry⟩ := frame.lookup henv formed (resources _ _ List.mem_cons_self) lookup
      have nonempty : demand.Nonempty := empty
      exact ⟨⟨entry.support, entry.typed, entry.related.typeCode henv hscoped formed nonempty, entry.related⟩⟩
  | .empty => exact ⟨.empty⟩
  | .union first second =>
    obtain ⟨left⟩ := variableSemantic henv hscoped formed frame lookup first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨right⟩ := variableSemantic henv hscoped formed frame lookup second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    let support := left.support.union right.support
    have wf := left.typed.wf_type.union right.typed.wf_type
    have lt := left.typed.enlarge (Profile.le_union_left _ _) wf
    have rt := right.typed.enlarge (Profile.le_union_right _ _) wf
    have code : TypeRelated env U registry target (A.subst σ) (A.subst σ) support :=
      TypeRelated.of_singletons (fun atom hm => (List.mem_append.mp hm).elim
        (fun h => left.code.singleton h) (fun h => right.code.singleton h))
    exact ⟨⟨support, lt.union rt, code,
      (left.related.retag henv lt code).union (right.related.retag henv rt code)⟩⟩
  | .view child change =>
    obtain ⟨before⟩ := variableSemantic henv hscoped formed frame lookup child resources
    exact ⟨⟨change.mapType before.support, change.mapType_typed before.typed,
      change.codeMap henv hscoped before.code, change.termMap henv hscoped formed before.related⟩⟩
  | .pad child =>
    obtain ⟨before⟩ := variableSemantic henv hscoped formed frame lookup child resources
    exact ⟨⟨before.support.pad, before.typed.pad, before.code.pad henv, before.related.pad henv⟩⟩
  | .unpad child =>
    obtain ⟨before⟩ := variableSemantic henv hscoped formed frame lookup child resources
    exact ⟨⟨before.support.down, before.typed.pad_inv, before.code.down henv, before.related.unpad henv formed⟩⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨before⟩ := variableSemantic henv hscoped formed frame lookup child resources
    let change := AtomView.commutePadFn (env := env) (U := U) (registry := registry) (Γ := target) key output
    refine ⟨⟨change.mapType before.support.pad, ?_, change.codeMap henv hscoped (before.code.pad henv), ?_⟩⟩
    · exact change.mapType_typed before.typed.pad
    · exact change.termMap henv hscoped formed (before.related.pad henv)
termination_by sizeOf query

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

namespace Lean4Lean.AnchoredSource.Adapted.FamilyCaptures
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalRecordSource
set_option backward.isDefEq.respectTransparency false

/-- All terminal requests are reconstructed with their original frozen
support, anchor, and domain. Only actual rich-frame lookup is used. -/
theorem interpretRichFrame {n : Nat} {keys : List (DataRequest (Profile n))}
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (captures : FamilyCaptures env U registry target headerSource locals σ expressions keys footprint)
    (resources : footprint.Available available) :
    RankedData.Arguments env U (relations env U registry n) target (keys : List (DataRequest (Profile n)))
      (expressions.map (·.subst σ)) (expressions.map (·.subst τ)) := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨observed⟩ := variableSemantic henv hscoped formed frame lookup value
      (fun i need member => resources i need (List.mem_append_left _ member))
    have aligned := alignment.admission henv anchor.toAdmission
    obtain ⟨_, _, actualSupport, actualTyped, _, actualCode, _, _⟩ := aligned
    have interpreted := adapter.termMap henv hscoped formed actualTyped actualCode observed.related
    obtain ⟨rawAnchor, _, typed, formedSupport, code, anchorRelated, _⟩ := anchor
    have pair := alignment.symm henv |>.related henv typed code interpreted
    refine .cons ?_ (interpretRichFrame henv hscoped formed frame substitutions tail
      (fun i need member => resources i need (List.mem_append_right _ member)))
    exact ⟨rawAnchor, alignment.path.symm.cast (substitutions.lookup lookup),
      typed, formedSupport, code, anchorRelated, pair⟩
termination_by sizeOf captures

end Lean4Lean.AnchoredSource.Adapted.FamilyCaptures
