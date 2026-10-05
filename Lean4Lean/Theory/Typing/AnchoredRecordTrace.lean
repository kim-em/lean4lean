import Lean4Lean.Theory.Typing.AnchoredDataTrace
import Lean4Lean.Theory.Typing.AnchoredRecordBeta
import Lean4Lean.Theory.Typing.AnchoredDataValueLaws
import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredSupport
import Batteries.Tactic.OpenPrivate

/-! Replay record observations at their frozen field supports. Both queries
retain the same descriptor support, and only literal lifts cross absorption. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false
private theorem normalizeRoute (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (formed : OnCtx Γ (env.IsType U)) :
    ∃ Ω, ProofInsertion env U Γ Ω ρ ∧ ContextChain env U Ω Δ := by
  induction route with
  | proof insertion => exact ⟨_, insertion, .refl⟩
  | context chain => exact ⟨_, .refl formed, chain⟩
  | comp before after first second =>
    obtain ⟨Ω, initial, changed⟩ := first formed
    obtain ⟨V, suffix, final⟩ := second (before.targetWF henv formed)
    obtain ⟨W, suffix', changed'⟩ := changed.pullProof henv suffix
    exact ⟨W, initial.comp suffix' henv, changed'.trans final⟩

private theorem MixedInsertion.eqBack (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (h : env.IsDefEq U Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)) :
    env.IsDefEq U Γ left right type := by
  induction route generalizing left right type with
  | proof insertion =>
    obtain ⟨embedding, map⟩ := insertion.toEmbedding henv
    have result := h.subst henv embedding.typed (hΓ₀ := embedding.baseWF)
    simpa only [← map, embedding.leftInv] using result
  | context chain =>
    apply (chain.symm henv).eq henv
    simpa only [lift'_refl] using h
  | comp _ _ first second =>
    apply first
    apply second
    simpa only [lift'_comp] using h

namespace RankedData

theorem Arguments.getEntry {α : Type} {entries : List α}
    {entry : α} {keys : α → DataRequest (Profile n)} {left right : α → VExpr}
    (arguments : Arguments env U lower Γ (entries.map keys) (entries.map left) (entries.map right))
    (member : entry ∈ entries) : RequestAdmission env U lower Γ (keys entry) (left entry) (right entry) := by
  induction entries with
  | nil => cases member
  | cons next rest ih =>
    cases arguments with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih tail member

private theorem RecordWitness.normalized (henv : env.Ordered)
    (W : RecordWitness env U registry (relations env U registry n) Γ left right type demand) :
    ∃ W' : RecordWitness env U registry (relations env U registry n) Γ left right type demand,
      ProofInsertion env U Γ W'.context W'.map := by
  obtain ⟨Ω, inserted, changed⟩ := normalizeRoute henv W.insertion W.baseWF
  have laws : LowerTransport env U (relations env U registry n) :=
    ⟨fun route h => route.code henv h, fun route h => route.term henv h⟩
  obtain ⟨W', contexts, maps⟩ := W.transportDisplay henv laws (.context (changed.symm henv))
  refine ⟨W', ?_⟩
  simpa only [contexts, maps, Lift.comp] using inserted

private theorem frontMap (ρ : Lift) (front : List VExpr) :
    (Lift.skipN .refl front.length).comp (ρ.consN front.length) =
      ρ.comp (.skipN .refl (renameAdded ρ front).length) := by
  simp only [renameAdded_length, Lift.skipN_comp_consN, Lift.refl_comp,
    Lift.comp_skipN, Lift.comp]

private theorem RecordRelation.prependWitness
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : ∀ (Γ front : List VExpr) (le re l r type : VExpr) (value support : Profile n),
      TraceEndpoint registry front le l → TraceEndpoint registry front re r →
      ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length) →
      env.IsDefEq U (front ++ Γ) (le.lift' (.skipN .refl front.length)) l
        (type.lift' (.skipN .refl front.length)) →
      env.IsDefEq U (front ++ Γ) (re.lift' (.skipN .refl front.length)) r
        (type.lift' (.skipN .refl front.length)) →
      Related env U registry (front ++ Γ) l r (type.lift' (.skipN .refl front.length))
        (value.rename (.skipN .refl front.length)) (support.rename (.skipN .refl front.length)) →
      Related env U registry Γ le re type value support)
    {Γ front : List VExpr} {left right leftResult rightResult type : VExpr}
    {demand : RecordData (Profile n)}
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (H : RecordRelation env U registry (relations env U registry n) (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length)) (demand.rename (.skipN .refl front.length))) :
    Nonempty (RecordWitness env U registry (relations env U registry n) Γ left right type demand) := by
  have renameRefl (d : RecordData (Profile n)) : d.rename .refl = d := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, RecordData.map_id]
  have atBase := H _ .refl (.refl (generated.targetWF henv))
  simp only [lift'_refl, renameRefl] at atBase
  obtain ⟨initial⟩ := atBase
  obtain ⟨W, post⟩ := initial.normalized henv
  let ν := (Lift.skipN .refl front.length).comp W.map
  let copied := renameAdded ν front
  let skip : Lift := .skipN .refl copied.length
  have total : ProofInsertion env U Γ W.context ν := generated.comp post henv
  obtain ⟨copyGenerated, extended⟩ := generated.renameFront front total.toFuture henv
  have copyGenerated' : ProofInsertion env U W.context (copied ++ W.context) skip := by
    simpa only [copied, skip, renameAdded_length] using copyGenerated
  obtain ⟨S⟩ := H _ _ extended
  have leftOld := W.insertion.eq henv leftEq
  have rightOld := W.insertion.eq henv rightEq
  have leftNew := leftEq.weak' henv extended.weakening
  have rightNew := rightEq.weak' henv extended.weakening
  have oldFields : Arguments env U (relations env U registry n) W.context
      (demand.fields.map (fun entry => DataRequest.rename ν entry.2))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 (leftResult.lift' W.map)))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 (rightResult.lift' W.map))) := by
    simpa only [RecordData.rename, RecordData.map, FamilyData.map, List.map_map, Function.comp_def,
      DataRequest.rename, DataRequest.map, KeyData.map, ← Profile.rename_comp, ← lift'_comp, ν] using W.fields
  have newFields : Arguments env U (relations env U registry n) S.context
      (demand.fields.map (fun entry => DataRequest.rename (ν.comp (skip.comp S.map)) entry.2))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1
        ((leftResult.lift' (ν.consN front.length)).lift' S.map)))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1
        ((rightResult.lift' (ν.consN front.length)).lift' S.map))) := by
    simpa only [RecordData.rename, RecordData.map, FamilyData.map, List.map_map, Function.comp_def,
      DataRequest.rename, DataRequest.map, KeyData.map, ← Profile.rename_comp, ← lift'_comp, frontMap, copied, skip,
      Lift.comp_assoc] using S.fields
  refine ⟨{
    baseWF := generated.baseWF
    context := W.context, map := ν, insertion := .proof total
    info := W.info, lookup := W.lookup
    ctorDefinition := W.ctorDefinition, ctorNative := W.ctorNative, ctorQuotient := W.ctorQuotient
    bounded := ?_, typeCode := ?_
    leftType := ?_, rightType := ?_
    leftOrigins := ?_, rightOrigins := ?_
    fields := ?_ }⟩
  · intro entry member
    exact W.bounded (entry.1, DataRequest.rename (.skipN .refl front.length) entry.2)
      (List.mem_map.mpr ⟨entry, member, rfl⟩)
  · have h := W.typeCode
    change FamilyRelation env U registry (relations env U registry n) W.context
      ((type.lift' (.skipN .refl front.length)).lift' W.map)
      ((type.lift' (.skipN .refl front.length)).lift' W.map)
      ((demand.family.rename (.skipN .refl front.length)).rename W.map) at h
    simpa only [ν, ← lift'_comp, FamilyData.rename_comp] using h
  · simpa only [ν, ← lift'_comp] using leftOld.hasType.1
  · simpa only [ν, ← lift'_comp] using rightOld.hasType.1
  · intro entry member
    obtain ⟨origin⟩ := W.leftOrigins _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, ν, ← lift'_comp] using
      origin.replaceMajor leftOld.symm⟩
  · intro entry member
    obtain ⟨origin⟩ := W.rightOrigins _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, ν, ← lift'_comp] using
      origin.replaceMajor rightOld.symm⟩
  · apply Arguments.mapEntries (arguments := oldFields)
    intro entry member admitted
    obtain ⟨lo⟩ := W.leftOrigins _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
    obtain ⟨ro⟩ := W.rightOrigins _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
    have leq : env.IsDefEq U W.context (.proj demand.family.name entry.1 (left.lift' ν))
        (.proj demand.family.name entry.1 (leftResult.lift' W.map)) (entry.2.domain.lift' ν) := by
      simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, ν, ← lift'_comp]
        using (lo.congr leftOld.symm).symm
    have req : env.IsDefEq U W.context (.proj demand.family.name entry.1 (right.lift' ν))
        (.proj demand.family.name entry.1 (rightResult.lift' W.map)) (entry.2.domain.lift' ν) := by
      simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, ν, ← lift'_comp]
        using (ro.congr rightOld.symm).symm
    obtain ⟨anchorEq, pairEq, typed, proper, code, _, _⟩ := admitted
    let support := entry.2.support.rename ν
    change TypeRelated env U registry W.context (entry.2.domain.lift' ν)
      (entry.2.domain.lift' ν) support at code
    refine ⟨anchorEq.trans leq.symm, (leq.trans pairEq).trans req.symm,
      typed, proper, code, ?_, ?_⟩
    all_goals
      have incoming := newFields.getEntry member
      obtain ⟨_, _, _, _, _, anchorTerm, pairTerm⟩ := incoming
      change Related env U registry S.context _ _ _ _ _ at anchorTerm pairTerm
      have anchorBase : Related env U registry (copied ++ W.context)
          ((entry.2.anchor.lift' ν).lift' skip)
          (.proj demand.family.name entry.1 (leftResult.lift' (ν.consN front.length)))
          ((entry.2.domain.lift' ν).lift' skip)
          ((entry.2.input.rename ν).rename skip) (support.rename skip) := by
        apply S.insertion.termBack henv
        simpa only [lift', lift'_comp, Profile.rename_comp, DataRequest.rename, DataRequest.map, KeyData.map, support] using anchorTerm
      have pairBase : Related env U registry (copied ++ W.context)
          (.proj demand.family.name entry.1 (leftResult.lift' (ν.consN front.length)))
          (.proj demand.family.name entry.1 (rightResult.lift' (ν.consN front.length)))
          ((entry.2.domain.lift' ν).lift' skip)
          ((entry.2.input.rename ν).rename skip) (support.rename skip) := by
        apply S.insertion.termBack henv
        simpa only [lift', lift'_comp, Profile.rename_comp, DataRequest.rename, DataRequest.map, KeyData.map, support] using pairTerm
      obtain ⟨ls⟩ := S.leftOrigins _ (List.mem_map.mpr
        ⟨_, List.mem_map.mpr ⟨entry, member, rfl⟩, rfl⟩)
      obtain ⟨rs⟩ := S.rightOrigins _ (List.mem_map.mpr
        ⟨_, List.mem_map.mpr ⟨entry, member, rfl⟩, rfl⟩)
      have lraw := (ls.congr (S.insertion.eq henv leftNew).symm).symm
      have rraw := (rs.congr (S.insertion.eq henv rightNew).symm).symm
      have lraw' : env.IsDefEq U (copied ++ W.context)
          ((VExpr.proj demand.family.name entry.1 (left.lift' ν)).lift' skip)
          (.proj demand.family.name entry.1 (leftResult.lift' (ν.consN front.length)))
          ((entry.2.domain.lift' ν).lift' skip) := by
        apply S.insertion.eqBack henv
        simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, lift', ← lift'_comp,
          frontMap, copied, skip, Lift.comp_assoc] using lraw
      have rraw' : env.IsDefEq U (copied ++ W.context)
          ((VExpr.proj demand.family.name entry.1 (right.lift' ν)).lift' skip)
          (.proj demand.family.name entry.1 (rightResult.lift' (ν.consN front.length)))
          ((entry.2.domain.lift' ν).lift' skip) := by
        apply S.insertion.eqBack henv
        simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.map, KeyData.map, lift', ← lift'_comp,
          frontMap, copied, skip, Lift.comp_assoc] using rraw
      have lt := (leftTrace.rename hscoped ν).proj W.lookup W.ctorDefinition W.ctorNative W.ctorQuotient
        (index := entry.1)
      have rt := (rightTrace.rename hscoped ν).proj W.lookup W.ctorDefinition W.ctorNative W.ctorQuotient
        (index := entry.1)
    · exact lower W.context copied _ _ _ _ _ _ _ .lifted lt copyGenerated'
        (anchorEq.hasType.1.weak' henv copyGenerated'.weakening) lraw' anchorBase
    · exact lower W.context copied _ _ _ _ _ _ _ lt rt copyGenerated' lraw' rraw' pairBase

theorem RecordRelation.prependEndpoints
    {n : Nat} {Γ front : List VExpr}
    {left right leftResult rightResult type : VExpr} {demand : RecordData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : ∀ (Γ front : List VExpr) (le re l r type : VExpr) (value support : Profile n),
      TraceEndpoint registry front le l → TraceEndpoint registry front re r →
      ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length) →
      env.IsDefEq U (front ++ Γ) (le.lift' (.skipN .refl front.length)) l
        (type.lift' (.skipN .refl front.length)) →
      env.IsDefEq U (front ++ Γ) (re.lift' (.skipN .refl front.length)) r
        (type.lift' (.skipN .refl front.length)) →
      Related env U registry (front ++ Γ) l r (type.lift' (.skipN .refl front.length))
        (value.rename (.skipN .refl front.length)) (support.rename (.skipN .refl front.length)) →
      Related env U registry Γ le re type value support)
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (H : RecordRelation env U registry (relations env U registry n) (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length)) (demand.rename (.skipN .refl front.length))) :
    RecordRelation env U registry (relations env U registry n) Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
  have W := H.future henv extended
  have W' : RecordRelation env U registry (relations env U registry n) (renameAdded ρ front ++ Δ)
      (leftResult.lift' (ρ.consN front.length)) (rightResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      ((demand.rename ρ).rename (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, RecordData.rename_comp, frontMap] using W
  have leftEq' : env.IsDefEq U (renameAdded ρ front ++ Δ)
      ((left.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      (leftResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, frontMap] using leftEq.weak' henv extended.weakening
  have rightEq' : env.IsDefEq U (renameAdded ρ front ++ Δ)
      ((right.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      (rightResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, frontMap] using rightEq.weak' henv extended.weakening
  exact W'.prependWitness henv hscoped lower (leftTrace.rename hscoped ρ) (rightTrace.rename hscoped ρ)
    (by simpa only [renameAdded_length] using newGenerated) leftEq' rightEq'

end RankedData
end Lean4Lean.AnchoredSemantics
