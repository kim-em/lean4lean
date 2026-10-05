import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionVariableCapture
import Lean4Lean.Theory.Typing.AnchoredConstructorPlanFront

/-! Pull an actual source application through the exposed declaration-plan
binder. The typed projected argument keeps its inferred source type; the
binder's original key, anchor and support are recovered by its finite key
program. No declared-domain source typing or semantic supplier is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor
open private normal_fn_parts unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
set_option backward.isDefEq.respectTransparency false

structure ProjectedBinderInput
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (oldKey : Key N) (support : Profile N) (oldOutput : Atom N)
    (output : Atom n) (bound : n ≤ N) where
  argument : ProjectionGradedResult env registry target node locals σ available oldKey.input
  admission : RankedData.RequestAdmission env U (relations env U registry N) target
    (⟨oldKey, support⟩ : DataRequest (Profile N))
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)
  outputAdapter : NormalAtomAdapter env U registry target oldOutput (raiseAtom N bound output)

/-- This is the missing key-alignment producer: the complete normalized
function adapter is consumed, including contravariant input, reanchor and
domain-rekey steps. The frozen binder support comes from its actual guard. -/
theorem ProjectionObs.pullBinder
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {oldKey : Key N} {support : Profile N} {oldOutput : Atom N}
    {key : Key n} {output : Atom n} (bound : n ≤ N)
    (guard : LambdaGuard env U registry target seed domain oldKey support)
    (functionAdapter : NormalAtomAdapter env U registry target (n := N + 1)
      (.fn oldKey oldOutput) (raiseAtom (N + 1) (Nat.succ_le_succ bound) (.fn key output)))
    (query : ProjectionObs env registry target node locals σ input footprint)
    (resources : footprint.Available available)
    (arguments : NormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)) :
    Nonempty (ProjectedBinderInput env registry target node locals σ available
      oldKey support oldOutput output bound) := by
  have exposed := functionAdapter.comp
    ((functionGradeView (env := env) (U := U) (registry := registry) (Γ := target)
      bound key output).toAdapter henv hscoped formed)
  obtain ⟨⟨keys⟩, ⟨outputs⟩⟩ := normal_fn_parts exposed
  have incoming := AdapterNormal.normalizeAdmission henv hscoped formed (Admitted.raise henv bound admitted)
  have seed := AdapterNormal.normalizeAdmission henv hscoped formed guard.anchor
  have pulled := unnormalize_admission henv hscoped formed (keys.pull henv hscoped formed seed incoming)
  have inputs : NormalProfileAdapter env U registry target (raiseProfile N bound input) oldKey.input :=
    (arguments.raise henv hscoped formed bound).comp keys.arguments
  obtain ⟨anchor, pair, _, _, _, _, first, last⟩ := pulled
  have code := guard.domains.left_diagonal
  exact ⟨{
    argument := {
      rank := N, bound := Nat.le_refl _, raw := raiseProfile N bound input
      footprint := footprint, query := .raise query bound
      adapter := by simpa only [raiseProfile_self] using inputs
      resources := resources }
    admission := ⟨anchor, pair, guard.inputTyped, guard.formed, code,
      Related.retag henv guard.inputTyped code first, Related.retag henv guard.inputTyped code last⟩
    outputAdapter := outputs }⟩

/-- The declaration binder's actual pack generates its local typed supply
at the exact old key, including dependencies introduced by the body code. -/
theorem ProjectedBinderInput.localSupply
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    {oldKey : Key N} {support : Profile N} {oldOutput : Atom N} {output : Atom n} {bound : n ≤ N}
    {packed : Profile N}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (input : ProjectedBinderInput env registry target node locals σ available
      oldKey support oldOutput output bound)
    (pack : BinderPack N packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldKey.input.atoms)
    (slot : Nat) :
    Nonempty (ProjectionVariableSupply env registry target node locals σ available slot
      ((bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons).map (slot, ·))) :=
  input.argument.supply henv hscoped formed _ slot
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))

private theorem variableFootprint
    (observation : Obs env U registry target locals σ (.bvar slot) demand footprint) :
    ∀ entry ∈ footprint, entry.1 = slot := by
  match observation with
  | .var .. => intro entry member; cases List.mem_singleton.mp member; rfl
  | .empty => intro _ member; cases member
  | .union first second =>
    intro entry member
    exact (List.mem_append.mp member).elim (variableFootprint first entry) (variableFootprint second entry)
  | .view child _ | .pad child | .unpad child | .rowShift child => exact variableFootprint child
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

/-- The actual binder pack and terminal variable observer produce the
terminal request's typed projection query, including all capture adapters.
The only resource premise is literal membership in the binder's finite list. -/
theorem ProjectedBinderInput.reifyTerminal
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    {oldKey : Key N} {support : Profile N} {oldOutput : Atom N} {output : Atom n} {bound : n ≤ N}
    {packed : Profile N}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (input : ProjectedBinderInput env registry target node locals σ available
      oldKey support oldOutput output bound)
    (pack : BinderPack N packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldKey.input.atoms)
    (slot : Nat)
    (value : Obs env U registry target captureLocals captures (.bvar slot) raw footprint)
    (resources : ∀ need, (slot, need) ∈ footprint →
      need ∈ bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (adapter : NormalProfileAdapter env U registry target raw requested) :
    Nonempty (ProjectionGradedResult env registry target node locals σ available requested) := by
  obtain ⟨whole⟩ := input.localSupply henv hscoped formed pack covered slot
  obtain ⟨supply⟩ := whole.restrict (after := footprint) (by
    intro entry member
    obtain ⟨index, need⟩ := entry
    have equal := variableFootprint value (index, need) member
    change index = slot at equal
    subst index
    exact List.mem_map.mpr ⟨need, resources need member, rfl⟩) (variableFootprint value)
  obtain ⟨reified⟩ := reifyProjectedVariable henv hscoped formed value supply
  exact ⟨{ reified with adapter := reified.adapter.comp (adapter.raise henv hscoped formed reified.bound) }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
