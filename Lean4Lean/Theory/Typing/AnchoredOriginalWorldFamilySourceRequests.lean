import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyConsumptionOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyRequest

/-! Source requests selected from the consumed family retain controls on
the SAME original argument observers, including terminal variable replay
and the finite descriptor adapter of the actual incoming family query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem RichFamilyArgumentSlot.transport_queries
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (same : expression = nextExpression)
    (slot : RichFamilyArgumentSlot root env registry target source locals σ available expression needs)
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (ready : property slot.argument.query.observation) :
    ∃ selected : RichFamilyArgumentSlot root env registry target source locals σ available nextExpression needs,
      property selected.argument.query.observation := by
  cases same
  exact ⟨slot, ready⟩

theorem RichFamilyArgumentSpine.lookup_queries
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior)
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (ready : spine.Queries property) (index : Nat) (bound : index < arguments.length) :
    ∃ slot : RichFamilyArgumentSlot root env registry target source locals σ available
      (arguments[arguments.length-1-index]'(by omega)) (prior index),
      property slot.argument.query.observation := by
  induction spine generalizing index with
  | nil => cases bound
  | @push arguments prior expression needs tail slot ih =>
    cases index with
    | zero =>
      have equal : (arguments ++ [expression])[(arguments ++ [expression]).length - 1 - 0]'(by
          simp only [List.length_append, List.length_singleton]; omega) = expression := by
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, Nat.sub_zero,
          List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact slot.transport_queries equal.symm property ready.2
    | succ index =>
      have small : index < arguments.length := by simp only [List.length_append, List.length_singleton] at bound; omega
      obtain ⟨selected, controlled⟩ := ih ready.1 index small
      have position : (arguments ++ [expression]).length - 1 - (index + 1) =
          arguments.length - 1 - index := by simp only [List.length_append, List.length_singleton]; omega
      have equal : (arguments ++ [expression])[(arguments ++ [expression]).length - 1 - (index + 1)]'(by omega) =
          arguments[arguments.length - 1 - index]'(by omega) := by
        simp only [position, List.getElem_append_left (by omega : arguments.length - 1 - index < arguments.length)]
      exact selected.transport_queries equal.symm property controlled

theorem RichFamilyArgumentSlot.replayVariable_controlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType} {input : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (slot : RichFamilyArgumentSlot root env registry target source locals σ available expression needs)
    (value : Obs env U registry target captureLocals seed (.bvar index) (rawInput : Profile n) footprint)
    (adapter : NormalProfileAdapter env U registry target rawInput input)
    (resources : ∀ i need, (i, need) ∈ footprint → need ∈ needs)
    (ready : ControlledStoredQuery controls frontier (.observation slot.argument.query.observation)) :
    Nonempty (ControlledStoredQuery controls frontier
      (.observation (slot.replayVariable henv hscoped formed value adapter resources).query.observation)) :=
  ready.raise (Nat.le_max_left _ _)


theorem FamilyCaptures.worldSourceRequests
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (captures : FamilyCaptures env U registry target headerSource captureLocals seed expressions requests footprint)
    (raw : Ctx.SubstEq env U target seed actual headerSource)
    (sourceLength : headerSource.length = arguments.length)
    (actualEq : ∀ i (bound : i < arguments.length), actual i =
      (arguments[arguments.length-1-i]'(by omega)).subst σ)
    (spine : RichFamilyArgumentSpine root env registry target source locals σ available arguments prior)
    (ready : spine.Queries (ControlledFamilyQuery controls frontier))
    (resources : footprint.Available prior) :
    List.Forall₂ (fun expression request => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available
        (expression.subst (nativeCaptureSubst arguments)) request)) expressions requests := by
  match captures with
  | .nil => exact .nil
  | .cons (index := index) (valueFootprint := valueFootprint) lookup value adapter alignment anchor tail =>
    have bound : index < arguments.length := by simpa only [sourceLength] using lookup.lt
    obtain ⟨slot, ⟨slotReady⟩⟩ := spine.lookup_queries _ ready index bound
    have resource : ∀ i need, (i, need) ∈ valueFootprint → need ∈ prior index := by
      intro i need member
      have same : i = index := value.variableTrace.indices member
      subst i
      exact resources index need (List.mem_append_left _ member)
    let query := slot.replayVariable henv hscoped formed value adapter resource
    obtain ⟨queryReady⟩ := slot.replayVariable_controlled henv hscoped formed value adapter resource slotReady
    refine .cons ?_ (FamilyCaptures.worldSourceRequests henv hscoped formed tail raw sourceLength actualEq spine ready (by
      intro i need member; exact resources i need (List.mem_append_right _ member)))
    have pair := alignment.path.symm.cast (raw.lookup lookup)
    have path := anchor.1.trans (by simpa only [actualEq index bound] using pair)
    simpa only [subst_bvar, nativeCaptureSubst, dif_pos bound] using
      (show Nonempty (WorldRichFamilySourceRequest controls frontier root registry target locals σ available
        (arguments[arguments.length-1-index]'(by omega)) _) from ⟨⟨query, queryReady, path⟩⟩)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem RichFamilyConsumedCaptures.worldObservations
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {consumed : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n + 1) (.family demand)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (packet : RichFamilyConsumedCaptures consumed)
    (ready : consumed.observed.Queries (ControlledFamilyQuery controls frontier)) :
    List.Forall₂ (fun expression request => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression request))
      arguments packet.requests := by
  have sourceLength : consumed.headerSource.length = arguments.length := by
    rw [consumed.sourceEq, consumed.saturated henv hscoped formed, List.take_length, List.length_reverse]
  have selected := FamilyCaptures.worldSourceRequests henv hscoped formed packet.captures consumed.raw
    sourceLength consumed.actualEq consumed.observed ready packet.resources
  have converted : List.Forall₂ (fun expression request => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression request))
      ((constantCaptureVariables consumed.anchors.length).map (·.subst (nativeCaptureSubst arguments)))
      packet.requests := List.forall₂_map_left_iff.mpr selected
  rw [consumed.length] at converted
  have exactArguments :
      (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) = arguments := by
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
  rwa [exactArguments] at converted

noncomputable def WorldRichFamilySourceRequest.pad
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (request : WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression input) :
    WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression
      (input.map id Profile.pad) where
  argument := { request.argument with query := request.argument.query.pad henv hscoped formed }
  controlled := Classical.choice (request.controlled.raise (Nat.le_max_left _ _))
  anchor := request.anchor

def WorldFamilyRequestProperty
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (family : FamilyData (Profile n)) : Prop :=
  family.name = name ∧ List.Forall₂ (· ≈ ·) family.levels levels ∧
    List.Forall₂ (fun expression request => Nonempty
      (WorldRichFamilySourceRequest controls frontier root registry target locals σ available expression request))
      arguments family.arguments

theorem WorldFamilyRequestProperty.pad
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (property : WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments family) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments family.pad := by
  refine ⟨property.1, property.2.1, ?_⟩
  exact List.forall₂_map_right_iff.mpr (Lean4Lean.List.Forall₂.imp
    (fun _ _ request => request.elim (fun selected => ⟨selected.pad henv hscoped formed⟩)) property.2.2)

/-- Exact source requests for the ACTUAL incoming family descriptor, after
all finite grade/code adapters. Every request retains its query controls. -/
theorem RichFamilyPlanConsumption.familyWorldRequests
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (consumed : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n+1) (.family demand))
    (ready : consumed.observed.Queries (ControlledFamilyQuery controls frontier)) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments demand := by
  obtain ⟨packet⟩ := consumed.familySourceCaptures henv hscoped formed
  have property : WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments ⟨name, levels, packet.relevant, packet.requests⟩ :=
    ⟨rfl, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl),
      packet.worldObservations henv hscoped formed ready⟩
  have raised := (FamilyAtomProperty.raise_iff
    (property := WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments)
    packet.bound (.family ⟨name, levels, packet.relevant, packet.requests⟩)).mpr property
  have result := GeneralNormalAtomAdapter.familyProperty packet.adapter
    (property := WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments)
    (fun source => source.pad henv hscoped formed) raised
  exact (FamilyAtomProperty.raise_iff consumed.bound (.family demand)).mp result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
