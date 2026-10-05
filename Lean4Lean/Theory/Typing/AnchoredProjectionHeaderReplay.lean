import Lean4Lean.Theory.Typing.AnchoredConstantHeaders
import Lean4Lean.Theory.Typing.AnchoredStageBudgets
import Lean4Lean.Theory.Typing.AnchoredProjectionRowsInterpretation
import Lean4Lean.Theory.Typing.AnchoredProjectionRowsReification
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! A projection replays frozen declaration rows only after the constructor
has been installed in its own original source environment. The existing
constant-header bank supplies the completed earlier theorem, at its own finite
control budget. Bare family transfer need not interpret these later rows.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- A completed stage is used at one finite budget for each actual observer.
The finite context entries and that observer determine the budget; forgetting
the returned bounds retains exactly the witnesses of the staged theorem. -/
theorem Staged.Joint.gradedOfAllFuel
    {control : Name → Bool} {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {source : List VExpr}
    {left right sourceType : VExpr}
    (original : ∀ fuel, Staged.Joint control fuel env U registry source left right sourceType) :
    GradedJoint env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have finite : Budgeted.PairedFits [] env U registry source target locals σ τ available := by
    constructor <;> constructor
    · intro index need member type lookup
      obtain ⟨entry⟩ := fits.forward.entry index need member type lookup
      exact ⟨entry, by intro _ _ member; cases member⟩
    · intro index need member type lookup
      obtain ⟨entry⟩ := fits.backward.entry index need member type lookup
      exact ⟨entry, by intro _ _ member; cases member⟩
  obtain ⟨fitFuel, finite⟩ := finite.finiteControl control
  have fitted (fuel : Nat) (bound : fitFuel ≤ fuel) :
      Staged.PairedFits control fuel env U registry source target locals σ τ available := by
    constructor <;> constructor
    · intro index need member type lookup
      obtain ⟨entry, bounded⟩ := finite.forward.entry index need member type lookup
      exact ⟨entry, Nat.le_trans (bounded control fitFuel (List.mem_singleton_self _)) bound⟩
    · intro index need member type lookup
      obtain ⟨entry, bounded⟩ := finite.backward.entry index need member type lookup
      exact ⟨entry, Nat.le_trans (bounded control fitFuel (List.mem_singleton_self _)) bound⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n demand footprint observation resources
    have joint := original (max fitFuel (observation.nativeDepth control))
      target locals σ τ available closed hTarget substitutions (fitted _ (Nat.le_max_left _ _))
    obtain ⟨result⟩ := joint.1 observation (Nat.le_max_right _ _) resources
    exact ⟨result.toGradedTransferResult⟩
  · intro n demand footprint observation resources
    have joint := original (max fitFuel (observation.nativeDepth control))
      target locals σ τ available closed hTarget substitutions (fitted _ (Nat.le_max_left _ _))
    obtain ⟨result⟩ := joint.2.1 observation (Nat.le_max_right _ _) resources
    exact ⟨result.toGradedTransferResult⟩
  · intro level relevant typeEq relevance n demand footprint observation resources
    have joint := original (max fitFuel (observation.nativeDepth control))
      target locals σ τ available closed hTarget substitutions (fitted _ (Nat.le_max_left _ _))
    exact joint.2.2.1 level relevant typeEq relevance observation (Nat.le_max_right _ _) resources
  · intro level relevant typeEq relevance n demand footprint observation resources
    have joint := original (max fitFuel (observation.nativeDepth control))
      target locals σ τ available closed hTarget substitutions (fitted _ (Nat.le_max_left _ _))
    exact joint.2.2.2 level relevant typeEq relevance observation (Nat.le_max_right _ _) resources

private theorem sourceFormationAtPrevious
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (earlier : ∀ {Γ l r A}, source.IsDefEqStrong U Γ l r A →
      GradedJoint env U registry Γ l r A)
    {Γ : List VExpr} {expression : VExpr}
    (formation : SourcePiFormation (fun Γ e A => source.IsDefEqStrong U Γ e e A) Γ expression) :
    SourcePiFormation (OriginalTypePayload source env U registry) Γ expression := by
  induction expression generalizing Γ with
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, domain⟩, ⟨v, codomain⟩, domainTree, bodyTree⟩ := formation
    exact .pi ⟨domain, earlier domain⟩ ⟨codomain, earlier codomain⟩
      (ihA domainTree) (ihB bodyTree)
  | _ => trivial

/-- Actual projection registration selects the constructor's earlier header,
not the (possibly much earlier) family header. All literal domain children are
interpreted by that completed stage. The strict count witnesses the valid
declaration-induction edge even inside one inductive block. -/
theorem Staged.OriginalConstantHeaders.projectionFormation
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (hsource : source.Ordered)
    (headers : Staged.OriginalConstantHeaders source env U registry)
    {name : Name} {info : VProjectionInfo} (registered : source.projections name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U) :
    ∃ origin : ConstantHeaderOrigin source info.ctorName ⟨info.uvars, info.ctorType⟩,
      origin.ordered.constantCount < hsource.constantCount ∧
      SourcePiFormation (OriginalTypePayload origin.source env U registry) []
        (info.ctorType.instL levels) := by
  obtain ⟨origin, control, earlier⟩ :=
    headers info.ctorName _ (hsource.projectionConstructor registered)
  obtain ⟨level, original⟩ := origin.typeInstance levelsWF
  exact ⟨origin, origin.count_lt hsource,
    sourceFormationAtPrevious (fun proof => Staged.Joint.gradedOfAllFuel
      (fun fuel => earlier fuel proof)) original.sourcePiFormation.1⟩

/-- Transport an exact field-domain slice from its frozen anchor tuple to
the actual prefix using only the current source's original header bank. -/
theorem ProjectionRowSlice.transferAtHeader
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : source.Ordered)
    (below : source ≤ env)
    (headers : Staged.OriginalConstantHeaders source env U registry)
    {name : Name} {info : VProjectionInfo} (registered : source.projections name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {domains : List VExpr} {keys : List FamilyKey} {required : Footprint} {position : Nat}
    (rows : ProjectionRows env U registry target required [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels) domains keys)
    (slice : ProjectionRowSlice env U registry target [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels) domains keys position)
    {xs ys : List VExpr}
    (arguments : FamilyArguments env U registry target (keys.take position) xs ys) :
    Nonempty (CodeTransferResult env U registry target slice.rows.terminalLocals
      (nativeCaptureSubst xs) (nativeCaptureSubst ys) slice.rows.terminalValuation
      slice.domain slice.domain slice.support) := by
  obtain ⟨origin, _, formation⟩ := headers.projectionFormation hsource registered levelsWF
  have initial : FamilyPrefixAlignment env U registry [] target []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) :=
    ⟨.nil, .nil, .nil, .nil⟩
  simpa only [familySubst_native, List.nil_append] using
    slice.transfer henv hscoped (origin.sourceBelow.trans below) rows formation
      (by intro _ _ member; cases member) hTarget initial arguments

/-- Replay and reify a selected literal domain in one step. The only source
resources are the exact finite prefix observers retained by the row plan. -/
theorem ProjectionRowSlice.reifyTemplateAtHeader
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : source.Ordered)
    (below : source ≤ env)
    (headers : Staged.OriginalConstantHeaders source env U registry)
    {name : Name} {info : VProjectionInfo} (registered : source.projections name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (closed : callerAvailable.AtomClosed)
    {domains : List VExpr} {keys : List FamilyKey} {required : Footprint} {position : Nat}
    (rows : ProjectionRows env U registry target required [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels) domains keys)
    (slice : ProjectionRowSlice env U registry target [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels) domains keys position)
    (N : Nat) (bounded : ∀ key ∈ keys.take position, key.rank ≤ N)
    {xs values : List VExpr}
    (arguments : FamilyArguments env U registry target (keys.take position)
      xs (values.map (·.subst σ)))
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      values (FamilyKey.uniform N (keys.take position) bounded))
    (scope : slice.domain.ClosedN values.length) :
    Nonempty (CertificateResult env U registry target callerLocals σ callerAvailable
      (slice.domain.instOuter values) slice.support) := by
  obtain ⟨replayed⟩ := slice.transferAtHeader henv hscoped hsource below headers
    registered levelsWF hTarget rows arguments
  exact slice.rows.reifyTemplate henv hscoped hTarget closed N bounded observations
    replayed.certificate scope replayed.available

/-- The complete registered-field consumer. Constructor-header provenance,
finite local fuel, frozen-seed transport, declaration scope, and substitution
back to the original projection field type are all discharged internally.
There is no caller-supplied semantic theorem for a field domain. -/
theorem ProjectionRowSlice.reifyProjectionTypeAtHeader
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : source.Ordered)
    (below : source ≤ env)
    (headers : Staged.OriginalConstantHeaders source env U registry)
    {name : Name} {info : VProjectionInfo} (registered : source.projections name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (closed : callerAvailable.AtomClosed)
    {domains : List VExpr} {result : VExpr}
    (shape : info.ctorType = wrapForalls domains result)
    {keys : List FamilyKey} {required : Footprint} {index coveredCount : Nat}
    (rows : ProjectionRows env U registry target required [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels)
      ((domains.map (·.instL levels)).take coveredCount) keys)
    (slice : ProjectionRowSlice env U registry target [] (nativeCaptureSubst [])
      (fun _ => []) (info.ctorType.instL levels)
      ((domains.map (·.instL levels)).take coveredCount) keys
      (info.nparams + index))
    (N : Nat) (bounded : ∀ key ∈ keys.take (info.nparams + index), key.rank ≤ N)
    {parameters xs : List VExpr} {major fieldType : VExpr}
    (parameterCount : parameters.length = info.nparams)
    (selected : info.fieldType name levels parameters index major = some fieldType)
    (arguments : FamilyArguments env U registry target (keys.take (info.nparams + index)) xs
      ((parameters ++ (List.range index).map (fun field => VExpr.proj name field major)).map (·.subst σ)))
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major))
      (FamilyKey.uniform N (keys.take (info.nparams + index)) bounded)) :
    Nonempty (CertificateResult env U registry target callerLocals σ callerAvailable
      fieldType slice.support) := by
  have prefixBound := (List.getElem?_eq_some_iff.mp slice.domainAt).1
  simp only [List.length_take, List.length_map] at prefixBound
  have fieldBound : info.nparams + index < domains.length := by omega
  have fullDomainAt : (domains.map (·.instL levels))[info.nparams + index]? =
      some slice.domain := by
    rw [← List.getElem?_take_of_lt (j := coveredCount) (by omega)]
    exact slice.domainAt
  have domainEq : slice.domain = domains[info.nparams + index].instL levels := by
    have chosen := fullDomainAt
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using fieldBound),
      List.getElem_map] at chosen
    exact (Option.some.inj chosen).symm
  have ctorClosed : info.ctorType.Closed := by
    obtain ⟨level, formation⟩ := hsource.constWF (hsource.projectionConstructor registered)
    exact VExpr.WF.closedN hsource ⟨_, formation⟩ trivial
  let signature : ConstantTelescope info.ctorType := ⟨domains, result, shape⟩
  have domainScope := signature.domain_scope ctorClosed (List.getElem?_eq_getElem fieldBound)
  have scope : slice.domain.ClosedN
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)).length := by
    rw [domainEq]
    simpa only [List.length_append, List.length_map, List.length_range, parameterCount]
      using domainScope.instL (ls := levels)
  have literal := info.fieldType_eq_instOuter shape levelCount parameterCount fieldBound
    (typeName := name) (major := major)
  have equal := Option.some.inj (selected.symm.trans literal)
  rw [equal, ← domainEq]
  exact slice.reifyTemplateAtHeader henv hscoped hsource below headers registered levelsWF
    hTarget closed rows N bounded arguments observations scope

end Lean4Lean.AnchoredSource.Adapted
