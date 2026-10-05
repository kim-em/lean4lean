import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationPairedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFuture
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

/-! Dependent Pi replay from finite original application seeds. Each row may
retain many source origins, differing grades, and arbitrary output actions.
The actual captured frame supplies precisely the computed seed requirements;
all returned body certificates, binder packs, and future capabilities are
constructed by paired replay of those original seeds.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure HeaderApplicationPiRow
    {seedEnv : VEnv} {U : Nat}
    (root : EndpointRef seedEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (σ : Subst) (available : Valuation) (A : VExpr) (functionIndex : Nat)
    (relevant : Bool) (ambient : Profile n) (key : Key n) (output : Profile n) where
  guard : LambdaGuard env U registry target σ A key ambient
  formed : output.HasType (.sort relevant)
  source : List VExpr
  locals : List Nat
  realization : Subst
  function : VExpr
  argument : VExpr
  originalFootprint : Footprint
  seeds : RichApplicationSeeds root env registry target source locals realization
    function argument originalFootprint output.atoms
  function_eq : function.subst realization = σ functionIndex
  argument_eq : argument.subst realization = key.anchor
  needs : List Need
  bounded : ∀ need ∈ needs, need.rank ≤ n
  covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms
  resources : (seeds.required (functionIndex + 1) 0).Available (available.push needs)

variable {source headerSource : List VExpr} {locals : List Nat}
  {seedEnv : VEnv} {U : Nat}
  {root : EndpointRef seedEnv U rootSource rootExpression rootType}

noncomputable def HeaderApplicationPiRow.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (row : HeaderApplicationPiRow root env registry Γ σ available A functionIndex relevant ambient key output) :
    HeaderApplicationPiRow root env registry Δ (σ.lift_r ρ) (available.rename ρ) A functionIndex
      relevant (ambient.rename ρ) (key.rename ρ) (output.rename ρ) where
  guard := row.guard.future henv future
  formed := by simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr row.formed
  source := row.source
  locals := row.locals
  realization := row.realization.lift_r ρ
  function := row.function
  argument := row.argument
  originalFootprint := Footprint.rename ρ row.originalFootprint
  seeds := row.seeds.future henv future
  function_eq := by simpa only [lift'_subst, Subst.lift_r] using congrArg (·.lift' ρ) row.function_eq
  argument_eq := by simpa only [lift'_subst, Key.rename] using congrArg (·.lift' ρ) row.argument_eq
  needs := row.needs.map (Need.rename ρ)
  bounded := by
    intro need member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact row.bounded old oldMember
  covered := by
    intro need member atom atomMember
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [← Need.atGrade_rename] at atomMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp atomMember
    exact List.mem_map_of_mem (row.covered old oldMember original originalMember)
  resources := by
    simpa only [RichApplicationSeeds.required_future, Valuation.rename_push] using row.resources.rename ρ

/-- Replay at any admitted argument, constructing the certificate at the
RIGHT realization of the exact original header-body node. -/
theorem HeaderApplicationPiRow.replay
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (row : HeaderApplicationPiRow root env registry target σ available A functionIndex relevant ambient key output)
    (admitted : Admitted env U registry target key key.anchor z) :
    ∃ footprint,
      Nonempty (RichCert headerEnv env U registry target body (Locals.push locals) (τ.cons z)
        relevant output footprint) ∧
      footprint.Available (available.push row.needs) ∧
      TypeRelated env U registry target (.app (σ functionIndex) key.anchor)
        (.app (τ functionIndex) z) output := by
  obtain ⟨⟨localFrame⟩, localSubstitutions⟩ := frame.pushAdmitted henv headerBelow substitutions
    domain location lineage domainCode domainResources row.guard admitted row.needs row.bounded row.covered
  have lookup : Lookup (A :: headerSource) (functionIndex + 1)
      (.forallE A.lift (familyBody.liftN 1 1)) := functionLookup.succ
  obtain ⟨footprint, ⟨certificate⟩, resources, related⟩ := row.seeds.headerReplayPaired
    henv hscoped formed row.formed localFrame localSubstitutions body row.resources lookup Lookup.zero
    row.function_eq row.argument_eq
  exact ⟨footprint, ⟨certificate⟩, resources, by
    simpa only [subst, Subst.cons, row.function_eq, row.argument_eq, Profile.mk, Profile.atoms] using related⟩

/-- The row's source query is rebuilt at the original frozen anchor, and
its binder pack is computed from the actual returned finite resources. -/
theorem HeaderApplicationPiRow.reconstruct
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (row : HeaderApplicationPiRow root env registry target σ available A functionIndex relevant ambient key output) :
    ∃ footprint,
      Nonempty (RichRows headerEnv env U registry target (.ref domain) body locals σ relevant ambient
        [(key, output)] footprint) ∧ footprint.Available available := by
  obtain ⟨bodyFootprint, ⟨bodyCode⟩, bodyResources, _⟩ := row.replay henv hscoped headerBelow formed
    substitutions frame domain location lineage body domainCode domainResources functionLookup row.guard.anchor
  obtain ⟨packed, outside, pack, covered, resources⟩ :=
    Footprint.pack_available bodyResources row.bounded row.covered
  refine ⟨outside, ⟨?_⟩, resources⟩
  simpa only [List.append_nil] using
    RichRows.cons (domain := EndpointState.ref domain) row.guard bodyCode pack covered RichRows.nil

private theorem admitted_from_anchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target key key.anchor x ∧
      Admitted env U registry target key key.anchor y := by
  obtain ⟨anchorRaw, pairRaw, support, typed, formed, code, anchor, pair⟩ := admitted
  have anchorSelf := Related.left_diagonal anchor
  exact ⟨⟨anchorRaw.hasType.1, anchorRaw, support, typed, formed, code, anchorSelf, anchor⟩,
    ⟨anchorRaw.hasType.1, anchorRaw.trans pairRaw, support, typed, formed, code,
      anchorSelf, Related.trans henv hscoped anchor pair⟩⟩

/-- The same finite seed row provides the arbitrary-argument capability in
every future context. Future transport and paired source replay are both
performed here; no future-body semantic premise is added to the row data. -/
theorem HeaderApplicationPiRow.capability
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (row : HeaderApplicationPiRow root env registry target σ available A functionIndex relevant ambient key output)
    (future : FutureInsertion env U target Δ ρ)
    (admitted : Admitted env U registry Δ (key.rename ρ) x y) :
    TypeRelated env U registry Δ
      ((((VExpr.app (.bvar (functionIndex + 1)) (.bvar 0)).subst σ.lift).lift' ρ.cons).inst x)
      ((((VExpr.app (.bvar (functionIndex + 1)) (.bvar 0)).subst σ.lift).lift' ρ.cons).inst y)
      (output.rename ρ) := by
  let shifted := row.future henv future
  have atArgument : ∀ z, Admitted env U registry Δ (key.rename ρ) (key.rename ρ).anchor z →
      TypeRelated env U registry Δ (.app ((σ functionIndex).lift' ρ) (key.anchor.lift' ρ))
        (.app ((σ functionIndex).lift' ρ) z) (output.rename ρ) := by
    intro z hz
    obtain ⟨_, _, _, related⟩ := shifted.replay henv hscoped headerBelow (future.targetWF henv)
      (substitutions.future henv future) (frame.future henv future) domain location lineage body
      (domainCode.future henv future) (domainResources.rename ρ) functionLookup hz
    exact related
  obtain ⟨toLeft, toRight⟩ := admitted_from_anchor henv hscoped admitted
  have sorted : (output.rename ρ).HasType (.sort relevant) := by
    simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr row.formed
  have pair := ((atArgument x toLeft).symm henv sorted.wf_value).trans henv (atArgument y toRight)
  have instantiated (z : VExpr) :
      (((VExpr.app (.bvar (functionIndex + 1)) (.bvar 0)).subst σ.lift).lift' ρ.cons).inst z =
        .app ((σ functionIndex).lift' ρ) z := by
    rw [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons]
    rfl
  simpa only [instantiated] using pair

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
