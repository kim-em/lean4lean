import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanResult
import Lean4Lean.Theory.Typing.AnchoredConstructorPlanFront

/-! Exposing a native constructor plan retains its actual original domain
and result occurrences, including rich projected certificates. Only finite
views and padding are traversed; no semantic call supplies a missing child. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive RichConstructorPlanFront (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {headerEnv : VEnv} {declaredType : VExpr} {headerLevel : VLevel}
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel))
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType)
    {source : List VExpr} (context : ContextDerivation headerEnv U source)
    (σ : Subst) (arguments : List VExpr) :
    {N : Nat} → Atom N → Footprint → Type where
  | terminal {family : FamilyData (Profile n)} {keys : List (DataRequest (Profile n))}
      {familyLevels : List VLevel} {familyArguments : List VExpr}
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
      (relevant : family.relevant = true)
      (resultNode : EndpointState headerEnv U source signature.result (.sort resultLevel))
      (resultLocation : Located header resultNode)
      (resultLineage : resultLocation.contextDerivation .nil = context)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (constantCaptureVariables arguments.length) keys captureFootprint)
      (resultCode : RichCert headerEnv env U registry target resultNode (List.range arguments.length)
        σ true
        (Profile.singleton (n := n + 1) (.family family)) resultFootprint)
      (bound : n + 1 ≤ N)
      (adapter : NormalAtomAdapter env U registry target
        (raiseAtom N bound (.ctor ⟨name, levels, keys, family, relevant⟩)) requested) :
      RichConstructorPlanFront env U registry target header name levels signature context σ arguments requested
        (captureFootprint ++ resultFootprint)
  | terminalRecord {demand : RecordData (Profile n)} {projection : VProjectionInfo}
      {familyLevels : List VLevel} {familyArguments : List VExpr}
      (registered : env.projections demand.family.name projection)
      (lookup : registry.projections demand.family.name = some projection)
      (constructorName : projection.ctorName = name)
      (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
      (resultNode : EndpointState headerEnv U source signature.result (.sort resultLevel))
      (resultLocation : Located header resultNode)
      (resultLineage : resultLocation.contextDerivation .nil = context)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length) σ
        (demand.fields.map fun entry => .bvar (arguments.length - 1 - (projection.nparams + entry.1)))
        (demand.fields.map (·.2)) captureFootprint)
      (resultCode : RichCert headerEnv env U registry target resultNode (List.range arguments.length) σ true
        (Profile.singleton (n := n + 1) (.family demand.family)) resultFootprint)
      (origins : ∀ entry ∈ demand.fields,
        Nonempty (RankedData.ProjectionOrigin env U target projection demand.family.name entry.1
          (mkApps (.const name levels) ((constantCaptureVariables arguments.length).map (·.subst σ)))
          (signature.result.subst σ) entry.2.domain))
      (bound : n + 1 ≤ N)
      (adapter : NormalAtomAdapter env U registry target (raiseAtom N bound (.record demand)) requested) :
      RichConstructorPlanFront env U registry target header name levels signature context σ arguments requested
        (captureFootprint ++ resultFootprint)
  | binder {domain : VExpr} {key : Key n} {output : Atom n} {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (original : EndpointRef headerEnv U source domain (.sort level))
      (location : Located header (.ref original))
      (lineage : location.contextDerivation .nil = context)
      (domainCode : RichCert headerEnv env U registry target (.ref original) (List.range arguments.length)
        σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ domain key support)
      (body : RichConstructorPlan env U registry target header name levels signature (.cons context original)
        (σ.cons key.anchor) (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (adapter : NormalAtomAdapter env U registry target (n := n + 1) (.fn key output) requested) :
      RichConstructorPlanFront env U registry target header name levels signature context σ arguments requested
        (domainFootprint ++ outside)

noncomputable def RichConstructorPlanFront.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : RichConstructorPlanFront env U registry target header name levels signature context σ arguments atom footprint)
    (change : AtomView env U registry target atom atom') :
    RichConstructorPlanFront env U registry target header name levels signature context σ arguments atom' footprint := by
  cases front with
  | terminal sat shape rel node location lineage captures code bound adapter =>
    exact .terminal sat shape rel node location lineage captures code bound (adapter.comp (change.toAdapter henv hscoped hTarget))
  | terminalRecord registered lookup cname bounded sat shape node location lineage captures code origins bound adapter =>
    exact .terminalRecord registered lookup cname bounded sat shape node location lineage captures code origins
      bound (adapter.comp (change.toAdapter henv hscoped hTarget))
  | binder origin original location lineage domain guard body pack covered adapter =>
    exact .binder origin original location lineage domain guard body pack covered (adapter.comp (change.toAdapter henv hscoped hTarget))

noncomputable def RichConstructorPlanFront.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : RichConstructorPlanFront env U registry target header name levels signature context σ arguments (atom : Atom N) footprint) :
    RichConstructorPlanFront env U registry target header name levels signature context σ arguments (N := N + 1) (.pad atom) footprint := by
  cases front with
  | terminal sat shape rel node location lineage captures code bound adapter =>
    apply RichConstructorPlanFront.terminal sat shape rel node location lineage captures code (Nat.le_trans bound (Nat.le_succ N))
    simpa only [raiseAtom_step bound, raiseAtom_step (Nat.le_refl N), raiseAtom_self] using adapter.raise henv hscoped hTarget (Nat.le_succ N)
  | terminalRecord registered lookup cname bounded sat shape node location lineage captures code origins bound adapter =>
    apply RichConstructorPlanFront.terminalRecord registered lookup cname bounded sat shape node location lineage
      captures code origins (Nat.le_trans bound (Nat.le_succ N))
    simpa only [raiseAtom_step bound, raiseAtom_step (Nat.le_refl N), raiseAtom_self] using adapter.raise henv hscoped hTarget (Nat.le_succ N)
  | @binder n level domainFootprint bodyFootprint outside requested domainExpr key output support packed
      origin original location lineage domain guard body pack covered adapter =>
    have guard' := guard.raise henv (Nat.le_succ _)
    have pack' := pack.raise (Nat.le_succ _)
    have covered' := raiseProfile_subset (Nat.le_succ _) covered
    simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
      raiseProfile_step (Nat.le_refl _), raiseProfile_self] at guard' pack' covered'
    refine .binder origin original location lineage (.pad domain) guard' (.pad body) pack' covered' ?_
    have first := ((AtomView.commutePadFn (env := env) (U := U) (registry := registry)
      (Γ := target) key output).inverse henv).toAdapter henv hscoped hTarget
    have second := adapter.raise henv hscoped hTarget (Nat.le_succ _)
    simp only [raiseAtom_step (Nat.le_refl _), raiseAtom_self] at second
    exact first.comp second

theorem RichConstructorPlan.front
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile N}
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint)
    (atom : Atom N) (singleton : demand = Profile.singleton atom) :
    Nonempty (RichConstructorPlanFront env U registry target header name levels signature context σ arguments atom footprint) := by
  match N, demand, footprint, plan with
  | _, _, _, .terminal sat shape rel node location lineage captures code =>
    cases List.singleton_inj.mp singleton
    exact ⟨.terminal sat shape rel node location lineage captures code (Nat.le_refl _) (by
      rw [raiseAtom_self]; exact .refl _)⟩
  | _, _, _, .terminalRecord registered lookup cname bounded sat shape node location lineage captures code origins =>
    cases List.singleton_inj.mp singleton
    exact ⟨.terminalRecord registered lookup cname bounded sat shape node location lineage captures code origins
      (Nat.le_refl _) (by rw [raiseAtom_self]; exact .refl _)⟩
  | _, _, _, .binder origin original location lineage domain guard body pack covered =>
    cases List.singleton_inj.mp singleton
    exact ⟨.binder origin original location lineage domain guard body pack covered (.refl _)⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp singleton
    obtain ⟨front⟩ := source.front henv hscoped hTarget _ rfl
    exact ⟨front.view henv hscoped hTarget change⟩
  | _, _, _, .pad source =>
    obtain ⟨original, same, output⟩ := List.map_eq_singleton_iff.mp singleton
    cases output
    obtain ⟨front⟩ := source.front henv hscoped hTarget original same
    exact ⟨front.pad henv hscoped hTarget⟩
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
