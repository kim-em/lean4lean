import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanResult
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanFront

/-! Expose the actual retained native family plan. Every binder keeps its
original header occurrence and lineage; no canonical registration header
or freshly normalized telescope is substituted for that original plan. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000

inductive RichFamilyPlanFront (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {headerEnv : VEnv} {declaredType : VExpr} {headerLevel : VLevel}
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel))
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType)
    {source : List VExpr} (context : ContextDerivation headerEnv U source)
    (σ : Subst) (arguments : List VExpr) :
    {N : Nat} → Atom N → Footprint → Type where
  | terminal {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (constantCaptureVariables arguments.length) keys footprint)
      (bound : n + 1 ≤ N)
      (adapter : NormalAtomAdapter env U registry target
        (raiseAtom N bound (.family ⟨name, levels, relevant, keys⟩)) requested) :
      RichFamilyPlanFront env U registry target header name levels signature context σ arguments requested footprint
  | binder {domain : VExpr} {level : VLevel} {key : Key n} {output : Atom n} {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (original : EndpointRef headerEnv U source domain (.sort level))
      (location : Located header (.ref original))
      (lineage : location.contextDerivation .nil = context)
      (domainCode : RichCert headerEnv env U registry target (.ref original) (List.range arguments.length)
        σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ domain key support)
      (body : RichFamilyPlan env U registry target header name levels signature (.cons context original) (σ.cons key.anchor) (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (adapter : NormalAtomAdapter env U registry target (n := n + 1) (.fn key output) requested) :
      RichFamilyPlanFront env U registry target header name levels signature context σ arguments requested
        (domainFootprint ++ outside)

noncomputable def RichFamilyPlanFront.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : RichFamilyPlanFront env U registry target header name levels signature context σ arguments atom footprint)
    (change : AtomView env U registry target atom atom') :
    RichFamilyPlanFront env U registry target header name levels signature context σ arguments atom' footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    exact .terminal sat shape rel captures bound (adapter.comp (change.toAdapter henv hscoped hTarget))
  | binder origin original location lineage domain guard body pack covered adapter =>
    exact .binder origin original location lineage domain guard body pack covered (adapter.comp (change.toAdapter henv hscoped hTarget))

noncomputable def RichFamilyPlanFront.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : RichFamilyPlanFront env U registry target header name levels signature context σ arguments (atom : Atom N) footprint) :
    RichFamilyPlanFront env U registry target header name levels signature context σ arguments (N := N + 1) (.pad atom) footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    apply RichFamilyPlanFront.terminal sat shape rel captures (Nat.le_trans bound (Nat.le_succ N))
    simpa only [raiseAtom_step bound, raiseAtom_step (Nat.le_refl N), raiseAtom_self] using adapter.raise henv hscoped hTarget (Nat.le_succ N)
  | @binder n domainFootprint bodyFootprint outside requested domainExpr level key output support packed
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

theorem RichFamilyPlan.front
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile N}
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint)
    (atom : Atom N) (singleton : demand = Profile.singleton atom) :
    Nonempty (RichFamilyPlanFront env U registry target header name levels signature context σ arguments atom footprint) := by
  match N, demand, footprint, plan with
  | _, _, _, .terminal sat shape rel captures =>
    cases List.singleton_inj.mp singleton
    exact ⟨.terminal sat shape rel captures (Nat.le_refl _) (by
      rw [raiseAtom_self]; exact .refl _)⟩
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
