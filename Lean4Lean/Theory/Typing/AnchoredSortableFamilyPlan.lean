import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanFront

/-! Finite rich family plans expose actual terminal captures and hereditary
binder certificates without changing the frozen request ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem SortableFamilyPlan.singleton
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) :
    ∃ atom, demand = Profile.singleton atom := by
  match tree with
  | .terminal .. => exact ⟨_, rfl⟩
  | .binder .. => exact ⟨_, rfl⟩
  | .view .. => exact ⟨_, rfl⟩
  | .pad source =>
    obtain ⟨atom, rfl⟩ := source.singleton
    exact ⟨.pad atom, Profile.pad_singleton atom⟩
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega

theorem SortableFamilyPlan.singleton_of_mem
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : SortableFamilyPlan env U registry target name levels signature arguments demand footprint)
    {atom : Atom n} (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  obtain ⟨chosen, rfl⟩ := tree.singleton
  cases List.mem_singleton.mp member
  rfl

noncomputable def SortableFamilyPlan.raise
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint)
    {N : Nat} (bound : n ≤ N) :
    SortableFamilyPlan env U registry target name levels signature arguments (raiseProfile N bound demand) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseProfile_self] using plan
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using plan
    · have low : n ≤ N := by omega
      rw [raiseProfile_step low]
      exact .pad (ih low)

noncomputable def FamilyPlan.toSortable
    (plan : FamilyPlan env U registry target name levels signature arguments profile footprint) :
    SortableFamilyPlan env U registry target name levels signature arguments profile footprint := by
  match plan with
  | .terminal saturated shape relevance captures => exact .terminal saturated shape relevance captures
  | .binder origin domain guard body pack covered =>
    exact .binder origin (.ofCode domain domain.formed) guard body.toSortable pack covered
  | .view source change => exact .view source.toSortable change
  | .pad source => exact .pad source.toSortable
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

theorem SortableFamilyPlan.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (tree : SortableFamilyPlan env U registry Γ name levels signature arguments demand footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ demand := by
  match tree with
  | .terminal _ _ _ _ => exact Profile.Live.singleton_iff.mpr True.intro
  | .binder _ _ guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
  | .view source change =>
    exact Profile.Live.singleton_iff.mpr
      (change.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .pad source => exact Profile.Live.pad_iff.mpr (source.live henv hscoped hΓ leaves)
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega
inductive SortableFamilyPlanFront (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel) {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (arguments : List VExpr) :
    {N : Nat} → Atom N → Footprint → Type where
  | terminal {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint)
      (bound : n + 1 ≤ N)
      (adapter : NormalAtomAdapter env U registry target
        (raiseAtom N bound (.family ⟨name, levels, relevant, keys⟩)) requested) :
      SortableFamilyPlanFront env U registry target name levels signature arguments requested footprint
  | binder {domain : VExpr} {key : Key n} {output : Atom n} {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : SortableCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain true support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : SortableFamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (adapter : NormalAtomAdapter env U registry target (n := n + 1) (.fn key output) requested) :
      SortableFamilyPlanFront env U registry target name levels signature arguments requested
        (domainFootprint ++ outside)

noncomputable def SortableFamilyPlanFront.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : SortableFamilyPlanFront env U registry target name levels signature arguments atom footprint)
    (change : AtomView env U registry target atom atom') :
    SortableFamilyPlanFront env U registry target name levels signature arguments atom' footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    exact .terminal sat shape rel captures bound (adapter.comp (change.toAdapter henv hscoped hTarget))
  | binder origin domain guard body pack covered adapter =>
    exact .binder origin domain guard body pack covered (adapter.comp (change.toAdapter henv hscoped hTarget))

noncomputable def SortableFamilyPlanFront.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (front : SortableFamilyPlanFront env U registry target name levels signature arguments (atom : Atom N) footprint) :
    SortableFamilyPlanFront env U registry target name levels signature arguments (N := N + 1) (.pad atom) footprint := by
  cases front with
  | terminal sat shape rel captures bound adapter =>
    apply SortableFamilyPlanFront.terminal sat shape rel captures (Nat.le_trans bound (Nat.le_succ N))
    simpa only [raiseAtom_step bound, raiseAtom_step (Nat.le_refl N), raiseAtom_self] using adapter.raise henv hscoped hTarget (Nat.le_succ N)
  | @binder n domainFootprint bodyFootprint outside requested domainExpr key output support packed
      origin domain guard body pack covered adapter =>
    have guard' := guard.raise henv (Nat.le_succ _)
    have pack' := pack.raise (Nat.le_succ _)
    have covered' := raiseProfile_subset (Nat.le_succ _) covered
    simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
      raiseProfile_step (Nat.le_refl _), raiseProfile_self] at guard' pack' covered'
    refine .binder origin (.pad domain) guard' (.pad body) pack' covered' ?_
    have first := ((AtomView.commutePadFn (env := env) (U := U) (registry := registry)
      (Γ := target) key output).inverse henv).toAdapter henv hscoped hTarget
    have second := adapter.raise henv hscoped hTarget (Nat.le_succ _)
    simp only [raiseAtom_step (Nat.le_refl _), raiseAtom_self] at second
    exact first.comp second

theorem SortableFamilyPlan.front
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile N}
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint)
    (atom : Atom N) (singleton : demand = Profile.singleton atom) :
    Nonempty (SortableFamilyPlanFront env U registry target name levels signature arguments atom footprint) := by
  match N, demand, footprint, plan with
  | _, _, _, .terminal sat shape rel captures =>
    cases List.singleton_inj.mp singleton
    exact ⟨.terminal sat shape rel captures (Nat.le_refl _) (by
      rw [raiseAtom_self]; exact .refl _)⟩
  | _, _, _, .binder origin domain guard body pack covered =>
    cases List.singleton_inj.mp singleton
    exact ⟨.binder origin domain guard body pack covered (.refl _)⟩
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


end Lean4Lean.AnchoredSource.Adapted
