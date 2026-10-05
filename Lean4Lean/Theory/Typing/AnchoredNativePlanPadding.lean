import Lean4Lean.Theory.Typing.AnchoredNativeInitialArguments
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaGrades
import Lean4Lean.Theory.Typing.AnchoredNativeDepth
import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

/-! Raising a native telescope distributes padding through its actual binders.
Each terminal RHS and domain certificate is padded, and each binder input is
raised without changing its source requirements. The resulting reversible
view relates the concrete new demand to ordinary outer padding. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

structure NativePlanPadding
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (original : NativePlan env U registry target signature arguments (.singleton atom) footprint) where
  output : Atom (n + 1)
  plan : NativePlan env U registry target signature arguments (.singleton output) footprint
  view : AtomView env U registry target (n := n + 1) (.pad atom) output
  depth : ∀ current, plan.nativeDepth current = original.nativeDepth current

noncomputable def NativePlan.padSingleton
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (henv : env.Ordered)
    (plan : NativePlan env U registry target signature arguments (.singleton atom) footprint) :
    NativePlanPadding plan := by
  match n, atom, plan with
  | _, atom, .terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq
      witnesses witnessLength witnessPrefix alignment literal body captures =>
    exact ⟨.pad atom, .terminal program selected lhsClosed rhsClosed saturated noTrailing
      prefixEq witnesses witnessLength witnessPrefix alignment literal (.pad body) captures,
      .refl _, by intro current; simp only [NativePlan.nativeDepth, Obs.nativeDepth]⟩
  | _ + 1, .fn key output, .binder origin domain guard body pack covered =>
    let child := body.padSingleton henv
    have guard' := guard.raise henv (Nat.le_succ _)
    have pack' := pack.raise (Nat.le_succ _)
    have covered' := raiseProfile_subset (Nat.le_succ _) covered
    simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
      raiseProfile_step (Nat.le_refl _), raiseProfile_self] at guard' pack' covered'
    exact ⟨.fn (Key.pad key) child.output, .binder origin (.pad domain) guard' child.plan pack' covered',
      .trans (.commutePadFn key output) (.fn (Key.pad key) child.view), by
        intro current
        simp only [NativePlan.nativeDepth, CodeCert.nativeDepth, child.depth]⟩
termination_by n
decreasing_by omega

structure NativeInitialTreePadding
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint) where
  output : Atom (n + 1)
  tree : NativeInitialTree env U registry target signature arguments (.singleton output) footprint
  view : AtomView env U registry target (n := n + 1) (.pad atom) output

noncomputable def NativeInitialTree.padSingleton
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (henv : env.Ordered)
    (tree : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint) :
    NativeInitialTreePadding tree := by
  match n, atom, tree with
  | _, atom, .terminal leaf =>
    exact ⟨.pad atom, .terminal {
      program := leaf.program
      selected := leaf.selected
      saturated := leaf.saturated
      noTrailing := leaf.noTrailing
      prefix_eq := leaf.prefix_eq
      witnesses := leaf.witnesses
      witnessLength := leaf.witnessLength
      witnessPrefix := leaf.witnessPrefix
      arguments_eq := leaf.arguments_eq
      bodyFootprint := leaf.bodyFootprint
      body := .pad leaf.body
      captures := leaf.captures }, .refl _⟩
  | _ + 1, .fn key output, .binder origin domain guard body pack covered =>
    let child := body.padSingleton henv
    have guard' := guard.raise henv (Nat.le_succ _)
    have pack' := pack.raise (Nat.le_succ _)
    have covered' := raiseProfile_subset (Nat.le_succ _) covered
    simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
      raiseProfile_step (Nat.le_refl _), raiseProfile_self] at guard' pack' covered'
    exact ⟨.fn (Key.pad key) child.output, .binder origin (.pad domain) guard' child.tree pack' covered',
      .trans (.commutePadFn key output) (.fn (Key.pad key) child.view)⟩
termination_by n
decreasing_by omega


structure NativePlanRaising
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} (bound : n ≤ N)
    (original : NativePlan env U registry target signature arguments (.singleton atom) footprint) where
  output : Atom N
  plan : NativePlan env U registry target signature arguments (.singleton output) footprint
  view : AtomView env U registry target (raiseAtom N bound atom) output
  depth : ∀ current, plan.nativeDepth current = original.nativeDepth current

noncomputable def NativePlan.raiseSingleton
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (henv : env.Ordered) {N : Nat} (bound : n ≤ N)
    (original : NativePlan env U registry target signature arguments (.singleton atom) footprint) :
    NativePlanRaising bound original := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ⟨atom, original, by simpa only [raiseAtom_self] using (AtomView.refl atom), fun _ => rfl⟩
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      exact ⟨atom, original, by simpa only [raiseAtom_self] using (AtomView.refl atom), fun _ => rfl⟩
    · have previousBound : n ≤ N := by omega
      let previous := ih previousBound
      let padded := previous.plan.padSingleton henv
      refine ⟨padded.output, padded.plan, ?_, ?_⟩
      · rw [raiseAtom_step previousBound]
        exact .trans (.pad previous.view) padded.view
      · intro current; exact (padded.depth current).trans (previous.depth current)

/-- The whole source-type certificate changes with the distributed demand;
its footprint and native nesting stay fixed. -/
noncomputable def NativePlanRaising.certificate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativePlan env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativePlanRaising bound original)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {support : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry target locals σ expression support required) :
    CodeCert env U registry target locals σ expression
      (raised.view.mapType (raiseProfile N bound support)) required :=
  .map raised.view (certificate.raise bound)

theorem NativePlanRaising.typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativePlan env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativePlanRaising bound original)
    {support : Profile n} (typed : (Profile.singleton atom).HasType support) :
    (Profile.singleton raised.output).HasType
      (raised.view.mapType (raiseProfile N bound support)) := by
  apply raised.view.mapType_typed
  simpa only [raiseProfile_singleton] using Profile.HasType.raise bound typed


structure NativeInitialTreeRaising
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} (bound : n ≤ N)
    (original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint) where
  output : Atom N
  tree : NativeInitialTree env U registry target signature arguments (.singleton output) footprint
  view : AtomView env U registry target (raiseAtom N bound atom) output

noncomputable def NativeInitialTree.raiseSingleton
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint}
    (henv : env.Ordered) {N : Nat} (bound : n ≤ N)
    (original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint) :
    NativeInitialTreeRaising bound original := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ⟨atom, original, by simpa only [raiseAtom_self] using (AtomView.refl atom)⟩
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      exact ⟨atom, original, by simpa only [raiseAtom_self] using (AtomView.refl atom)⟩
    · have previousBound : n ≤ N := by omega
      let previous := ih previousBound
      let padded := previous.tree.padSingleton henv
      refine ⟨padded.output, padded.tree, ?_⟩
      · rw [raiseAtom_step previousBound]
        exact .trans (.pad previous.view) padded.view

/-- The whole source-type certificate changes with the distributed demand;
its footprint and native nesting stay fixed. -/
noncomputable def NativeInitialTreeRaising.certificate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativeInitialTreeRaising bound original)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {support : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry target locals σ expression support required) :
    CodeCert env U registry target locals σ expression
      (raised.view.mapType (raiseProfile N bound support)) required :=
  .map raised.view (certificate.raise bound)

theorem NativeInitialTreeRaising.typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativeInitialTreeRaising bound original)
    {support : Profile n} (typed : (Profile.singleton atom).HasType support) :
    (Profile.singleton raised.output).HasType
      (raised.view.mapType (raiseProfile N bound support)) := by
  apply raised.view.mapType_typed
  simpa only [raiseProfile_singleton] using Profile.HasType.raise bound typed

noncomputable def NativePlanRaising.adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativePlan env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativePlanRaising bound original)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U)) :
    NormalProfileAdapter env U registry target (.singleton raised.output)
      (raiseProfile N bound (.singleton atom)) := by
  rw [raiseProfile_singleton]
  exact (ProfileView.cons (raised.view.inverse henv) ProfileView.nil).toAdapter henv hscoped hTarget

theorem NativePlanRaising.certificateDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativePlan env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativePlanRaising bound original)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {support : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry target locals σ expression support required)
    (current : Name → Bool) :
    (raised.certificate certificate).nativeDepth current = certificate.nativeDepth current := by
  simp only [NativePlanRaising.certificate, CodeCert.nativeDepth, CodeCert.nativeDepth_raise]

noncomputable def NativeInitialTreeRaising.adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativeInitialTreeRaising bound original)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U)) :
    NormalProfileAdapter env U registry target (.singleton raised.output)
      (raiseProfile N bound (.singleton atom)) := by
  rw [raiseProfile_singleton]
  exact (ProfileView.cons (raised.view.inverse henv) ProfileView.nil).toAdapter henv hscoped hTarget

theorem NativeInitialTreeRaising.certificateDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {atom : Atom n} {footprint : Footprint} {N : Nat} {bound : n ≤ N}
    {original : NativeInitialTree env U registry target signature arguments (.singleton atom) footprint}
    (raised : NativeInitialTreeRaising bound original)
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {support : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry target locals σ expression support required)
    (current : Name → Bool) :
    (raised.certificate certificate).nativeDepth current = certificate.nativeDepth current := by
  simp only [NativeInitialTreeRaising.certificate, CodeCert.nativeDepth, CodeCert.nativeDepth_raise]

end Lean4Lean.AnchoredSource.Adapted
