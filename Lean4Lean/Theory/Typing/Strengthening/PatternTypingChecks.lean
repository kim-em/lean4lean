import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Compiled
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! # Uniform replay of concrete pattern checks

The quotient typing argument is adapted from route A's `CoreDescent.lean`.
Here the result is packaged uniformly over all matching typed occurrences, so a
raw computation can retain its certificate through arbitrary syntactic lifts.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean.VExpr

/-- The head of a typed application spine is typed. -/
theorem mkApps_head_hasType {env : VEnv} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {fn T : VExpr}, env.HasType U Γ (VExpr.mkApps fn args) T →
      ∃ T', env.HasType U Γ fn T'
  | [], _, _, h => ⟨_, h⟩
  | a :: args, fn, _, h =>
    let ⟨_, h'⟩ := mkApps_head_hasType henv hΓ (args := args) (fn := .app fn a) h
    let ⟨_, _, hf, _⟩ := h'.app_inv henv hΓ
    ⟨_, hf⟩

/-- The alignment checks of the quotient rule hold below as soon as the instance is typed
below: the major `Quot.mk [u'] α' r' a` is typed at `Quot [u] α r` by the type of `Quot.lift`,
and `Quot` is rigid. The universe guard is context-free. -/
theorem quot_check_of_typed {env : VEnv} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) {e T : VExpr} {m1 : List VLevel} {m2 : quotPattern.Path → VExpr}
    (hm : quotPattern.Matches e m1 m2) (he : env.HasType U Γ e T)
    (hnz : ¬ ((VLevel.param 0).inst m1 ≈ .zero)) :
    quotPatternCheck.OK (env.IsDefEqU U Γ) m1 m2 := by
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, hrec, hctor⟩ := SimplePattern.iota_matches_inv hm
  obtain ⟨x₀, x₁, x₂, x₃, x₄, rfl⟩ : ∃ x₀ x₁ x₂ x₃ x₄, recArgs = [x₀, x₁, x₂, x₃, x₄] := by
    rcases recArgs with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, _, rfl⟩ | simp at h1
  obtain ⟨y₀, y₁, y₂, rfl⟩ : ∃ y₀ y₁ y₂, ctorArgs = [y₀, y₁, y₂] := by
    rcases ctorArgs with _ | ⟨y₀, _ | ⟨y₁, _ | ⟨y₂, _ | ⟨_, _⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, rfl⟩ | simp at h2
  -- the levels of the head
  obtain ⟨_, hhead⟩ := mkApps_head_hasType henv hΓ he
  obtain ⟨ci, hci, hwf, hlen⟩ := hhead.const_inv henv hΓ
  rw [hr.lift] at hci
  cases hci
  change m1.length = 2 at hlen
  obtain ⟨u, v, rfl⟩ : ∃ u v, m1 = [u, v] := by
    rcases m1 with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
  have hu : u.WF U := hwf u (by simp)
  have hv : v.WF U := hwf v (by simp)
  have hM := QuotRegistered.major_type henv hΓ hr hu hv (major := mkApps (.const ``Quot.mk lsC) [y₀, y₁, y₂])
    ⟨_, he⟩
  -- the levels of the constructor
  obtain ⟨_, hheadM⟩ := mkApps_head_hasType henv hΓ hM
  obtain ⟨ci, hci, hwfM, hlenM⟩ := hheadM.const_inv henv hΓ
  rw [hr.constructor] at hci
  cases hci
  change lsC.length = 1 at hlenM
  obtain ⟨u', rfl⟩ : ∃ u', lsC = [u'] := by
    rcases lsC with _ | ⟨u', _ | ⟨_, _⟩⟩ <;> simp_all
  have hu' : u'.WF U := hwfM u' (by simp)
  -- the type of the constructor spine
  obtain ⟨res, hw, hres⟩ := HasType.mkApps_telescope henv hΓ
    (HasType.const hr.constructor (ls := [u']) (by simpa using hu') rfl) ⟨_, hM⟩ (by rfl)
  cases hw with | cons ha hw =>
  cases hw with | cons hrel hw =>
  cases hw with | cons hval hw =>
  cases hw
  simp [VExpr.instL, VExpr.inst, VLevel.inst, VExpr.inst_lift, ← VExpr.lift_instN_lo] at hres
  have hQQ := hM.uniqU henv hΓ hres
  obtain ⟨_, hsort⟩ := hM.isType henv.ordered hΓ
  have hinj := (IsDefEqU.rigidApp_inv (args := [x₀, x₁]) (args' := [y₀, y₁]) henv hΓ
    (hr.quot_rigid henv) hQQ hsort).2
  cases hinj with | cons hx₀ hinj =>
  cases hinj with | cons hx₁ _ =>
  have e0 : m2 (Sum.inl (some (some (some (some none))))) = x₀ := hrec 0 (by omega)
  have e1 : m2 (Sum.inl (some (some (some none)))) = x₁ := hrec 1 (by omega)
  have f0 : m2 (Sum.inr (some (some none))) = y₀ := hctor 0 (by omega)
  have f1 : m2 (Sum.inr (some none)) = y₁ := hctor 1 (by omega)
  simp only [quotPatternCheck, Pattern.Check.OK, Pattern.RHS.apply]
  refine ⟨hnz, ?_, ?_, trivial⟩
  · simpa only [e0, f0] using hx₀
  · simpa only [e1, f1] using hx₁

/-- Every matching typed occurrence at these levels passes the rule's checks.
The context, source, and captures are all universally quantified: this certificate
has no dependency on the occurrence that originally enabled a computation. -/
def CheckFromTyping (env : VEnv) (U : Nat) (p : Pattern)
    (r : p.RHS × p.Check) (levels : List VLevel) : Prop :=
  ∀ {Γ e T captures}, OnCtx Γ (env.IsType U) → p.Matches e levels captures →
    env.HasType U Γ e T → r.2.OK (env.IsDefEqU U Γ) levels captures

/-- An enabled concrete rule passes its checks at every typed occurrence with
these levels. Ordinary iota guards depend only on levels; quotient alignments
are re-established from the new occurrence's typing by rigid-head injectivity. -/
theorem ConcretePattern.checkFromTyping {env : VEnv} (henv : env.WF)
    {p : Pattern} {r : p.RHS × p.Check} (hp : ConcretePattern env p r)
    {relation : VExpr → VExpr → Prop} {levels : List VLevel} {captures : p.Path → VExpr}
    (hck : r.2.OK relation levels captures) : CheckFromTyping env U p r levels := by
  intro Γ e T captures₀ hΓ hm ht
  rcases hp with hd | hq | hi
  · cases hd
    trivial
  · cases hq
    simp only [quotPatternCheck, Pattern.Check.OK] at hck
    exact quot_check_of_typed henv hΓ ‹QuotRegistered env› hm ht hck.1
  · cases hi with | intro _ _ =>
    unfold InductiveSignature.RecursorData.guard
    unfold InductiveSignature.RecursorData.guard at hck
    split <;> simp_all [Pattern.Check.OK]

end Lean4Lean.VEnv.Strengthening.PureObservation
