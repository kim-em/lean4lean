import Lean4Lean.Theory.Typing.Strengthening.NormalDescent
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Compiled
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! # Descent of core reductions

The reduction side of route A, for the core calculus `ParRed` (β and the registered pattern
rules): a parallel step above on the lift of a term typed below is the lift of a parallel step
below, with **no hypothesis** beyond well-formedness (`ParRed.descend`). The reduct of every
core rule is a syntactic function of the lifted input; the only context-dependent data are the
pattern checks, and the concrete table of a well-formed environment (`WF.checkDescends`) has
none that needs the smaller context: definitions carry `.true`, registered ι rules carry a
universe guard (context-free), and the quotient rule's two alignment checks hold below whenever
the instance is typed below (`quot_check_of_typed`: the major `Quot.mk α' r' a` is typed at
`Quot α r`, so `α ≡ α'` and `r ≡ r'` by injectivity of the rigid head `Quot`). PR #53's study
discharged this check with the typed front; typing alone suffices.

What does *not* descend this way: `FullStep.funEta`/`structEta` (reducts are not lifts: their
annotations are read off a typing above) and `delta`/`quotDelta` (singleton prefix unfolding:
its `UnfoldingCheck` aligns the indices of a major typed below, a conversion between
propositionally equal terms). -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr

/-! ## The quotient check from typing -/

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

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- The pattern checks of the table descend from a lifted typed instance to its instance
below. -/
def CheckDescends : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check} {ρ : Lift} {Γ Γ' : List VExpr} {e T : VExpr}
    {m1 : List VLevel} {m2 : p.Path → VExpr},
    Pat p r → Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    p.Matches e m1 m2 → Γ ⊢ e : T →
    r.2.OK (IsDefEqU Params.env univs Γ') m1 (fun x => (m2 x).lift' ρ) →
    r.2.OK (IsDefEqU Params.env univs Γ) m1 m2

/-- **Descent of core parallel reduction.** A `ParRed` step above on the lift of a term typed
below is the lift of a `ParRed` step below, given the descent of the checks. -/
theorem ParRed.descend (hck : CheckDescends) {Γ' : List VExpr} {l out : VExpr}
    (H : ParRed Γ' l out) : ∀ {ρ : Lift} {Γ : List VExpr} {e T : VExpr},
    Ctx.Lift' ρ Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Γ ⊢ e : T → e.lift' ρ = l → ∃ e', out = e'.lift' ρ ∧ ParRed Γ e e' := by
  induction H with
  | bvar => intro ρ Γ e T W hΓ hΓ' he hl; exact ⟨e, hl.symm, .rfl⟩
  | sort => intro ρ Γ e T W hΓ hΓ' he hl; exact ⟨e, hl.symm, .rfl⟩
  | const => intro ρ Γ e T W hΓ hΓ' he hl; exact ⟨e, hl.symm, .rfl⟩
  | app _ _ ihf iha =>
    intro ρ Γ e T W hΓ hΓ' he hl
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨f', rfl, hf'⟩ := ihf W hΓ hΓ' hf rfl
    obtain ⟨a', rfl, ha'⟩ := iha W hΓ hΓ' ha rfl
    exact ⟨.app f' a', rfl, .app hf' ha'⟩
  | proj _ ih =>
    intro ρ Γ e T W hΓ hΓ' he hl
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨m', rfl, hm'⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨.proj _ _ m', rfl, .proj hm'⟩
  | lam _ _ ihA ihb =>
    intro ρ Γ e T W hΓ hΓ' he hl
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    obtain ⟨A', rfl, hA'⟩ := ihA W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ihb (W.cons (A := A)) ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weak' henv W⟩ hb rfl
    exact ⟨.lam A' b', rfl, .lam hA' hb'⟩
  | forallE _ _ ihA ihB =>
    intro ρ Γ e T W hΓ hΓ' he hl
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv.ordered
    obtain ⟨A', rfl, hA'⟩ := ihA W hΓ hΓ' hA rfl
    obtain ⟨B', rfl, hB'⟩ := ihB (W.cons (A := A)) ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weak' henv W⟩ hB rfl
    exact ⟨.forallE A' B', rfl, .forallE hA' hB'⟩
  | beta _ _ ihb iha =>
    intro ρ Γ e T W hΓ hΓ' he hl
    obtain ⟨f, a, rfl, hf, rfl⟩ := lift'_eq_app hl
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hf.symm
    obtain ⟨A₁, B₁, hlam, ha⟩ := he.app_inv henv hΓ
    obtain ⟨⟨u, hA⟩, -⟩ := hlam.lam_inv henv hΓ
    obtain ⟨B, -, hb⟩ := hlam.lam_inv_forallE henv hΓ
    obtain ⟨b', rfl, hb'⟩ := ihb (W.cons (A := A)) ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weak' henv W⟩ hb rfl
    obtain ⟨a', rfl, ha'⟩ := iha W hΓ hΓ' ha rfl
    exact ⟨b'.inst a', (lift'_inst_hi b' a' ρ).symm, .beta hb' ha'⟩
  | extra hp hm hchk hargs ih =>
    intro ρ Γ e T W hΓ hΓ' he hl
    subst hl
    obtain ⟨m2₀, hm₀, hm2⟩ := Pattern.matches_lift'.1 hm
    have hm2f := funext hm2
    subst hm2f
    obtain ⟨m2₀', hm2'⟩ := Classical.axiomOfChoice fun a =>
      let ⟨_, ht⟩ := hm₀.hasType hΓ he a
      ih a W hΓ hΓ' ht rfl
    refine ⟨_, ?_, .extra hp hm₀ (hck hp W hΓ hm₀ he hchk) fun a => (hm2' a).2⟩
    rw [Pattern.RHS.lift'_apply]
    congr 1
    exact funext fun a => (hm2' a).1

end

/-- The checks of the concrete pattern table of a well-formed environment descend from any
lifted typed instance: definitions are unguarded, registered ι rules carry a context-free
universe guard, and the quotient rule's alignment checks follow from typing
(`quot_check_of_typed`). -/
theorem WF.checkDescends {env : VEnv} (henv : env.WF) (U : Nat) :
    @CheckDescends (henv.params U) := by
  letI := henv.params U
  intro p r ρ Γ Γ' e T m1 m2 hp W hΓ hm he hchk
  rcases hp with hd | hq | hi
  · cases hd
    trivial
  · cases hq
    simp only [quotPatternCheck, Pattern.Check.OK] at hchk
    exact quot_check_of_typed henv hΓ ‹QuotRegistered env› hm he hchk.1
  · cases hi with | intro _ _ =>
    unfold InductiveSignature.RecursorData.guard
    unfold InductiveSignature.RecursorData.guard at hchk
    split <;> simp_all [Pattern.Check.OK]

end Lean4Lean.VEnv.Strengthening
