import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalTelescope

/-! # Instantiating computationally equal dependent telescopes

The source application's typing supplies each argument domain. Computational
Pi injectivity and substitution propagate the comparison to the result bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => TypedComputationTypeEq D Γ e1 e2

/-- Two computationally equal telescopes of the same length have computationally equal bodies at arguments that a function
typed by the first telescope accepts. -/
theorem TypedComputationTypeEq.wrapForalls_instOuter
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms doms' body body'}, args.length = doms.length → doms'.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body → VExpr.WF env univs Γ (VExpr.mkApps f args) →
      Γ ⊢ VExpr.wrapForalls doms body ≫≪ VExpr.wrapForalls doms' body' →
      Γ ⊢ body.instOuter args ≫≪ body'.instOuter args := by
  intro args
  induction args with
  | nil =>
    intro f doms doms' body body' hlen hlen' _ _ H
    cases doms with
    | nil => cases doms' with
      | nil => exact H
      | cons => simp at hlen'
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms doms' body body' hlen hlen' hf hwf H
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
    cases doms' with
    | nil => simp at hlen'
    | cons d' ds' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hlen'
      have hfa : VExpr.WF env univs Γ (.app f a) :=
        VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app f a) (by simpa [VExpr.mkApps] using hwf)
      obtain ⟨A, B, hf', ha'⟩ := hfa.app_inv henv.orderedStrong hΓ
      have ⟨⟨_, hdA⟩, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
      have had : Γ ⊢ a : d := ha'.defeqU_r henv hΓ ⟨_, hdA.symm⟩
      obtain ⟨hdd, -⟩ := H.forallE_inv heq hs HF hΓ
      have had' : Γ ⊢ a : d' := had.defeqU_r henv hΓ hdd.defeq
      obtain ⟨-, hY⟩ := H.forallE_inst heq hs HF hΓ had'
      have hfa' : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      have hY' : Γ ⊢ (VExpr.wrapForalls ds body).inst a ≫≪ (VExpr.wrapForalls ds' body').inst a := hY
      rw [VExpr.wrapForalls_inst] at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.wrapForalls_inst] at hY'
      have := ih (f := .app f a) (by simpa using hlen) (by simpa [hlen] using hlen') hfa'
        (by simpa [VExpr.mkApps] using hwf) hY'
      simpa [hlen, hlen'] using this

end Lean4Lean.VEnv.Strengthening
