import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalTyping
import Lean4Lean.Theory.Typing.Confluence.JoinTelescope

/-! # Computational typing along declared telescopes

Structural application certificates retain chains between the declared result
and actual assignment. Pi injectivity uses explicit type-fork joining; no
ordinary uniqueness equation is promoted to a computation chain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => TypedComputationTypeEq D Γ e1 e2

theorem HasTypeC.mkApps_head (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f T}, HasTypeC D Γ (VExpr.mkApps f args) T → ∃ T', HasTypeC D Γ f T'
  | [], _, _, H => ⟨_, H⟩
  | a :: as, f, _, H =>
    let ⟨_, H'⟩ := HasTypeC.mkApps_head hΓ (f := .app f a) (args := as) H
    let ⟨_, _, hf, _⟩ := H'.app_inv hΓ
    ⟨_, hf⟩

/-- One step of a telescope: a computational comparison of Π-types instantiated at a typed argument. -/
theorem TypedComputationTypeEq.forallE_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .forallE X Y ≫≪ .forallE A B) (ha : Γ ⊢ a : A) :
    Γ ⊢ a : X ∧ Γ ⊢ Y.inst a ≫≪ B.inst a := by
  obtain ⟨hX, hY⟩ := H.forallE_inv heq hs HF hΓ
  have ha' : Γ ⊢ a : X := ha.defeqU_r henv hΓ hX.defeq.symm
  have hXT : env.IsType univs Γ X := ⟨hX.choose, hX.choose_spec.defeq.hasType.1⟩
  exact ⟨ha', hY.inst heq hs hΓ hXT ha'⟩

/-- Computational conversions along an application spine compare its actual
assignment with the instantiated body of the declared telescope. -/
theorem HasTypeC.mkApps_wrapForalls
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {args f doms body}, args.length = doms.length →
      Γ ⊢ f : VExpr.wrapForalls doms body →
      (∀ T', HasTypeC D Γ f T' → Γ ⊢ VExpr.wrapForalls doms body ≫≪ T') →
      ∀ T', HasTypeC D Γ (VExpr.mkApps f args) T' → Γ ⊢ body.instOuter args ≫≪ T' := by
  intro args
  induction args with
  | nil =>
    intro f doms body hlen _ hcond T' hJ
    cases doms with
    | nil => exact hcond T' hJ
    | cons => simp at hlen
  | cons a as ih =>
    intro f doms body hlen hf hcond T' hJ
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨_, hJa⟩ := HasTypeC.mkApps_head hΓ (f := .app f a) (args := as) hJ
      obtain ⟨A, B, hJf, hJa', -⟩ := hJa.app_inv hΓ
      obtain ⟨had, -⟩ := (hcond _ hJf).forallE_inst heq hs HF hΓ hJa'.hasType
      have hfa : Γ ⊢ .app f a : (VExpr.wrapForalls ds body).inst a := HasType.app hf had
      rw [VExpr.wrapForalls_inst] at hfa
      have := ih (f := .app f a) (by simpa using hlen) hfa ?_ T' hJ
      · simpa [hlen] using this
      · intro T'' hJ''
        obtain ⟨A', B', hJf', hJa'', hB⟩ := hJ''.app_inv hΓ
        have ⟨_, hY⟩ := (hcond _ hJf').forallE_inst heq hs HF hΓ hJa''.hasType
        rw [← VExpr.wrapForalls_inst]
        exact hY.trans hΓ hB

/-- The actual major certificate retains a computational comparison with the
instantiated declared major domain of a recursor application. -/
theorem HasTypeC.major_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants rn = some ⟨u, VExpr.wrapForalls pre (.forallE dm br)⟩)
    (hlen : recArgs.length = pre.length)
    (H : HasTypeC D Γ (.app (VExpr.mkApps (.const rn L) recArgs) M) T) :
    ∃ X, HasTypeC D Γ M X ∧ Γ ⊢ (dm.instL L).instOuter recArgs ≫≪ X := by
  obtain ⟨X, Y, hJf, hJM, -⟩ := H.app_inv hΓ
  obtain ⟨_, hJc⟩ := HasTypeC.mkApps_head hΓ hJf
  obtain ⟨ci, hci, -⟩ := hJc.const_inv hΓ
  rw [hc] at hci; cases hci
  obtain ⟨_, hw, hl⟩ := hJc.hasType.const_inv henv.orderedStrong hΓ
  rw [hc] at hw; cases hw
  have hct : Γ ⊢ .const rn L : VExpr.wrapForalls (pre.map (·.instL L))
      (.forallE (dm.instL L) (br.instL L)) := by
    have := HasType.const (Γ := Γ) hc hl.1 hl.2
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using this
  have hj := HasTypeC.mkApps_wrapForalls heq hs HF hΓ (by simpa using hlen) hct (fun T' hJ' => by
    obtain ⟨ci, hci, hj⟩ := hJ'.const_inv hΓ
    rw [hc] at hci; cases hci
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using hj) _ hJf
  obtain ⟨B', hB'⟩ := VExpr.instOuter_forallE (dm.instL L) (br.instL L) recArgs
  rw [hB'] at hj
  exact ⟨X, hJM, (hj.forallE_inv heq hs HF hΓ).1⟩

/-- A saturated constant spine retains a computational comparison with its
instantiated declared result type. -/
theorem HasTypeC.const_spine_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants cn = some ⟨u, VExpr.wrapForalls Ds Rs⟩)
    (hlen : B.length = Ds.length)
    (H : HasTypeC D Γ (VExpr.mkApps (.const cn cl) B) X) :
    Γ ⊢ (Rs.instL cl).instOuter B ≫≪ X := by
  obtain ⟨_, hJc⟩ := HasTypeC.mkApps_head hΓ H
  obtain ⟨_, hw, hl⟩ := hJc.hasType.const_inv henv.orderedStrong hΓ
  rw [hc] at hw; cases hw
  have hct : Γ ⊢ .const cn cl : VExpr.wrapForalls (Ds.map (·.instL cl)) (Rs.instL cl) := by
    have := HasType.const (Γ := Γ) hc hl.1 hl.2
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using this
  exact HasTypeC.mkApps_wrapForalls heq hs HF hΓ (by simpa using hlen) hct (fun T' hJ' => by
    obtain ⟨ci, hci, hj⟩ := hJ'.const_inv hΓ
    rw [hc] at hci; cases hci
    simpa [VExpr.instL_wrapForalls, VExpr.instL] using hj) _ H

end Lean4Lean.VEnv.Strengthening
