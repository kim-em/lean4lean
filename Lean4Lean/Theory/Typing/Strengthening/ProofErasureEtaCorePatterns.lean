import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCoreSpineCleanup

/-! # Registered pattern matching through sorted eta histories -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private const_spine_app from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- A constant-and-capture match has the corresponding literal constant spine. -/
theorem Matches.const_spine (H : Matches ((Pattern.const c).varN count) a ls caps) :
    ∃ args, a = mkApps (.const c ls) args := by
  induction count generalizing a with
  | zero => cases H; exact ⟨[], rfl⟩
  | succ count ih =>
    cases H with
    | var H =>
      obtain ⟨args, rfl⟩ := ih H
      exact ⟨args ++ [_], mkApps_snoc.symm⟩

/-- Pointwise related arguments transport a constant-spine match and all its
captures, keeping the head and universe list exact. -/
theorem Matches.varN_pair {R : ProofShape → ProofShape → Prop}
    (H : Matches ((Pattern.const c).varN count) (mkApps (.const c ls) args) ls caps)
    (HA : List.Forall₂ R args args') :
    ∃ caps', Matches ((Pattern.const c).varN count) (mkApps (.const c ls) args') ls caps' ∧
      ∀ i, R (caps i) (caps' i) := by
  induction count generalizing args args' with
  | zero =>
    generalize E : mkApps (.const c ls) args = source at H
    cases H
    rcases List.eq_nil_or_snoc args with rfl | ⟨_, _, rfl⟩
    · cases HA; exact ⟨nofun, .const, nofun⟩
    · rw [mkApps_snoc] at E; cases E
  | succ count ih =>
    generalize E : mkApps (.const c ls) args = source at H
    cases H with
    | var H =>
      obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
      obtain ⟨args₀', y, rfl, HA₀, HY⟩ := List.forall₂_snoc_left HA
      obtain ⟨caps', HM, HC⟩ := ih H HA₀
      refine ⟨fun i => i.elim y caps', ?_, ?_⟩
      · rw [mkApps_snoc]; exact .var HM
      · intro i; cases i with
        | none => exact HY
        | some i => exact HC i
/-- Paired heads and arguments form paired spines, including template RHSs. -/
theorem AmbientVariant.mkApps_pair (V : AmbientVariant Guard Atom n f g)
    (H : List.Forall₂ (AmbientVariant Guard Atom n) args args') :
    AmbientVariant Guard Atom n (mkApps f args) (mkApps g args') := by
  induction H generalizing f g with
  | nil => exact V
  | cons HX _ ih => exact ih (.app V HX)

end ProofShape

variable [Params] {D : Definitions}

/-- A registered pattern beta-exposes a matching target with paired captures,
unless the complete source/target pair is a single eta origin. Actual redex
typing excludes a function origin at its inspected constructor major; a whole
redex origin is retained for the separate exact full-core origin simulation. -/
theorem sorted_eta_core_pattern_cleanup (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (hp : Pat p r) (H : Matches p a ls caps)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    (∃ b' caps', ProofShape.BetaRed b b' ∧ Matches p b' ls caps' ∧
      ∀ i, AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n (caps i) (caps' i)) ∨
    LiftedOrigin (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  obtain ⟨original, HM, _⟩ := proofErase_pattern_match_inv (Ee ▸ H)
  cases sp with
  | defn c =>
    cases H
    cases V with
    | refl => exact .inl ⟨_, nofun, .refl, .const, nofun⟩
    | origin HO => exact .inr HO
  | iota rc mr cc kc =>
    cases H with
    | app HF HX =>
      cases V with
      | refl => exact .inl ⟨_, _, .refl, .app HF HX, fun _ => .refl⟩
      | origin HO => exact .inr HO
      | app VF VX =>
        obtain ⟨argsF, rfl⟩ := HF.const_spine
        obtain ⟨argsX, rfl⟩ := HX.const_spine
        obtain ⟨eF, eX, rfl, _, EF, EX⟩ := erase_app_inv Ee
        obtain ⟨_, _, hF, hX⟩ := ht.app_inv henv hΓ
        obtain ⟨argsX', RX, HXpair⟩ := sorted_eta_core_nonfunction_spine_cleanup hs hΓ₀ hA hf hn
          VX hΓ hX (fun _ _ => Params.major_not_pi hΓ hp HM ht) EX W
        obtain ⟨argsF', RF, HFpair⟩ := sorted_eta_core_applied_constant_spine_cleanup hs hΓ₀ hA hf hn
          VF VX hΓ ht Ee W
        have HFpair' := ((Lean4Lean.List.Forall₂.append_of_right (by rfl)).1 HFpair).1
        obtain ⟨capsF', HMF, HCF⟩ := HF.varN_pair HFpair'
        obtain ⟨capsX', HMX, HCX⟩ := HX.varN_pair HXpair
        refine .inl ⟨_, Sum.elim capsF' capsX', ?_, .app HMF HMX, ?_⟩
        · rw [ProofShape.mkApps_snoc] at RF
          exact RF.trans (.app .refl RX)
        · intro i; cases i with
          | inl i => exact HCF i
          | inr i => exact HCX i

end Lean4Lean.VEnv.Strengthening
