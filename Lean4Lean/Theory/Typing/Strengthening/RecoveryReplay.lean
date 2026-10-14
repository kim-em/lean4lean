import Lean4Lean.Theory.Typing.Strengthening.RecoveryExistence

/-! # Type recovery needs only sound replay for ambient typing

Scoped descent is a stronger property than the ambient soundness needed to
replay a recovery certificate. Keeping these separate permits ordinary full
reduction to serve as a complete recovery base without assuming strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- A computation replays at every source typing in its own context. This does
not assert scope reflection or replay below a binder insertion. -/
def ComputeReplay (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ e out}, C Γ e out → OnCtx Γ (env.IsType univs) → env.SimAt univs Γ e out

/-- Every scoped computation has ambient replay. The converse is not assumed. -/
theorem ComputeDescent.replay (H : ComputeDescent C) : ComputeReplay C :=
  fun R hΓ => H.simAt R hΓ

/-- Ambient typing of a recovery certificate only uses replay of its type
computations. It needs no ability to remove binders from those computations. -/
theorem TypeRecoveryWith.hasType_of_replay (R : TypeRecoveryWith C Γ e T)
    (hc : ComputeReplay C) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ e) : env.HasType univs Γ e T := by
  induction R with
  | sort hu => exact .sort hu
  | const hc hw hl => exact .const hc hw hl
  | bvar h => exact .bvar h
  | lam R ih =>
    obtain ⟨⟨_, hA⟩, hb⟩ := ht.lam_inv henv hΓ
    exact .lam hA (ih ⟨hΓ, _, hA⟩ hb)
  | app R ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact application_at_recovered_pi hΓ ht (ih hΓ ⟨_, hf⟩)
  | forallE hA hB => exact .forallE hA hB
  | proj hi R hF ih =>
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    exact projection_at_recovered_family henv hΓ hi ⟨_, ht'⟩ (ih hΓ ⟨_, hm.hasType.2⟩) hF
  | convert R H ih =>
    have he := ih hΓ ht
    obtain ⟨_, hT⟩ := he.isType henv hΓ
    exact (hc H hΓ _ hT).defeq he

/-- Computational head exposure supplies the local synthesis clauses using
ambient replay alone. No strengthening property is used in this construction. -/
theorem RecoveryHeads.of_replay_exposure (hc : ComputeReplay C)
    (hPi : RecoveryPiExposure C) (hProj : RecoveryProjectionExposure C) :
    RecoveryHeads C where
  app hΓ ht R := by
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    have hf' := R.hasType_of_replay hc hΓ ⟨_, hf⟩
    obtain ⟨_, hT⟩ := hf'.isType henv hΓ
    obtain ⟨A', B', RT⟩ := hPi hΓ hT (hf'.uniqU henv hΓ hf)
    exact ⟨A', B', .convert R RT⟩
  proj hΓ ht R := by
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    have hm' := R.hasType_of_replay hc hΓ ⟨_, hm.hasType.2⟩
    obtain ⟨info, ls, args, F, hi, RT, hF⟩ := hProj hΓ ⟨_, ht'⟩ hm'
    exact ⟨info, ls, args, F, hi, .convert R RT, hF⟩

end Lean4Lean.VEnv.Strengthening
