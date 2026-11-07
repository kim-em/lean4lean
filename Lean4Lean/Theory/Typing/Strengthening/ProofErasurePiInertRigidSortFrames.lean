import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWrapperElimination
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Exact administrative frames around rigid sort-valued constants

Beta return alone forgets which lambda is compared at an application node.
This invariant retains every live constant or identity wrapper, together with
ordinary sort typing in its actual scope. Discarded arguments and annotations
remain arbitrary. No comparison transport or general carrier conversion is
assumed by the computation theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- A rigid sort-valued head behind constant and identity beta wrappers.
The constant body may mention its binder in discarded positions. Each live
payload retains an actual universe assignment in its own raw context. -/
inductive RigidSortFrames (c : Name) : List ProofShape → ProofShape → Prop where
  | const : ControlTyping Δ (.const c ls) (.sort u) → RigidSortFrames c Δ (.const c ls)
  | constant : ControlTyping Δ (.app (.lam A b) x) (.sort u) →
      RigidSortFrames c (A :: Δ) b → RigidSortFrames c Δ (.app (.lam A b) x)
  | identity : ControlTyping Δ (.app (.lam A (.bvar 0)) x) (.sort u) →
      RigidSortFrames c Δ x → RigidSortFrames c Δ (.app (.lam A (.bvar 0)) x)

/-- Every retained root is an actual type, independently of its wrappers. -/
theorem RigidSortFrames.typing (H : RigidSortFrames c Δ e) :
    ∃ u, ControlTyping Δ e (.sort u) := by
  cases H <;> exact ⟨_, by assumption⟩

/-- Typed substitution transports the complete frame structure, including
its node typings; it requires no substitution theorem for guarded computation. -/
theorem RigidSortFrames.subst (H : RigidSortFrames c Δ e)
    (W : ContextSubstitution Δ Δ' τ) : RigidSortFrames c Δ' (e.subst τ) := by
  induction H generalizing Δ' τ with
  | const HT => exact .const (HT.subst W)
  | constant HT _ ih => exact .constant (HT.subst W) (ih W.cons)
  | identity HT _ ih => exact .identity (HT.subst W) (ih W)

/-- Changing only the interpreted context preserves the exact frame syntax. -/
theorem RigidSortFrames.context (H : RigidSortFrames c Δ e)
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) : RigidSortFrames c Δ' e := by
  simpa only [ProofShape.subst_id] using H.subst W

/-- A fresh typed binder lifts all retained frames. -/
theorem RigidSortFrames.lift (H : RigidSortFrames c Δ e) (SD : DomainSort Δ A u) :
    RigidSortFrames c (A :: Δ) (e.liftN 1) := by
  obtain ⟨v, HT⟩ := H.typing
  have HS := H.subst (HT.weak_interpretation SD)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ HS

/-- Every frame tree beta-returns to its designated family. This forgetful
readout uses neither soundness nor confluence of any guarded relation. -/
theorem RigidSortFrames.beta_return (H : RigidSortFrames c Δ e) :
    ∃ ls, BetaRed e (.const c ls) := by
  induction H with
  | const => exact ⟨_, .refl⟩
  | constant _ _ ih =>
    obtain ⟨ls, RB⟩ := ih
    exact ⟨ls, (BetaRed.app (.lam .refl RB) .refl).trans .beta⟩
  | identity _ _ ih =>
    obtain ⟨ls, RX⟩ := ih
    refine ⟨ls, ProofShape.BetaRed.trans .beta ?_⟩
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons] using RX

/-- A primitive at a rigid type constant can only change universes or add
one of the two administrative beta wrappers. Actual sort typing rules out
native function and structure eta at this root. -/
theorem pi_inert_rigid_sort_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : ControlTyping Δ (.const c ls) (.sort u))
    (R : PiInertStage D n Δ (.const c ls) out) :
    (∃ ls', out = .const c ls') ∨ out = constantExpansion (.const c ls) ∨
      ∃ A, out = .app (.lam A (.bvar 0)) (.const c ls) := by
  have HR := R.1
  clear R
  induction n with
  | zero =>
    rcases HR with (HR | HR) | HR
    · exact (erased_iota_primitive_no_rigid hc hD HR rfl).elim
    · cases HR with
      | const => exact .inl ⟨_, rfl⟩
    · cases HR; exact .inr (.inl rfl)
  | succ n ih =>
    rcases HR with HR | HR | HR | HR | HR | HR
    · exact ih HR
    · have hh : (ProofShape.const c ls).constHead = some c := rfl
      generalize EE : ProofShape.const c ls = source at HR hh
      cases HR.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact (V.not_rigid (hn ▸ hc)).elim
    · cases HR
    · cases HR; exact .inr (.inr ⟨_, rfl⟩)
    · exact (HT.no_eta_sort (erased_static_structure_eta_expansion_stage_descent heq hs n) HR).elim
    · exact (HT.no_masked_structure (erased_static_structure_eta_expansion_stage_descent heq hs n) HR).elim

private theorem frame_binder_change
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : RigidSortFrames c (A :: Δ) b) (RA : ScopedCompute Step Δ A A') :
    RigidSortFrames c (A' :: Δ) b := by
  obtain ⟨u, Γ, f, hΓ, EΓ, ht, Ee⟩ := H.typing
  cases Γ with
  | nil => cases EΓ
  | cons C Γ =>
    obtain ⟨hΓ, v, hC⟩ := hΓ
    obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨C', HC, EC'⟩ := proofErase_scoped_compute_realize hstep hΓ hC EΓ EC RA
    apply H.context
    have W : ContextSubstitution (proofEraseCtx (C :: Γ)) (proofEraseCtx (C' :: Γ))
        ProofShape.Subst.id := ContextSubstitution.of_defeqCtx hΓ (IsDefEqCtx.succ .zero HC)
    intro Γ₀ hΓ₀ EΓ₀
    simpa only [proofEraseCtx, EC, EC', EΓ] using
      W hΓ₀ (by simpa only [proofEraseCtx, EC, EΓ] using EΓ₀)

/-- Compatible Pi-inert computation preserves the exact live wrapper tree.
The auxiliary lambda clause retains its body in the final annotation context;
ordinary typed context conversion transports the frame data at that boundary. -/
theorem RigidSortFrames.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R : ScopedCompute (PiInertStage D n) Δ e out)
    (H : RigidSortFrames c Δ e) : RigidSortFrames c Δ out := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht HR.1
  have main : ∀ {Δ e out}, ScopedCompute (PiInertStage D n) Δ e out →
      (RigidSortFrames c Δ e → RigidSortFrames c Δ out) ∧
      (∀ A b, e = .lam A b → RigidSortFrames c (A :: Δ) b →
        ∃ A' b', out = .lam A' b' ∧ RigidSortFrames c (A' :: Δ) b') := by
    intro Δ e out R
    induction R using ScopedCompute.rootBeta_induction with
    | refl => exact ⟨fun H => H, fun A b E H => ⟨A, b, E, H⟩⟩
    | base HR =>
      constructor
      · intro H
        cases H with
        | const HT =>
          have HT' := HT.compute hd (.base HR)
          rcases pi_inert_rigid_sort_root heq hs hc hD HT HR with ⟨ls', rfl⟩ | rfl | ⟨A, rfl⟩
          · exact .const HT'
          · exact .constant HT' ((RigidSortFrames.const HT).lift HT.constant_frame.2)
          · exact .identity HT' (.const HT)
        | constant | identity => exact (pi_inert_stage_no_lam_app HR).elim
      · intro A b E H
        exact (pi_inert_stage_no_lam (E ▸ HR)).elim
    | trans R₁ R₂ ih₁ ih₂ =>
      constructor
      · exact fun H => ih₂.1 (ih₁.1 H)
      · intro A b E H
        obtain ⟨A', b', E', H'⟩ := ih₁.2 A b E H
        exact ih₂.2 A' b' E' H'
    | app RF RX ihf ihx =>
      constructor
      · intro H
        cases H with
        | constant HT HB =>
          obtain ⟨A', b', rfl, HB'⟩ := ihf.2 _ _ rfl HB
          exact .constant (HT.compute hd (.app RF RX)) HB'
        | identity HT HX =>
          obtain ⟨A', rfl, _⟩ := RF.pi_inert_identity_lam
          exact .identity (HT.compute hd (.app RF RX)) (ihx.1 HX)
      · intro A b E; cases E
    | lam RA RB ihA ihB =>
      constructor
      · intro H; cases H
      · intro A b E H
        cases E
        exact ⟨_, _, rfl, frame_binder_change hd (ihB.1 H) RA⟩
    | beta =>
      constructor
      · intro H
        cases H with
        | constant HT HB =>
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
            HB.subst HT.beta_interpretation
        | identity HT HX => simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
            ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons] using HX
      · intro A b E; cases E
    | proj | forallE =>
      constructor
      · intro H; cases H
      · intro A b E; cases E
  exact (main R).1 H

/-- Every Pi-inert continuation of an actual rigid sort-valued constant has
only constant/identity administrative frames at its live head. The theorem
retains a syntactic tree, rather than only existence of a beta return. -/
theorem pi_inert_rigid_sort_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const c ls) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ (.const c ls)) out) : RigidSortFrames c (proofEraseCtx Γ) out := by
  have E : proofErase Γ (.const c ls) = .const c ls := if_neg (not_isProof_of_sort hΓ hS)
  rw [E] at R
  exact (RigidSortFrames.const ⟨Γ, _, hΓ, rfl, hS, E⟩).compute heq hs hc hD R

end Lean4Lean.VEnv.Strengthening
