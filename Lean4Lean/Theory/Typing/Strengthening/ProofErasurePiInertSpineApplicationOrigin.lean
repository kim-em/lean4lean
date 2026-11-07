import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTerminalDepth

/-! # Original arguments or a whole control wrapper at a stable spine

A minimum primitive-count path excludes a constant expansion that is later
consumed. A surviving expansion either lies below an original final argument,
or wraps the whole original spine. The latter retains a typed universe control
argument and a path from the original spine to the lower payload.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
variable [Params] {D : Definitions}

omit [Params] in
private theorem forall₂_snoc_right (H : List.Forall₂ R source (pre ++ [last])) :
    ∃ pre₀ last₀, source = pre₀ ++ [last₀] ∧ List.Forall₂ R pre₀ pre ∧ R last₀ last := by
  induction pre generalizing source with
  | nil =>
    cases H with
    | cons HR HS => cases HS; exact ⟨[], _, rfl, .nil, HR⟩
  | cons a pre ih =>
    cases H with
    | cons HR HS =>
      obtain ⟨pre₀, last₀, rfl, HP, HL⟩ := ih HS
      exact ⟨_ :: pre₀, last₀, rfl, .cons HR HP, HL⟩

/-- An application reached from a typed core-stable empty-level constant
spine either retains the original last argument, with separate function and
argument paths, or is a whole-spine constant wrapper. In the latter case its
argument is sort-typed and its lower payload is reachable from the original
spine. No constructor-field comparison or forward checker closure is assumed. -/
theorem pi_inert_zero_spine_application_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c []) args))
    (R : ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) args) (.app f x)) :
    (∃ pre a, args = pre ++ [a] ∧
      ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) pre) f ∧
      ScopedCompute (PiInertStage D 0) Δ a x) ∨
    (∃ A payload, f = .lam A (payload.liftN 1) ∧
      ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) args) payload ∧
      ControlTyping Δ x (.sort (.succ .zero))) := by
  obtain ⟨cost, RC, hmin⟩ := R.minimal_count
  rcases RC.const_spine_or_cut @hroot with ⟨ls', args', EO, HL, HA⟩ |
      ⟨ls', pre, pending, target, cp, ct, HC, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    obtain ⟨args₀, Eargs, Ef⟩ := const_spine_app EO.symm
    rw [Eargs] at HA
    obtain ⟨pre₀, a, rfl, HP, HX⟩ := forall₂_snoc_right HA
    exact .inl ⟨pre₀, a, rfl, Ef ▸ (ScopedCompute.refl.mkApps HP), HX⟩
  cases HL
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have HTP := RP.forget.spine_cut_source_typed @hd HT
  rcases HR.1 with HR | HE
  · exact (HN HR).elim
  cases HE with
  | intro hn =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTP
    have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
      .sort (by trivial)
    have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
      if_neg (not_isProof_of_sort hΓ hA)
    change ScopedComputeCount (PiInertStage D 0) ct Δ
      (ProofShape.mkApps (.lam (.sort (.succ .zero))
        ((ProofShape.mkApps (.const c []) pre).liftN 1)) (.sort .zero :: pending)) (.app f x) at RT
    rcases RT.pi_inert_lambda_spine_or_beta with
      ⟨rawA, rawb, args', cf, ca, hc, EO, RF, RX⟩ |
      ⟨rawA, rawb, x', xs', cf, ca, tail, hc, RF, RX, Rtail⟩
    · obtain ⟨A', e', cb, hcb, _, _, EF, RE⟩ :=
        pi_inert_constant_lambda_count_readout heq hs hΓ hA ht EΓ
          (by simpa only [EA, Ee] using RF)
      cases RX with
      | @cons cx _ x' cr _ pending' RX0 RXP =>
        have RE' : ScopedCompute (PiInertStage D 0) Δ
            (ProofShape.mkApps (.const c []) pre) (proofErase Γ e') := by
          simpa only [EΓ, Ee] using RE.forget
        rw [EF] at EO
        cases pending using List.snoc_induction with
        | nil =>
          cases RXP
          change ProofShape.app f x = ProofShape.app (.lam (proofErase Γ A') ((proofErase Γ e').liftN 1)) x' at EO
          obtain ⟨rfl, rfl⟩ := ProofShape.app.inj EO
          have HA' : List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) args pre := by
            simpa only [List.append_nil] using HA
          have HS : ControlTyping Δ (.sort .zero) (.sort (.succ .zero)) := by
            have htS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
            exact ⟨Γ, _, hΓ, EΓ, htS, if_neg (not_isProof_of_sort hΓ htS)⟩
          exact .inr ⟨_, _, rfl, (ScopedCompute.refl.mkApps HA').trans RE', HS.compute @hd RX0.forget⟩
        | snoc pending last _ =>
          obtain ⟨pending'', last', cp', cx', rfl, _, RP', RX'⟩ := RXP.snoc_inv
          rw [← List.cons_append, ProofShape.mkApps_snoc] at EO
          obtain ⟨rfl, rfl⟩ := ProofShape.app.inj EO
          have HA' : List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) args ((pre ++ pending) ++ [last]) := by
            simpa only [List.append_assoc] using HA
          obtain ⟨original, a, rfl, HP, HX⟩ := forall₂_snoc_right HA'
          have HF₀ : ScopedCompute (PiInertStage D 0) Δ
              (ProofShape.mkApps (.const c []) original)
              (ProofShape.mkApps (constantExpansion (ProofShape.mkApps (.const c []) pre)) pending) := by
            apply (ScopedCompute.refl.mkApps HP).trans
            rw [ProofShape.mkApps_append]
            exact (ScopedCompute.base HR).mkApps (.rfl (fun _ _ => .refl))
          have HF₁ := RF.forget.mkApps (ScopedArgumentsCount.cons RX0 RP').forget
          rw [EF] at HF₁
          exact .inl ⟨original, a, rfl, HF₀.trans HF₁, HX.trans RX'.forget⟩
    · obtain ⟨A', e', cb, hcb, _, _, EF, RE⟩ :=
        pi_inert_constant_lambda_count_readout heq hs hΓ hA ht EΓ
          (by simpa only [EA, Ee] using RF)
      cases EF
      cases RX with
      | cons _ RXP =>
        have RE' : ScopedComputeCount (PiInertStage D 0) cb Δ
            (ProofShape.mkApps (.const c []) pre) (proofErase Γ e') := by
          simpa only [EΓ, Ee] using RE
        have RB := RE'.mkApps RXP
        rw [← ProofShape.mkApps_append] at RB
        have Rtail' : ScopedComputeCount (PiInertStage D 0) tail Δ
            (ProofShape.mkApps (proofErase Γ e') xs') (.app f x) := by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
            ProofShape.lift_subst_cons, ProofShape.subst_id] using Rtail
        have HM := hmin _ (RP.trans (RB.trans Rtail'))
        omega

/-- Stable-spine computation cannot end at a bare lambda, variable, sort,
projection or Pi. A bare constant endpoint is exactly the original empty
spine; every other possible endpoint is an application. -/
theorem pi_inert_zero_spine_head_shape
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c []) args))
    (R : ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) args) out) :
    (args = [] ∧ out = .const c []) ∨ ∃ f x, out = .app f x := by
  obtain ⟨ls', args', HD, HL, HA⟩ := pi_inert_zero_stable_spine_frames heq hs @hroot HT R
  cases HL
  cases out with
  | app f x => exact .inr ⟨f, x, rfl⟩
  | lam A b =>
    obtain ⟨A', b', EE, _, _⟩ := HD.reduce.lam_inv
    have EC := congrArg ProofShape.constHead EE
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at EC
    cases EC
  | proof | bvar | sort | const | proj | forallE =>
    have EE := HD.eq_of_nonlambda (by
      intro A b pending E
      cases pending using List.snoc_induction with
      | nil => cases E
      | snoc pending x _ => rw [ProofShape.mkApps_snoc] at E; cases E)
    cases args' using List.snoc_induction with
    | nil => cases EE <;> cases HA <;> exact .inl ⟨rfl, rfl⟩
    | snoc args' x _ => rw [ProofShape.mkApps_snoc] at EE; cases EE

end Lean4Lean.VEnv.Strengthening
