import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionExposure

/-! # Counted terminal projection results without an exposure assumption

A sorted projection may remain unevaluated at its endpoint. For endpoints
without a lambda head, administrative wrappers can still be removed, and a
selected-field tail can be moved into its constructor with its exact count.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
namespace ProofShape

private theorem scoped_selected_argument_count
    (HG : args[j]? = some field) (R : ScopedComputeCount Step cost Δ field out) :
    ScopedArgumentsCount Step Δ cost args (args.set j out) := by
  induction args generalizing j with
  | nil => simp at HG
  | cons a args ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero] at HG
      cases Option.some.inj HG
      simpa only [List.set_cons_zero, Nat.add_zero] using
        ScopedArgumentsCount.cons R (ScopedArgumentsCount.refl (args := args))
    | succ j =>
      simpa only [List.set_cons_succ, Nat.zero_add] using
        ScopedArgumentsCount.cons (ScopedComputeCount.beta (BetaRed.refl (e := a)))
          (ih (by simpa only [List.getElem?_cons_succ] using HG))

/-- Moving a selected field's computation into its constructor argument
preserves the exact count, stage and all other arguments. -/
theorem ScopedComputeCount.selected_argument
    (HG : args[j]? = some field) (R : ScopedComputeCount Step cost Δ field out) :
    ScopedComputeCount Step cost Δ (ProofShape.mkApps f args) (ProofShape.mkApps f (args.set j out)) := by
  simpa only [Nat.zero_add] using
    (ScopedComputeCount.beta (BetaRed.refl (e := f))).mkApps (scoped_selected_argument_count HG R)

end ProofShape
variable [Params] {D : Definitions}

/-- At a non-lambda endpoint, a sorted projection either retains its major
history or has an actual selection and field tail within budget. The endpoint
may itself be a projection; no non-projection exposure premise is used. -/
theorem pi_inert_sorted_projection_count_keep_or_select
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj s i m) out) :
    (∃ major before, before ≤ cost ∧ out = .proj s i major ∧
      ScopedComputeCount (PiInertStage D n) before Δ m major) ∨
    (∃ major field before after, before+1+after ≤ cost ∧
      ScopedComputeCount (PiInertStage D n) before Δ m major ∧
      Primitive D (.proj s i major) field ∧
      ScopedComputeCount (PiInertStage D n) after Δ field out) := by
  induction cost using Nat.strongRecOn generalizing m with
  | ind cost ih =>
    rcases R.projection_first_root with ⟨major, EO, RM⟩ |
      ⟨major, target, before, after, HC, RM, RP, RT⟩
    · exact .inl ⟨major, cost, by omega, EO, RM⟩
    have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
      fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
        hΓ hΓ' W ht R.1
    have HT' := HT.compute hd (.proj RM.forget)
    rcases static_structure_sorted_projection_root heq hs HT' RP.1 with RI | RC | ⟨k, _, RN⟩
    · exact .inr ⟨major, target, before, after, by omega, RM, RI, RT⟩
    all_goals
      have HTsource : TypedSource Δ (.proj s i major) := by
        obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT'
        exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
      have bypass : ∃ j, j ≤ after ∧ ScopedComputeCount (PiInertStage D n) j Δ (.proj s i major) out := by
        first
        | exact pi_inert_expansion_count_bypass_nonlambda heq hs HTsource
            (Recovery := PiInertStage D n) (.inl RC) RT hout
        | exact pi_inert_expansion_count_bypass_nonlambda heq hs HTsource (.inr RN) RT hout
      obtain ⟨j, hj, RJ⟩ := bypass
      rcases ih j (by omega) HT' RJ with ⟨last, cb, HB, EO, RL⟩ |
        ⟨last, field, cb, ca, HB, RL, RI, RF⟩
      · exact .inl ⟨last, before+cb, by omega, EO, RM.trans RL⟩
      · exact .inr ⟨last, field, before+cb, ca, by omega, RM.trans RL, RI, RF⟩

/-- The exact non-lambda endpoint is a retained projection or a terminal
selection of a computed major. The major count plus the terminal action's
zero/one cost does not exceed the original projection budget. -/
theorem pi_inert_sorted_projection_count_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj s i m) out) :
    ∃ major cm, ScopedComputeCount (PiInertStage D n) cm Δ m major ∧
      ((out = .proj s i major ∧ cm ≤ cost) ∨
       (Primitive D (.proj s i major) out ∧ cm+1 ≤ cost)) := by
  rcases pi_inert_sorted_projection_count_keep_or_select heq hs HT hout R with
    ⟨major, cm, hcm, EO, RM⟩ | ⟨major, field, before, after, HB, RM, RI, RF⟩
  · exact ⟨major, cm, RM, .inl ⟨EO, hcm⟩⟩
  · cases RI with
    | projIota hi hl hg =>
      have hj := (List.getElem?_eq_some_iff.1 hg).1
      refine ⟨_, before+after, RM.trans (RF.selected_argument hg), .inr ⟨?_, by omega⟩⟩
      exact .projIota hi (by simpa only [List.length_set] using hl) (by simp [hj])

end Lean4Lean.VEnv.Strengthening
