import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicEtaObservation

/-! # Function eta preserves a neutral family's opaque argument

A raw test substitutes the identity for a distinguished family variable. Its
argument observation then reads back the exact opaque variable by beta alone.
The test is an operational interpretation, not an object-language substitution.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicControl
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)

private theorem observation_subst (a : ProofShape) (τ : ProofShape.Subst) :
    (a.subst τ).toObservationExpr = a.toObservationExpr.subst (fun i => (τ i).toObservationExpr) := by
  have hl (τ : ProofShape.Subst) : (fun i => (τ.lift i).toObservationExpr) =
      VExpr.Subst.lift (fun i => (τ i).toObservationExpr) := by
    funext i
    cases i <;> simp only [ProofShape.Subst.lift, VExpr.Subst.lift,
      toObservationExpr, toObservationExpr_liftN]
  induction a generalizing τ <;> simp only [ProofShape.subst, toObservationExpr, VExpr.subst, *]

/-- The raw identity test replaces just the family variable. It is used only
to separate observations and need not preserve actual object-language typing. -/
def familyTest (f : Nat) : ProofShape.Subst :=
  fun j => if j = f then .lam (.sort .zero) (.bvar 0) else .bvar j

variable [Params] [Atom]

/-- A family application at a typed opaque variable preserves that argument's
exact observable identity through every function-eta/singleton stage. -/
theorem eta_union_family_argument_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort u)))
    (HX : ControlTyping Δ (.bvar i) .atom)
    (HA : ControlTyping Δ (.app (.bvar f) (.bvar i)) (.sort u)) (hif : i ≠ f)
    (R : ScopedCompute (ErasedEtaExpansionUnion D) Δ (.app (.bvar f) (.bvar i)) out) :
    ProofShape.BetaRed (out.subst (familyTest f)) (.bvar i) := by
  let S : Sets := fun j t o =>
    (j = f ∧ t = .arrow .atom (.sort u) ∧ o = .app [.pi] .pi) ∨
    (j = i ∧ t = .atom ∧ o = .pi)
  have HS : S.Typed Δ := by
    intro j t o H
    rcases H with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact HF
    · exact HX
  have H : Obs Δ S (.app (.bvar f) (.bvar i)) (.sort u) .pi := by
    apply Obs.app HA (keys := [.pi])
    · exact .var HF (.fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .atom)
        .sort) (.inl ⟨rfl, rfl, rfl⟩)
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact .var HX .atom (.inr ⟨rfl, rfl, rfl⟩)
  have HO := (H.eta_union heq hs R HS).forget
    (T := fun j o => (j = f ∧ o = .app [.pi] .pi) ∨ (j = i ∧ o = .pi))
    (fun _ _ _ h => h.elim (fun h => .inl ⟨h.1, h.2.2⟩) (fun h => .inr ⟨h.1, h.2.2⟩))
  have HR := NeutralObservation.Obs.realizes HO
    (σ := fun j => (familyTest f j).toObservationExpr) (target := .bvar i) (by
      intro j key H
      rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [NeutralObservation.Realizes]
        intro a ha
        have HB : VExpr.BetaRed (.app (.lam (.sort .zero) (.bvar 0)) a) a := by
          simpa [VExpr.inst, VExpr.instVar, VExpr.liftN, VExpr.liftN_zero] using
            (VExpr.BetaRed.beta (A := .sort .zero) (b := .bvar 0) (a := a))
        have HA : VExpr.BetaRed a (.bvar i) := by
          simpa only [NeutralObservation.Realizes] using ha .pi (by simp)
        simpa [familyTest, toObservationExpr, NeutralObservation.Realizes] using HB.trans HA
      · simp only [familyTest, if_neg hif, toObservationExpr, NeutralObservation.Realizes]
        exact .refl)
  apply beta_toObservationExpr_iff.1
  simpa only [observation_subst, toObservationExpr, NeutralObservation.Realizes] using HR

/-- Different opaque arguments of the same neutral family have no common
full-eta reduct. Their family and argument annotations may compute arbitrarily. -/
theorem eta_union_family_arguments_no_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ControlTyping Δ (.bvar f) (.arrow .atom (.sort u)))
    (HI : ControlTyping Δ (.bvar i) .atom) (HJ : ControlTyping Δ (.bvar j) .atom)
    (HA : ControlTyping Δ (.app (.bvar f) (.bvar i)) (.sort u))
    (HB : ControlTyping Δ (.app (.bvar f) (.bvar j)) (.sort u))
    (hif : i ≠ f) (hjf : j ≠ f) (hne : i ≠ j) :
    ¬ ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) Δ (.app (.bvar f) (.bvar i)) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion D) Δ (.app (.bvar f) (.bvar j)) shared := by
  rintro ⟨shared, RI, RJ⟩
  have RI := eta_union_family_argument_readout heq hs HF HI HA hif RI
  have RJ := eta_union_family_argument_readout heq hs HF HJ HB hjf RJ
  obtain ⟨out, HI', HJ'⟩ := RI.raw_confluent RJ
  have EI := HI'.fixed_of_normal (Step := fun _ _ => False) ⟨by simp, trivial⟩
  have EJ := HJ'.fixed_of_normal (Step := fun _ _ => False) ⟨by simp, trivial⟩
  exact hne (ProofShape.bvar.inj (EI.symm.trans EJ))

end Lean4Lean.VEnv.Strengthening.AtomicControl
