import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordStages

/-! # Beta readout with no parameter demands

Joint preservation retains enough operational information to expose the
constructor or family head. Its argument stays arbitrary. Consequently this
readout survives every raw substitution, independently of native guards.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- Value and family-type observations beta-expose their fixed heads. Function
keys consume only their listed inputs; all other type keys have trivial readout. -/
def Realizes (uc ctor family : Name) (e : ProofShape) : Key → Prop
  | .unit => BetaRed e (.const uc [])
  | .record => ∃ a, BetaRed e (.app (.const ctor []) a)
  | .fn _ keys result => ∀ a, (∀ key ∈ keys, Realizes uc ctor family a key) → Realizes uc ctor family (.app e a) result
  | .type .record => ∃ a, BetaRed e (.app (.const family []) a)
  | .type _ => True
termination_by key => sizeOf key

/-- Beta predecessors preserve every operational readout. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes uc ctor family e' key) :
    Realizes uc ctor family e key := by
  cases key with
  | unit =>
    simp only [Realizes] at H ⊢
    exact R.trans H
  | record =>
    simp only [Realizes] at H ⊢
    obtain ⟨a, HA⟩ := H; exact ⟨a, R.trans HA⟩
  | fn A keys result =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
  | type key =>
    cases key with
    | unit | type | fn => simp only [Realizes]
    | record =>
      simp only [Realizes] at H ⊢
      obtain ⟨a, HA⟩ := H; exact ⟨a, R.trans HA⟩
termination_by sizeOf key

/-- Raw substitution realizes the observer from its free demands. Constructor
and family leaves ignore their arguments completely. No target typing or
native certificate is used by this purely beta readout. -/
theorem Obs.realizes (H : Obs unit record parameter uc ctor family Ω S e key)
    (hσ : ∀ j key, S j key → Realizes uc ctor family (σ j) key) :
    Realizes uc ctor family (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [ProofShape.subst, Realizes]; exact .refl
  | record_ctor | family =>
    simp only [ProofShape.subst, Realizes]
    exact fun a _ => ⟨a, .refl⟩
  | unit_type | univ | family_type | pi => simp only [Realizes]
  | app _ _ _ ihf iha =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam Δ A b domain keys result S _ _ _ _ _ _ ihb =>
    simp only [Realizes]
    intro a ha
    have HB := ihb (σ := σ.cons a) (fun j key hj => by
      cases j with
      | zero => exact ha key hj
      | succ j => exact hσ j key hj)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext j
      cases j with
      | zero => rfl
      | succ j => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons,
          ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

/-- With no free demands, a native family observation exposes its family head
after any raw substitution. Its supplied argument remains arbitrary. -/
theorem Obs.family_head
    (H : Obs unit record parameter uc ctor family Δ (fun _ _ => False) e (.type .record)) :
    ∃ a, BetaRed (e.subst σ) (.app (.const family []) a) := by
  simpa only [Realizes] using H.realizes (σ := σ) (fun _ _ h => h.elim)

/-- The analogous readout exposes the value's registered constructor head. -/
theorem Obs.constructor_head
    (H : Obs unit record parameter uc ctor family Δ (fun _ _ => False) e .record) :
    ∃ a, BetaRed (e.subst σ) (.app (.const ctor []) a) := by
  simpa only [Realizes] using H.realizes (σ := σ) (fun _ _ h => h.elim)

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
