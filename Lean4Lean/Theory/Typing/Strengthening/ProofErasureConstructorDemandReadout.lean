import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandStages

/-! # Operational readout of joint constructor and native-type demands

Unit values, record values, and record-family types keep their selected unit
parameter. Higher type keys impose no operational readout restriction, but
cannot become function keys when substituted into a control program.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- Operational demands distinguish unit terms, constructor terms, and their
native family types. Other type keys only constrain annotations in the observer. -/
def Realizes (uc ctor family : Name) (i : Nat) (e : ProofShape) : Key → Prop
  | .unit => ∃ a, (a = .bvar i ∨ a = .const uc []) ∧ BetaRed e a
  | .record => ∃ a, (a = .app (.const ctor []) (.bvar i) ∨ a = .app (.const ctor []) (.const uc [])) ∧ BetaRed e a
  | .fn _ keys result => ∀ a, (∀ key ∈ keys, Realizes uc ctor family i a key) → Realizes uc ctor family i (.app e a) result
  | .type .record => ∃ a, (a = .app (.const family []) (.bvar i) ∨ a = .app (.const family []) (.const uc [])) ∧ BetaRed e a
  | .type _ => True
termination_by key => sizeOf key

/-- Beta predecessors retain all operational demands, including higher-order
function demands whose input lists contain type keys. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes uc ctor family i e' key) :
    Realizes uc ctor family i e key := by
  cases key with
  | unit | record =>
    simp only [Realizes] at H ⊢
    obtain ⟨a, HA, HB⟩ := H
    exact ⟨a, HA, R.trans HB⟩
  | fn A keys result =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
  | type key =>
    cases key with
    | unit | type | fn => simp only [Realizes]
    | record =>
      simp only [Realizes] at H ⊢
      obtain ⟨a, HA, HB⟩ := H
      exact ⟨a, HA, R.trans HB⟩
termination_by sizeOf key

/-- Every joint observation has the operational interpretation under any raw
substitution supplying its free demands. Annotation certificates do not provide
unjustified value leaves. -/
theorem Obs.realizes (H : Obs unit record uc ctor family Δ S e key)
    (hσ : ∀ j key, S j key → Realizes uc ctor family i (σ j) key) :
    Realizes uc ctor family i (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [ProofShape.subst, Realizes]; exact ⟨_, Or.inr rfl, .refl⟩
  | record_ctor | family =>
    simp only [ProofShape.subst, Realizes]
    intro a ha
    have HA := ha .unit (by simp)
    simp only [Realizes] at HA
    obtain ⟨a', HA, HB⟩ := HA
    rcases HA with rfl | rfl
    · exact ⟨_, Or.inl rfl, .app .refl HB⟩
    · exact ⟨_, Or.inr rfl, .app .refl HB⟩
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
      | succ j => simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

/-- The ambient program demands just its selected unit variable. -/
def UnitSets (i : Nat) : Sets := fun j key => j = i ∧ key = .unit

/-- Closing the operational substitution leaves the raw program unchanged. -/
theorem Obs.readout (H : Obs unit record uc ctor family Δ (UnitSets i) e key) :
    Realizes uc ctor family i e key := by
  have HR := H.realizes (σ := Subst.id) (by
    rintro j key ⟨rfl, rfl⟩
    simp only [Realizes]
    exact ⟨_, Or.inl rfl, .refl⟩)
  simpa only [ProofShape.subst_id] using HR

/-- A demanded unit has a beta path to its original variable or constructor. -/
theorem Obs.unit_readout (H : Obs unit record uc ctor family Δ (UnitSets i) e .unit) :
    BetaRed e (.bvar i) ∨ BetaRed e (.const uc []) := by
  have HR := H.readout
  simp only [Realizes] at HR
  obtain ⟨a, rfl | rfl, HB⟩ := HR
  · exact .inl HB
  · exact .inr HB

/-- A demanded record has a beta path to the constructor at one of its two
tracked unit leaves. Full computation preservation may be applied beforehand. -/
theorem Obs.record_readout (H : Obs unit record uc ctor family Δ (UnitSets i) e .record) :
    BetaRed e (.app (.const ctor []) (.bvar i)) ∨ BetaRed e (.app (.const ctor []) (.const uc [])) := by
  have HR := H.readout
  simp only [Realizes] at HR
  obtain ⟨a, rfl | rfl, HB⟩ := HR
  · exact .inl HB
  · exact .inr HB

/-- A demanded native record type retains the same two parameter leaves. -/
theorem Obs.family_readout (H : Obs unit record uc ctor family Δ (UnitSets i) e (.type .record)) :
    BetaRed e (.app (.const family []) (.bvar i)) ∨ BetaRed e (.app (.const family []) (.const uc [])) := by
  have HR := H.readout
  simp only [Realizes] at HR
  obtain ⟨a, rfl | rfl, HB⟩ := HR
  · exact .inl HB
  · exact .inr HB

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
