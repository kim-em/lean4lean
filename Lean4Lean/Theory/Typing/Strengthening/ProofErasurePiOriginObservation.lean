import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure

/-! # Finite observations retaining a marked Pi payload

Payloads live in a fixed outer context. The depth counts temporary control
binders: every marked Pi is lifted past all of them. Substitutions can change
those binders freely while fixing the outer variables and payload histories.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.PiOriginObservation
open _root_.Lean4Lean
open PureObservation (Ob Sets)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- A substitution fixes the original context below its control-binder prefix. -/
def FixedTail (n m : Nat) (σ : Subst) : Prop :=
  ∀ i, σ (n + i) = .bvar (m + i)

/-- Entering one control binder preserves the original-variable agreement. -/
theorem FixedTail.lift (H : FixedTail n m σ) : FixedTail (n+1) (m+1) σ.lift := by
  intro i
  change σ.lift (n+1+i) = .bvar (m+1+i)
  rw [show n+1+i = (n+i)+1 by omega]
  change (σ (n+i)).liftN 1 = .bvar (m+1+i)
  rw [H i]
  simp only [ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte]
  congr 1
  omega

/-- Supplying a control argument leaves the original context fixed. -/
theorem FixedTail.cons (H : FixedTail n m σ) : FixedTail (n+1) m (σ.cons a) := by
  intro i
  simpa only [Nat.add_right_comm, Subst.cons] using H i

/-- Every original payload is transported exactly, without inspecting it. -/
theorem FixedTail.payload (H : FixedTail n m σ) (e : ProofShape) :
    (e.liftN n).subst σ = e.liftN m := by
  calc
    (e.liftN n).subst σ = e.subst (fun i => .bvar (m+i)) := by
      apply subst_liftN_agree
      intro i
      simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using H i
    _ = e.liftN m := by
      simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
        (subst_bvar_liftN (n := m) (k := 0) e)

/-- A marked Pi retains its lower payload certificate at every control depth. -/
inductive Obs (P : ProofShape → ProofShape → Prop) : Nat → Sets → ProofShape → Ob → Prop where
  | var : S i o → Obs P n S (.bvar i) o
  | payload : P A B → Obs P n S ((ProofShape.forallE A B).liftN n) .pi
  | app : Obs P n S f (.app keys o) → (∀ key ∈ keys, Obs P n S a key) → Obs P n S (.app f a) o
  | lam : Obs P (n+1) (Sets.cons (fun key => key ∈ keys) S) b o →
      Obs P n S (.lam A b) (.app keys o)

/-- Renaming may move the control variables but fixes every marked payload. -/
theorem Obs.rename (H : Obs P n S e o) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → ∃ j, σ i = .bvar j ∧ T j key) : Obs P m T (e.subst σ) o := by
  induction H generalizing m T σ with
  | var h => obtain ⟨j, E, hj⟩ := hσ _ _ h; simpa only [subst, E] using Obs.var hj
  | payload h => rw [HT.payload]; exact .payload h
  | app _ _ ihf iha => exact .app (ihf HT hσ) (fun key hk => iha key hk HT hσ)
  | @lam n keys S b o A _ ih =>
    apply Obs.lam
    apply ih HT.lift
    intro i key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i key hi
      exact ⟨j+1, by simp [Subst.lift, E, liftN, liftVar, Nat.add_comm], hj⟩

/-- Inserting a control binder lifts the payload and the observed syntax together. -/
theorem Obs.lift (H : Obs P n S e o) :
    Obs P (n+1) (Sets.cons Q S) (e.liftN 1) o := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.rename HT (T := Sets.cons Q S) (fun i key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Observed arguments may replace control variables without changing payloads. -/
theorem Obs.subst (H : Obs P n S e o) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Obs P m T (σ i) key) : Obs P m T (e.subst σ) o := by
  induction H generalizing m T σ with
  | var h => exact hσ _ _ h
  | payload h => rw [HT.payload]; exact .payload h
  | app _ _ ihf iha => exact .app (ihf HT hσ) (fun key hk => iha key hk HT hσ)
  | @lam n keys S b o A _ ih =>
    apply Obs.lam
    apply ih HT.lift
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i => exact (hσ i key hi).lift

/-- Application inversion retains exactly the finite argument demands. -/
theorem Obs.app_inv (H : Obs P n S (.app f a) o) :
    ∃ keys, Obs P n S f (.app keys o) ∧ ∀ key ∈ keys, Obs P n S a key := by
  cases H with
  | app hf ha => exact ⟨_, hf, ha⟩

/-- A lambda can only acquire a function demand through its body. -/
theorem Obs.lam_inv (H : Obs P n S (.lam A b) o) :
    ∃ keys result, o = .app keys result ∧ Obs P (n+1) (Sets.cons (fun key => key ∈ keys) S) b result := by
  cases H with
  | lam hb => exact ⟨_, _, rfl, hb⟩

/-- A literal Pi observation retains a lower payload and its exact lift. -/
theorem Obs.forallE_inv (H : Obs P n S (.forallE X Y) o) :
    o = .pi ∧ ∃ A B, P A B ∧ X = A.liftN n ∧ Y = B.liftN n 1 := by
  cases H with
  | payload h => exact ⟨rfl, _, _, h, rfl, rfl⟩

/-- Opaque primitive heads cannot consume a marked payload demand. -/
theorem Obs.not_primitiveHead (H : Obs P n S e o) : ¬ PrimitiveHead e := by
  induction H with
  | var | payload | lam => exact id
  | app _ _ ihf _ => exact ihf

/-- No observation is generated by a sort or the proof marker. -/
theorem Obs.not_sort (H : Obs P n S (.sort u) o) : False := by cases H

/-- Projection syntax carries no payload demand. -/
theorem Obs.not_proj (H : Obs P n S (.proj s i e) o) : False := by cases H

/-- Beta discharges a finite control-variable demand while leaving the marked
payload's original context untouched. -/
theorem Obs.beta_forward (H : Obs P n S (.app (.lam A b) a) o) : Obs P n S (b.inst a) o := by
  obtain ⟨keys, hf, ha⟩ := H.app_inv
  obtain ⟨keys', result, E, hb⟩ := hf.lam_inv
  cases E
  have HT : FixedTail n n Subst.id := by intro i; rfl
  have R := hb.subst (HT.cons (a := a)) (T := S) (fun i key hi => by
    cases i with
    | zero => exact ha key hi
    | succ i => exact .var hi)
  simpa only [inst_eq_subst, Subst.liftN, Subst.one] using R

/-- An unused control binder carries the same payload observation. -/
theorem Obs.constant_expansion (H : Obs P n S e o) :
    Obs P n S (.app (.lam A (e.liftN 1)) arg) o :=
  .app (.lam (H.lift (Q := fun key => key ∈ ([] : List Ob)))) (by simp)

/-- An identity control frame demands only the observation of its payload. -/
theorem Obs.identity_expansion (H : Obs P n S e o) :
    Obs P n S (.app (.lam A (.bvar 0)) e) o := by
  apply Obs.app (keys := [o])
  · exact .lam (.var (by simp [Sets.cons]))
  · intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact H

/-- Operational meaning retaining the selected lower payload certificate. -/
def Realizes (P : ProofShape → ProofShape → Prop) (n : Nat) (e : ProofShape) : Ob → Prop
  | .pi => ∃ A B, P A B ∧ BetaRed e ((ProofShape.forallE A B).liftN n)
  | .sort => False
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes P n a key) → Realizes P n (.app e a) o
termination_by o => sizeOf o

/-- Beta predecessors realize the same payload. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes P n e' o) : Realizes P n e o := by
  cases o with
  | pi =>
    simp only [Realizes] at H ⊢
    obtain ⟨A, B, HP, H⟩ := H
    exact ⟨A, B, HP, R.trans H⟩
  | sort => simp only [Realizes] at H
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Marked observations realize their unchanged payload histories after every
substitution that fixes original variables and supplies the control demands. -/
theorem Obs.realizes (H : Obs P n S e o) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Realizes P m (σ i) key) : Realizes P m (e.subst σ) o := by
  induction H generalizing m σ with
  | var h => exact hσ _ _ h
  | payload h => rw [HT.payload]; simp only [Realizes]; exact ⟨_, _, h, .refl⟩
  | app _ _ ihf iha =>
    have HF := ihf HT hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk HT hσ)
  | @lam n keys S b o A _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih HT.cons (fun i key hi => by
      cases i with
      | zero => exact ha key hi
      | succ i => exact hσ i key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [inst_eq_subst, Subst.liftN, subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons, lift_subst_cons, subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

/-- At depth zero an empty control valuation reads the exact lower marked Pi. -/
theorem Obs.readout (H : Obs P 0 (fun _ _ => False) e .pi) :
    ∃ A B, P A B ∧ BetaRed e (.forallE A B) := by
  have HT : FixedTail 0 0 Subst.id := by intro i; rfl
  have R := H.realizes HT (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes, liftN_zero] using R

end Lean4Lean.VEnv.Strengthening.ProofShape.PiOriginObservation
