import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentControlObservation

/-! # Type payloads in dependent control programs

A marked type lives below temporary control binders. Ignored arguments may have
arbitrary dependent types or be proofs; demanded values carry finite profiles.
All frame typings use ordinary typing, without native argument certificates.
-/
namespace Lean4Lean.VEnv.Strengthening.DependentPayloadObservation
open _root_.Lean4Lean Params ProofShape
open DemandProfile (Profile Typing Demand Sets)
open PureObservation (Ob)
open PiOriginObservation (FixedTail)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A marked payload has arbitrary syntax and a universe profile.
It stays in the fixed outer context below every temporary control binder. -/
inductive Obs (P : ProofShape → Prop) :
    Nat → List ProofShape → Sets → ProofShape → Profile → Ob → Prop where
  | var : Typing Δ (.bvar i) t → Demand t o → S i t o → Obs P n Δ S (.bvar i) t o
  | payload : Typing Δ (a.liftN n) .sort →
      P a → Obs P n Δ S (a.liftN n) .sort .pi
  | app : Typing Δ (.app f a) B → Obs P n Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs P n Δ S a A key) → Obs P n Δ S (.app f a) B o
  | lam : Typing Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs P (n+1) (D :: Δ) (Sets.cons A keys S) b B o →
      Obs P n Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Forgetting the demand retains its ordinary source typing. -/
theorem Obs.typing (H : Obs P n Δ S e t o) : Typing Δ e t := by
  cases H <;> assumption

/-- Every derivable observation has a demand compatible with its control type. -/
theorem Obs.demand (H : Obs P n Δ S e t o) : Demand t o := by
  induction H with
  | var _ HD => exact HD
  | payload => exact .sort
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Typed renaming fixes the original argument and transports all control
node witnesses using its ordinary context interpretation. -/
theorem Obs.rename (H : Obs P n Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs P m Δ' T (e.subst σ) t o := by
  induction H generalizing m Δ' T σ with
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [subst, E] using
      (Obs.var (by simpa only [subst, E] using H.subst W) HD hj : Obs P m Δ' T (.bvar j) _ _)
  | payload H HP =>
    have H' := H.subst W
    rw [HT.payload] at H' ⊢
    exact .payload H' HP
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ D b A B keys n S o H HK _ ih =>
    apply Obs.lam (H.subst W) HK
    apply ih W.cons HT.lift
    intro i t key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i t key hi
      exact ⟨j+1, by simp [Subst.lift, E, liftN, liftVar, Nat.add_comm], hj⟩

/-- A well-typed fresh binder lifts the observation and its assigned type. -/
theorem Obs.lift (H : Obs P n Δ S e t o) (SD : DomainSort Δ D u) :
    Obs P (n+1) (D :: Δ) (Sets.cons A keys S) (e.liftN 1) t o := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.rename (H.typing.weak_interpretation SD) HT
    (T := Sets.cons A keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution discharges arbitrary finite control demands. The
image premise is needed only at demanded variables, at their retained type. -/
theorem Obs.subst (H : Obs P n Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → Demand t key →
      Obs P m Δ' T (σ i) t key) : Obs P m Δ' T (e.subst σ) t o := by
  induction H generalizing m Δ' T σ with
  | var H HD h => exact hσ _ _ _ h HD
  | payload H HP =>
    have H' := H.subst W
    rw [HT.payload] at H' ⊢
    exact .payload H' HP
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ D b A B keys n S o H HK _ ih =>
    have H' := H.subst W
    obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H
    obtain ⟨D₀, b₀, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _⟩ := hf.lam_inv henv hΓ
    have SD : DomainSort Δ D u := ⟨Γ, D₀, hΓ, EΓ, hD, ED⟩
    apply Obs.lam H' HK
    apply ih W.cons HT.lift
    intro i t key hi HD
    cases i with
    | zero =>
      obtain ⟨rfl, hk⟩ := hi
      exact .var (H'.lam_parts.2 HD.visible) HD ⟨rfl, hk⟩
    | succ i => exact (hσ i t key hi HD).lift (W.sort SD)

/-- Native eta preserves every typed marked demand. Sort payloads cannot
expand, while function demands pass through the retained fresh variable. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs P n Δ S e t o) (R : NativeEtaExpansion Step Δ e out) :
    Obs P n Δ S out t o := by
  cases H.demand with
  | sort => exact (H.typing.no_eta_sort hstep R).elim
  | @fn keys A B o HK HO =>
    obtain ⟨D, u, rfl, HT, HB, SD, HX⟩ := H.typing.eta_parts hstep R
    apply Obs.lam HT HK
    apply Obs.app HB (H.lift SD)
    intro key hk
    obtain ⟨E, HV⟩ := HX (HK key hk).visible
    rw [E]
    exact .var HV (HK key hk) ⟨rfl, hk⟩

/-- Identity context interpretation changes typing decorations while keeping
the raw observation, payload depth, and valuation exactly fixed. -/
theorem Obs.context (H : Obs P n Δ S e t o) (W : ContextSubstitution Δ Δ' Subst.id) :
    Obs P n Δ' S e t o := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  simpa only [subst_id] using H.rename W HT (fun i t key hi => ⟨i, rfl, hi⟩)

/-- The constant wrapper introduces no argument demand; its fixed domain
and whole function nevertheless retain their canonical control typings. -/
theorem Obs.constant_expansion (H : Obs P n Δ S e t o) :
    Obs P n Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame H.demand.visible
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro (H.typing.ne_proof H.demand.visible)))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands exactly its original typed payload. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs P n Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) :
    Obs P n Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep H.demand.visible RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact H.demand
      · exact .var (HF.lam_parts.2 H.demand.visible) H.demand ⟨rfl, by simp⟩
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact H

/-- An observed primitive head can only be a marked argument; control
variables, lambdas and function-position observations cannot supply that head. -/
theorem Obs.primitive_payload (H : Obs P n Δ S e t o) (HH : PrimitiveHead e) :
    ∃ a, e = a.liftN n ∧ t = .sort ∧ o = .pi ∧ P a := by
  induction H with
  | var | lam => cases HH
  | payload _ HP => exact ⟨_, rfl, rfl, rfl, HP⟩
  | app _ _ _ ihf _ =>
    obtain ⟨_, _, E, _⟩ := ihf HH
    cases E

/-- Every observation either marks the entire argument or has a control
head on which opaque primitives and level conversion cannot act. -/
theorem Obs.payload_or_headless (H : Obs P n Δ S e t o) :
    (∃ a, e = a.liftN n ∧ t = .sort ∧ o = .pi ∧ P a) ∨
      (¬ PrimitiveHead e ∧ ∀ u, e ≠ .sort u) := by
  cases H with
  | payload _ HP => exact .inl ⟨_, rfl, rfl, rfl, HP⟩
  | var | lam => exact .inr ⟨id, by intro u E; cases E⟩
  | app _ HF _ =>
    refine .inr ⟨?_, by intro u E; cases E⟩
    intro HH
    obtain ⟨_, _, E, _⟩ := HF.primitive_payload HH
    cases E

/-- A beta control frame supplies its demanded observations to the body.
Marked arguments are fixed below the temporary prefix by typed substitution. -/
theorem Obs.beta_frame
    (HT : Typing Δ (.app (.lam D b) a) B)
    (HF : Obs P n Δ S (.lam D b) (.arrow A B) (.app keys o))
    (HX : ∀ key ∈ keys, Obs P n Δ S a A key)
    (HS : S.Typed Δ) : Obs P n Δ S (b.inst a) B o := by
  generalize E : ProofShape.lam D b = f at HF
  cases HF with
  | var | app => cases E
  | lam HL HK HB =>
    cases E
    have HF : FixedTail n n Subst.id := by intro i; rfl
    have R := HB.subst HT.beta_interpretation HF.cons (T := S) (fun i t key hi HD => by
      cases i with
      | zero =>
        obtain ⟨rfl, hk⟩ := hi
        exact HX key hk
      | succ i => exact .var (HS i t key hi) HD hi)
    simpa only [inst_eq_subst, Subst.liftN, Subst.one] using R

/-- An atomic demand reads a lower payload; function demands describe finite
applications. Dependent profiles never use the neutral-result demand. -/
def Realizes (P : ProofShape → Prop) (n : Nat) (e : ProofShape) : Ob → Prop
  | .pi => ∃ a, P a ∧ BetaRed e (a.liftN n)
  | .sort => False
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes P n a key) → Realizes P n (.app e a) o
termination_by o => sizeOf o

omit [Params] in
/-- Beta predecessors preserve the complete argument certificate. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes P n e' o) :
    Realizes P n e o := by
  cases o with
  | sort => simp only [Realizes] at H
  | pi =>
    simp only [Realizes] at H ⊢
    obtain ⟨a, HP, H⟩ := H
    exact ⟨a, HP, R.trans H⟩
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Typed argument observations have an operational meaning under every
substitution fixing their original context and supplying the free demands. -/
theorem Obs.realizes (H : Obs P n Δ S e t o) (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → Realizes P m (σ i) key) :
    Realizes P m (e.subst σ) o := by
  induction H generalizing m σ with
  | var _ _ h => exact hσ _ _ _ h
  | payload _ h => rw [HT.payload]; simp only [Realizes]; exact ⟨_, h, .refl⟩
  | app _ _ _ ihf iha =>
    have HF := ihf HT hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk HT hσ)
  | @lam Δ D b A B keys n S o _ _ _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih HT.cons (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [inst_eq_subst, Subst.liftN, subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons, lift_subst_cons, subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := D.subst σ))) HB

end Lean4Lean.VEnv.Strengthening.DependentPayloadObservation
