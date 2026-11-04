import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDemandProfileFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure

/-! # Finite observations with dependent and ignored argument types

Ignored domains permit arbitrary dependent parameters, including proofs.
Only a demanded argument must carry an observable profile and remain retained.
-/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Universes and functions can be demanded; ignored domains supply no demands. -/
inductive Demand : Profile → Ob → Prop where
  | sort : Demand .sort .pi
  | fn : (∀ key ∈ keys, Demand A key) → Demand B o → Demand (.arrow A B) (.app keys o)

omit [Params] in
/-- Every finite demand has an observable result, excluding ignored profiles. -/
theorem Demand.visible (H : Demand p o) : p.Visible := by
  induction H with
  | sort => exact .sort
  | fn _ _ _ ih => exact .arrow ih

/-- A control valuation records the ordinary type of each demanded variable. -/
def Sets := Nat → Profile → Ob → Prop

/-- Extend a valuation by the demands on one argument. -/
def Sets.cons (A : Profile) (keys : List Ob) (S : Sets) : Sets
  | 0, t, o => t = A ∧ o ∈ keys
  | i+1, t, o => S i t o

/-- Neutral observations have typed nodes, but no constant, projection or Pi
payload rule. Only the selected free variables supply atomic observations. -/
inductive Obs : List ProofShape → Sets → ProofShape → Profile → Ob → Prop where
  | var : Typing Δ (.bvar i) t → Demand t o → S i t o → Obs Δ S (.bvar i) t o
  | app : Typing Δ (.app f a) B → Obs Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs Δ S a A key) → Obs Δ S (.app f a) B o
  | lam : Typing Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs (D :: Δ) (Sets.cons A keys S) b B o → Obs Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Every observed term retains its assigned ordinary control type. -/
theorem Obs.typing (H : Obs Δ S e t o) : Typing Δ e t := by cases H <;> assumption

/-- The observation is compatible with that assigned type. -/
theorem Obs.demand (H : Obs Δ S e t o) : Demand t o := by
  induction H with
  | var _ HD => exact HD
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Interpreted variable renaming transports all node typings and demands. -/
theorem Obs.rename (H : Obs Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using H.subst W) HD hj : Obs Δ' T (.bvar j) _ _)
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W hσ) (fun key hk => iha key hk W hσ)
  | @lam Δ D b A B keys S o H HK _ ih =>
    apply Obs.lam (H.subst W) HK
    apply ih W.cons
    intro i t key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i t key hi
      exact ⟨j+1, by simp [ProofShape.Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm], hj⟩

/-- A fresh typed binder lifts every existing observation. -/
theorem Obs.lift (H : Obs Δ S e t o) (SD : DomainSort Δ D u) :
    Obs (D :: Δ) (Sets.cons A keys S) (e.liftN 1) t o := by
  have R := H.rename (H.typing.weak_interpretation SD)
    (T := Sets.cons A keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution supplies only demanded observations; it needs no native
recovery or comparison certificate for the substituted terms. -/
theorem Obs.subst (H : Obs Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → Demand t key → Obs Δ' T (σ i) t key) :
    Obs Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | var H HD h => exact hσ _ _ _ h HD
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W hσ) (fun key hk => iha key hk W hσ)
  | @lam Δ D b A B keys S o H HK _ ih =>
    have H' := H.subst W
    obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H
    obtain ⟨D₀, b₀, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _⟩ := hf.lam_inv henv hΓ
    have SD : DomainSort Δ D u := ⟨Γ, D₀, hΓ, EΓ, hD, ED⟩
    apply Obs.lam H' HK
    apply ih W.cons
    intro i t key hi HD
    cases i with
    | zero => obtain ⟨rfl, hk⟩ := hi; exact .var (H'.lam_parts.2 HD.visible) HD ⟨rfl, hk⟩
    | succ i => exact (hσ i t key hi HD).lift (W.sort SD)

/-- Free demands carry ordinary typings in their current context. -/
def Sets.Typed (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i t o, S i t o → Typing Δ (.bvar i) t

/-- The fresh variable extends a typed valuation. -/
theorem Sets.Typed.cons (HS : S.Typed Δ) (HX : A.Visible → Typing (D :: Δ) (.bvar 0) A)
    (HK : ∀ key ∈ keys, Demand A key) (SD : DomainSort Δ D u) : (Sets.cons A keys S).Typed (D :: Δ) := by
  intro i t o hi
  cases i with
  | zero => obtain ⟨rfl, hk⟩ := hi; exact HX (HK o hk).visible
  | succ i => exact (HS i t o hi).subst ((HS i t o hi).weak_interpretation SD)

/-- Identity context interpretation changes node typings while fixing syntax. -/
theorem Obs.context (H : Obs Δ S e t o) (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    Obs Δ' S e t o := by
  simpa only [ProofShape.subst_id] using H.rename W (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta replaces the bound control demands by observations of its argument. -/
theorem Obs.beta_forward (H : Obs Δ S (.app (.lam D b) a) t o) (HS : S.Typed Δ) :
    Obs Δ S (b.inst a) t o := by
  cases H with
  | app HT HF HX =>
    cases HF with
    | lam HL HK HB =>
      have R := HB.subst HT.beta_interpretation (T := S) (fun i t key hi HD => by
        cases i with
        | zero => obtain ⟨rfl, hk⟩ := hi; exact HX key hk
        | succ i => exact .var (HS i t key hi) HD hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

/-- Forgetting typing decorations gives the existing raw neutral semantics. -/
theorem Obs.forget (H : Obs Δ S e t o) (hS : ∀ i t key, S i t key → T i key) :
    VariableObservation T e o := by
  induction H generalizing T with
  | var _ _ hi => exact NeutralObservation.Obs.var (hS _ _ _ hi)
  | app _ _ _ ihf iha => exact NeutralObservation.Obs.app (ihf hS) (fun key hk => iha key hk hS)
  | lam _ _ _ ih =>
    apply NeutralObservation.Obs.lam
    apply ih
    intro i t key hi
    cases i with
    | zero => exact hi.2
    | succ i => exact hS i t key hi

/-- No constant or projection primitive can act on an observed head. -/
theorem Obs.not_primitiveHead (H : Obs Δ S e t o) : ¬ PrimitiveHead e :=
  (H.forget (T := fun _ _ => True) (fun _ _ _ _ => trivial)).not_primitiveHead

/-- A sort has no neutral demand. -/
theorem Obs.not_sort (H : Obs Δ S (.sort u) t o) : False := by cases H

/-- A projection has no neutral demand. -/
theorem Obs.not_proj (H : Obs Δ S (.proj s j e) t o) : False := by cases H

/-- A Pi has no neutral demand. -/
theorem Obs.not_pi (H : Obs Δ S (.forallE A B) t o) : False := by cases H

/-- Native eta preserves the demanded result. An ignored argument may be a
proof; whenever its value is demanded, its visible profile forces retention. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs Δ S e t o) (R : NativeEtaExpansion Step Δ e out) : Obs Δ S out t o := by
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

/-- Constant expansion introduces no new demand on its arbitrary argument. -/
theorem Obs.constant_expansion (H : Obs Δ S e t o) : Obs Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame H.demand.visible
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro (H.typing.ne_proof H.demand.visible)))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands its original payload, at the same type. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) : Obs Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep H.demand.visible RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H.demand
      · exact .var (HF.lam_parts.2 H.demand.visible) H.demand ⟨rfl, by simp⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H

end Lean4Lean.VEnv.Strengthening.DemandProfile
