import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages

/-! # A rigid family demanding a unit endofunction parameter

The observation tracks a monomorphic rigid family constant as well as the
unit constructor. The family demands its retained unit endofunction argument, so its
parameter history survives beta, changed annotations and function eta. Its
function demand has an empty input-demand list: only ordinary input typing is
needed. This permits fresh inputs under a convertible, natively selected domain.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open AtomicControl (Atom ControlType ControlTyping Demand Sets)
variable [Params] [Atom] {c r : Name} {v : VLevel}

/-- Typed control nodes demand free variables, the unit constructor or the
rigid family applied to a demanded unit endofunction. Projections and Pi types have no rule. -/
inductive Obs (c r : Name) (v : VLevel) : List ProofShape → Sets → ProofShape → ControlType → Ob → Prop where
  | var : ControlTyping Δ (.bvar i) t → Demand t o → S i t o → Obs c r v Δ S (.bvar i) t o
  | rigid : ControlTyping Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) →
      Obs c r v Δ S (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) (.app [.app [] .pi] .pi)
  | terminal : ControlTyping Δ (.const c []) .atom → Obs c r v Δ S (.const c []) .atom .pi
  | app : ControlTyping Δ (.app f a) B → Obs c r v Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs c r v Δ S a A key) → Obs c r v Δ S (.app f a) B o
  | lam : ControlTyping Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs c r v (D :: Δ) (Sets.cons A keys S) b B o → Obs c r v Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Every observed term retains its assigned ordinary control type. -/
theorem Obs.typing (H : Obs c r v Δ S e t o) : ControlTyping Δ e t := by cases H <;> assumption

/-- The observation is compatible with that assigned type. -/
theorem Obs.demand (H : Obs c r v Δ S e t o) : Demand t o := by
  induction H with
  | var _ HD => exact HD
  | terminal => exact .atom
  | rigid =>
    apply Demand.fn ?_ .sort
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .fn (by simp) .atom
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Interpreted variable renaming transports all node typings and demands. -/
theorem Obs.rename (H : Obs c r v Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs c r v Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using H.subst W) HD hj : Obs c r v Δ' T (.bvar j) _ _)
  | terminal H => exact .terminal (H.subst W)
  | rigid H => exact .rigid (H.subst W)
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
theorem Obs.lift (H : Obs c r v Δ S e t o) (SD : DomainSort Δ D u) :
    Obs c r v (D :: Δ) (Sets.cons A keys S) (e.liftN 1) t o := by
  have R := H.rename (H.typing.weak_interpretation SD)
    (T := Sets.cons A keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution supplies only demanded observations; it needs no native
recovery or comparison certificate for the substituted terms. -/
theorem Obs.subst (H : Obs c r v Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → Demand t key → Obs c r v Δ' T (σ i) t key) :
    Obs c r v Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | var H HD h => exact hσ _ _ _ h HD
  | terminal H => exact .terminal (H.subst W)
  | rigid H => exact .rigid (H.subst W)
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W hσ) (fun key hk => iha key hk W hσ)
  | @lam Δ D b A B keys S o H HK _ ih =>
    have H' := H.subst W
    obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H
    obtain ⟨D₀, b₀, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _⟩ := hf.lam_inv henv hΓ
    have SD : DomainSort Δ D u := ⟨Γ, D₀, hΓ, EΓ, hD, ED⟩
    apply Obs.lam H' HK
    apply ih W.cons
    intro i t key hi HD
    cases i with
    | zero => obtain ⟨rfl, hk⟩ := hi; exact .var H'.lam_parts.2 HD ⟨rfl, hk⟩
    | succ i => exact (hσ i t key hi HD).lift (W.sort SD)

/-- Identity context interpretation changes node typings while fixing syntax. -/
theorem Obs.context (H : Obs c r v Δ S e t o) (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    Obs c r v Δ' S e t o := by
  simpa only [ProofShape.subst_id] using H.rename W (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta replaces the bound control demands by observations of its argument. -/
theorem Obs.beta_forward (H : Obs c r v Δ S (.app (.lam D b) a) t o) (HS : S.Typed Δ) :
    Obs c r v Δ S (b.inst a) t o := by
  cases H with
  | app HT HF HX =>
    cases HF with
    | lam HL HK HB =>
      have R := HB.subst HT.beta_interpretation (T := S) (fun i t key hi HD => by
        cases i with
        | zero => obtain ⟨rfl, hk⟩ := hi; exact HX key hk
        | succ i => exact .var (HS i t key hi) HD hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

/-- Every primitive root of an observation has one of the two designated
rigid heads. Application may expose the family head but cannot invent another. -/
theorem Obs.primitive_head (H : Obs c r v Δ S e t o) (HH : PrimitiveHead e) :
    e.constHead = some c ∨ e.constHead = some r := by
  induction H with
  | var | lam => cases HH
  | terminal => exact .inl rfl
  | rigid => exact .inr rfl
  | app _ _ _ ihf _ => exact ihf HH

/-- A sort has no neutral demand. -/
theorem Obs.not_sort (H : Obs c r v Δ S (.sort u) t o) : False := by cases H

/-- A projection has no neutral demand. -/
theorem Obs.not_proj (H : Obs c r v Δ S (.proj s j e) t o) : False := by cases H

/-- A Pi has no neutral demand. -/
theorem Obs.not_pi (H : Obs c r v Δ S (.forallE A B) t o) : False := by cases H

/-- Typed function eta preserves neutral demands. At an atomic carrier or
universe it is impossible; at arrows the fresh argument is retained. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs c r v Δ S e t o) (R : NativeEtaExpansion Step Δ e out) : Obs c r v Δ S out t o := by
  cases H.demand with
  | atom => exact (H.typing.no_eta_atom hstep R).elim
  | sort => exact (H.typing.no_eta_sort hstep R).elim
  | @fn keys A B o HK HO =>
    obtain ⟨D, rfl, HT, HB, HX, u, SD⟩ := H.typing.eta_parts hstep R
    exact .lam HT HK (.app HB (H.lift SD) (fun key hk => .var HX (HK key hk) ⟨rfl, hk⟩))

/-- Constant expansion introduces no new demand on its arbitrary argument. -/
theorem Obs.constant_expansion (H : Obs c r v Δ S e t o) : Obs c r v Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro H.typing.ne_proof))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands its original payload, at the same type. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs c r v Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) : Obs c r v Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H.demand
      · exact .var HF.lam_parts.2 H.demand ⟨rfl, by simp⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
