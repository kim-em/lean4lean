import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandObservation
import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelCompatibility

/-! # Polymorphic stored aliases with independent universe-instance evidence

An alias observes every actual stored body at equivalent universe arguments.
These are recursive observation derivations, not consequences of ordinary
conversion. The inductive evidence is well-founded; it need not have finitely
many branches because universe instances are universally quantified.
-/
namespace Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open DemandProfile
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {c : Name} {arity : Nat}

/-- Typed control frames and sort-valued stored aliases. Each equivalent
universe instance has its own independently observed actual body. -/
inductive Obs (c : Name) (arity : Nat) : List ProofShape → Sets → ProofShape → Profile → Ob → Prop where
  | const : Typing Δ (.const c ls) (spineProfile arity) →
      Obs c arity Δ S (.const c ls) (spineProfile arity) (spineDemand arity)
  | delta : Typing Δ (.const name levels) .sort →
      (PureObservation.Definitions.ofEnv env univs henv).unfolds name levels rhs →
      (∀ {levels' rhs'}, List.Forall₂ (· ≈ ·) levels levels' →
        (PureObservation.Definitions.ofEnv env univs henv).unfolds name levels' rhs' →
        Obs c arity Δ S (proofErase [] rhs') .sort .pi) →
      Obs c arity Δ S (.const name levels) .sort .pi
  | var : Typing Δ (.bvar i) t → Demand t o → S i t o → Obs c arity Δ S (.bvar i) t o
  | app : Typing Δ (.app f a) B → Obs c arity Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs c arity Δ S a A key) → Obs c arity Δ S (.app f a) B o
  | lam : Typing Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs c arity (D :: Δ) (Sets.cons A keys S) b B o → Obs c arity Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Every observed term retains its assigned ordinary control type. -/
theorem Obs.typing (H : Obs c arity Δ S e t o) : Typing Δ e t := by cases H <;> assumption

/-- The observation is compatible with that assigned type. -/
theorem Obs.demand (H : Obs c arity Δ S e t o) : Demand t o := by
  induction H with
  | const => exact spineDemand_valid arity
  | delta => exact .sort
  | var _ HD => exact HD
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Interpreted variable renaming transports all node typings and demands. -/
theorem Obs.rename (H : Obs c arity Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs c arity Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | const H => exact .const (by simpa only [ProofShape.subst] using H.subst W)
  | delta HT HD _ ih =>
    apply Obs.delta (by simpa only [ProofShape.subst] using HT.subst W) HD
    intro levels' rhs' HL HD'
    simpa only [proofErase_closed_subst ((PureObservation.Definitions.ofEnv env univs henv).closed HD')] using ih HL HD' W hσ
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using H.subst W) HD hj : Obs c arity Δ' T (.bvar j) _ _)
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
theorem Obs.lift (H : Obs c arity Δ S e t o) (SD : DomainSort Δ D u) :
    Obs c arity (D :: Δ) (Sets.cons A keys S) (e.liftN 1) t o := by
  have R := H.rename (H.typing.weak_interpretation SD)
    (T := Sets.cons A keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution supplies only demanded observations; it needs no native
recovery or comparison certificate for the substituted terms. -/
theorem Obs.subst (H : Obs c arity Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → Demand t key → Obs c arity Δ' T (σ i) t key) :
    Obs c arity Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | const H => exact .const (by simpa only [ProofShape.subst] using H.subst W)
  | delta HT HD _ ih =>
    apply Obs.delta (by simpa only [ProofShape.subst] using HT.subst W) HD
    intro levels' rhs' HL HD'
    simpa only [proofErase_closed_subst ((PureObservation.Definitions.ofEnv env univs henv).closed HD')] using ih HL HD' W hσ
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

/-- Identity context interpretation changes node typings while fixing syntax. -/
theorem Obs.context (H : Obs c arity Δ S e t o) (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    Obs c arity Δ' S e t o := by
  simpa only [ProofShape.subst_id] using H.rename W (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta replaces the bound control demands by observations of its argument. -/
theorem Obs.beta_forward (H : Obs c arity Δ S (.app (.lam D b) a) t o) (HS : S.Typed Δ) :
    Obs c arity Δ S (b.inst a) t o := by
  cases H with
  | app HT HF HX =>
    cases HF with
    | lam HL HK HB =>
      have R := HB.subst HT.beta_interpretation (T := S) (fun i t key hi HD => by
        cases i with
        | zero => obtain ⟨rfl, hk⟩ := hi; exact HX key hk
        | succ i => exact .var (HS i t key hi) HD hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

/-- A primitive head is rigid unless the entire source is a bare alias.
Sort-valued aliases cannot supply the function of an application. -/
theorem Obs.primitive_head (H : Obs c arity Δ S e t o) (HH : PrimitiveHead e)
    (HA : ∀ name levels, e ≠ .const name levels) : e.constHead = some c := by
  have aux : ∀ {Δ S e t o}, Obs c arity Δ S e t o → PrimitiveHead e →
      t ≠ .sort → e.constHead = some c := by
    intro Δ S e t o H
    induction H with
    | const => intros; rfl
    | delta => intro _ h; exact (h rfl).elim
    | var => intro h _; exact h.elim
    | app _ _ _ ihf _ => intro hh _; exact ihf hh (by intro h; cases h)
    | lam => intro h _; exact h.elim
  cases H with
  | const => rfl
  | delta => exact (HA _ _ rfl).elim
  | var | lam => cases HH
  | app _ HF _ =>
    have E := aux HF (by exact HH) (by intro h; cases h)
    exact E

/-- Every primitive head is either the designated rigid family or an actual
stored definition; application frames preserve that disjunction. -/
theorem Obs.primitive_heads (H : Obs c arity Δ S e t o) (HH : PrimitiveHead e) :
    e.constHead = some c ∨ ∃ name levels rhs,
      (PureObservation.Definitions.ofEnv env univs henv).unfolds name levels rhs ∧
      e.constHead = some name := by
  induction H with
  | const => exact .inl rfl
  | delta _ HD => exact .inr ⟨_, _, _, HD, rfl⟩
  | var | lam => cases HH
  | app _ _ _ ihf _ => exact ihf HH

/-- All previous dependent rigid observations embed without new premises. -/
theorem Obs.of_rigid (H : RigidDemandProfile.Obs c arity Δ S e t o) :
    Obs c arity Δ S e t o := by
  induction H with
  | const HT => exact .const HT
  | var HT HD HS => exact .var HT HD HS
  | app HT _ _ ihf iha => exact .app HT ihf iha
  | lam HT HK _ ih => exact .lam HT HK ih

/-- Every monomorphic alias derivation embeds. Equivalent empty universe
lists are empty, and the stored registry fixes the body at that instance. -/
theorem Obs.of_monomorphic (H : AliasDemandProfile.Obs c arity Δ S e t o) :
    Obs c arity Δ S e t o := by
  induction H with
  | const HT => exact .const HT
  | delta HT HD _ ih =>
    apply Obs.delta HT HD
    intro levels' rhs' HL HD'
    cases HL
    cases PureObservation.Definitions.ofEnv_unique henv HD HD'
    exact ih
  | var HT HD HS => exact .var HT HD HS
  | app HT _ _ ihf iha => exact .app HT ihf iha
  | lam HT HK _ ih => exact .lam HT HK ih

/-- A nonempty universe instance of an actual stored alias cannot occur in
the old monomorphic grammar at a rigid family. Thus the new instance coverage
is a strict extension whenever such an installed alias is present. -/
theorem stored_poly_alias_not_monomorphic
    (hc : env.Rigid c)
    (HD : (PureObservation.Definitions.ofEnv env univs henv).unfolds name levels rhs)
    (hne : levels ≠ []) :
    ¬ AliasDemandProfile.Obs c arity Δ S (.const name levels) t o := by
  intro H
  cases H with
  | const => exact PureObservation.Definitions.ofEnv_no_rigid henv hc HD
  | delta => exact hne rfl

/-- A sort has no neutral demand. -/
theorem Obs.not_sort (H : Obs c arity Δ S (.sort u) t o) : False := by cases H

/-- A projection has no neutral demand. -/
theorem Obs.not_proj (H : Obs c arity Δ S (.proj s j e) t o) : False := by cases H

/-- A Pi has no neutral demand. -/
theorem Obs.not_pi (H : Obs c arity Δ S (.forallE A B) t o) : False := by cases H

/-- Native eta preserves the demanded result. An ignored argument may be a
proof; whenever its value is demanded, its visible profile forces retention. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs c arity Δ S e t o) (R : NativeEtaExpansion Step Δ e out) : Obs c arity Δ S out t o := by
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
theorem Obs.constant_expansion (H : Obs c arity Δ S e t o) : Obs c arity Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame H.demand.visible
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro (H.typing.ne_proof H.demand.visible)))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands its original payload, at the same type. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs c arity Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) : Obs c arity Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep H.demand.visible RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H.demand
      · exact .var (HF.lam_parts.2 H.demand.visible) H.demand ⟨rfl, by simp⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H

end Lean4Lean.VEnv.Strengthening.PolyAliasDemandProfile
