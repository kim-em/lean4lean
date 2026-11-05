import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeterogeneousControlTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages

/-! # Body and argument demands for unit-parameter constructors

The unit and record carriers are distinct ordinary types. A bare constructor
function demands its unit argument, including beneath temporary binders.
Substitution and beta preserve these demands. Native parameter coverage is not
inferred from ordinary typing or from this observation alone.
-/
namespace Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open HeterogeneousControl (ControlType ControlTyping)
variable [Params] {c r : Name} {unit record : AtomicControl.Atom}

/-- Finite neutral demands distinguish non-function atoms from arrows. -/
inductive Demand : ControlType → Ob → Prop where
  | atom : Demand (.atom carrier) .pi
  | sort : Demand (.sort u) .pi
  | fn : (∀ key ∈ keys, Demand A key) → Demand B o → Demand (.arrow A B) (.app keys o)

/-- A control valuation records the ordinary type of each demanded variable. -/
def Sets := Nat → ControlType → Ob → Prop

/-- Extend a valuation by the demands on one argument. -/
def Sets.cons (A : ControlType) (keys : List Ob) (S : Sets) : Sets
  | 0, t, o => t = A ∧ o ∈ keys
  | i+1, t, o => S i t o

/-- Typed control nodes demand free variables, the unit constructor or the
record constructor applied to a demanded unit. Projections and Pi types have no rule. -/
inductive Obs (unit record : AtomicControl.Atom) (c r : Name) : List ProofShape → Sets → ProofShape → ControlType → Ob → Prop where
  | var : ControlTyping Δ (.bvar i) t → Demand t o → S i t o → Obs unit record c r Δ S (.bvar i) t o
  | rigid : ControlTyping Δ (.const r []) (.arrow (.atom unit) (.atom record)) →
      Obs unit record c r Δ S (.const r []) (.arrow (.atom unit) (.atom record)) (.app [.pi] .pi)
  | terminal : ControlTyping Δ (.const c []) (.atom unit) → Obs unit record c r Δ S (.const c []) (.atom unit) .pi
  | app : ControlTyping Δ (.app f a) B → Obs unit record c r Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs unit record c r Δ S a A key) → Obs unit record c r Δ S (.app f a) B o
  | lam : ControlTyping Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs unit record c r (D :: Δ) (Sets.cons A keys S) b B o → Obs unit record c r Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Every observed term retains its assigned ordinary control type. -/
theorem Obs.typing (H : Obs unit record c r Δ S e t o) : ControlTyping Δ e t := by cases H <;> assumption

/-- The observation is compatible with that assigned type. -/
theorem Obs.demand (H : Obs unit record c r Δ S e t o) : Demand t o := by
  induction H with
  | var _ HD => exact HD
  | terminal => exact .atom
  | rigid => exact .fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .atom) .atom
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Interpreted variable renaming transports all node typings and demands. -/
theorem Obs.rename (H : Obs unit record c r Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs unit record c r Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ with
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using H.subst W) HD hj : Obs unit record c r Δ' T (.bvar j) _ _)
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
theorem Obs.lift (H : Obs unit record c r Δ S e t o) (SD : DomainSort Δ D u) :
    Obs unit record c r (D :: Δ) (Sets.cons A keys S) (e.liftN 1) t o := by
  have R := H.rename (H.typing.weak_interpretation SD)
    (T := Sets.cons A keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution supplies only demanded observations; it needs no native
recovery or comparison certificate for the substituted terms. -/
theorem Obs.subst (H : Obs unit record c r Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i t key, S i t key → Demand t key → Obs unit record c r Δ' T (σ i) t key) :
    Obs unit record c r Δ' T (e.subst σ) t o := by
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

/-- Free demands carry ordinary typings in their current context. -/
def Sets.Typed (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i t o, S i t o → ControlTyping Δ (.bvar i) t

/-- The fresh variable extends a typed valuation. -/
theorem Sets.Typed.cons (HS : S.Typed Δ) (HX : ControlTyping (D :: Δ) (.bvar 0) A)
    (SD : DomainSort Δ D u) : (Sets.cons A keys S).Typed (D :: Δ) := by
  intro i t o hi
  cases i with
  | zero => obtain ⟨rfl, _⟩ := hi; exact HX
  | succ i => exact (HS i t o hi).subst ((HS i t o hi).weak_interpretation SD)

/-- Identity context interpretation changes node typings while fixing syntax. -/
theorem Obs.context (H : Obs unit record c r Δ S e t o) (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    Obs unit record c r Δ' S e t o := by
  simpa only [ProofShape.subst_id] using H.rename W (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta replaces the bound control demands by observations of its argument. -/
theorem Obs.beta_forward (H : Obs unit record c r Δ S (.app (.lam D b) a) t o) (HS : S.Typed Δ) :
    Obs unit record c r Δ S (b.inst a) t o := by
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
theorem Obs.primitive_head (H : Obs unit record c r Δ S e t o) (HH : PrimitiveHead e) :
    e.constHead = some c ∨ e.constHead = some r := by
  induction H with
  | var | lam => cases HH
  | terminal => exact .inl rfl
  | rigid => exact .inr rfl
  | app _ _ _ ihf _ => exact ihf HH

/-- A sort has no neutral demand. -/
theorem Obs.not_sort (H : Obs unit record c r Δ S (.sort u) t o) : False := by cases H

/-- A projection has no neutral demand. -/
theorem Obs.not_proj (H : Obs unit record c r Δ S (.proj s j e) t o) : False := by cases H

/-- A Pi has no neutral demand. -/
theorem Obs.not_pi (H : Obs unit record c r Δ S (.forallE A B) t o) : False := by cases H

/-- Typed function eta preserves neutral demands. At an atomic carrier or
universe it is impossible; at arrows the fresh argument is retained. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs unit record c r Δ S e t o) (R : NativeEtaExpansion Step Δ e out) : Obs unit record c r Δ S out t o := by
  cases H.demand with
  | atom => exact (H.typing.no_eta_atom hstep R).elim
  | sort => exact (H.typing.no_eta_sort hstep R).elim
  | @fn keys A B o HK HO =>
    obtain ⟨D, rfl, HT, HB, HX, u, SD⟩ := H.typing.eta_parts hstep R
    exact .lam HT HK (.app HB (H.lift SD) (fun key hk => .var HX (HK key hk) ⟨rfl, hk⟩))

/-- Constant expansion introduces no new demand on its arbitrary argument. -/
theorem Obs.constant_expansion (H : Obs unit record c r Δ S e t o) : Obs unit record c r Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro H.typing.ne_proof))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands its original payload, at the same type. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs unit record c r Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) : Obs unit record c r Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H.demand
      · exact .var HF.lam_parts.2 H.demand ⟨rfl, by simp⟩
    · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact H

/-- Operational demands retain the assigned control type, so a unit leaf
and a type-family result may have different sets of acceptable readouts. -/
def Realizes (P : ControlType → ProofShape → Prop) (e : ProofShape)
    (t : ControlType) : Ob → Prop
  | .pi => ∃ a, P t a ∧ ProofShape.BetaRed e a
  | .sort => False
  | .app keys o => match t with
    | .arrow A B => ∀ a, (∀ key ∈ keys, Realizes P a A key) → Realizes P (.app e a) B o
    | _ => False
termination_by o => sizeOf o

/-- Beta predecessors preserve all typed operational demands. -/
theorem Realizes.beta_back (R : ProofShape.BetaRed e e') (H : Realizes P e' t o) :
    Realizes P e t o := by
  cases o with
  | sort => simp only [Realizes] at H
  | pi =>
    simp only [Realizes] at H ⊢
    obtain ⟨a, HP, H⟩ := H
    exact ⟨a, HP, R.trans H⟩
  | app keys o =>
    cases t with
    | atom _ | sort => simp only [Realizes] at H
    | arrow A B =>
      simp only [Realizes] at H ⊢
      exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Typed unit observations have an operational interpretation under every
raw substitution supplying their free demands. The unit constructor and record
constructor must satisfy the selected operational interpretation. -/
theorem Obs.realizes (H : Obs unit record c r Δ S e t o) (HC : P (.atom unit) (.const c []))
    (HF : Realizes P (.const r []) (.arrow (.atom unit) (.atom record)) (.app [.pi] .pi))
    (hσ : ∀ i t key, S i t key → Realizes P (σ i) t key) :
    Realizes P (e.subst σ) t o := by
  induction H generalizing σ with
  | var _ _ h => exact hσ _ _ _ h
  | terminal => simp only [Realizes]; exact ⟨_, HC, .refl⟩
  | rigid => exact HF
  | app _ _ _ ihf iha =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam Δ D b A B keys S o _ _ _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih (σ := σ.cons a) (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back (E ▸ (ProofShape.BetaRed.beta (A := D.subst σ))) HB

end Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
