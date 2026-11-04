import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortOriginObservation

/-! # Typed finite observations of marked universe payloads

Control types constrain the shape of a finite demand. In particular a function
variable cannot be assigned a sort-head demand, the untyped case that fails under
eta expansion. Valuations also retain these types when beta supplies arguments.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.SortControlObservation
open _root_.Lean4Lean Params
open PureObservation (Ob)
open PiOriginObservation (FixedTail)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- A finite demand follows its closed control type. -/
inductive Demand : ControlType → Ob → Prop where
  | payload : Demand (.sort u) .sort
  | neutral : Demand (.sort u) .pi
  | fn : (∀ key ∈ keys, Demand A key) → Demand B o → Demand (.arrow A B) (.app keys o)

/-- Control valuations remember both a demand and its assigned type. -/
def Sets := Nat → ControlType → Ob → Prop

/-- Bind the finite demands of one control argument at its assigned type. -/
def Sets.cons (A : ControlType) (keys : List Ob) (S : Sets) : Sets
  | 0, t, o => t = A ∧ o ∈ keys
  | i+1, t, o => S i t o

variable [Params]
/-- Every observed node has an ordinary typed representative. Universe payloads
retain their level certificate below temporary control binders. -/
inductive Obs (P : VLevel → Prop) :
    Nat → List ProofShape → Sets → ProofShape → ControlType → Ob → Prop where
  | var : ControlTyping Δ (.bvar i) t → Demand t o → S i t o → Obs P n Δ S (.bvar i) t o
  | payload : ControlTyping Δ (.sort v) (.sort u) →
      P v → Obs P n Δ S (.sort v) (.sort u) .sort
  | app : ControlTyping Δ (.app f a) B → Obs P n Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs P n Δ S a A key) → Obs P n Δ S (.app f a) B o
  | lam : ControlTyping Δ (.lam D b) (.arrow A B) → (∀ key ∈ keys, Demand A key) →
      Obs P (n+1) (D :: Δ) (Sets.cons A keys S) b B o →
      Obs P n Δ S (.lam D b) (.arrow A B) (.app keys o)

/-- Forgetting the demand retains its ordinary source typing. -/
theorem Obs.typing (H : Obs P n Δ S e t o) : ControlTyping Δ e t := by
  cases H <;> assumption

/-- Every derivable observation has a demand compatible with its control type. -/
theorem Obs.demand (H : Obs P n Δ S e t o) : Demand t o := by
  induction H with
  | var _ HD => exact HD
  | payload => exact .payload
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Typed renaming fixes the original payload and transports all control
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
    exact .payload H' HP
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ D b A B keys n S o H HK _ ih =>
    have H' := H.subst W
    obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H
    obtain ⟨D₀, b₀, rfl, _, ED, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hD⟩, _⟩ := hf.lam_inv henv hΓ
    have SD : DomainSort Δ D u := ⟨Γ, D₀, hΓ, EΓ, hD, ED⟩
    apply Obs.lam H' HK
    apply ih W.cons HT.lift
    intro i t key hi HD
    cases i with
    | zero =>
      obtain ⟨rfl, hk⟩ := hi
      exact .var H'.lam_parts.2 HD ⟨rfl, hk⟩
    | succ i => exact (hσ i t key hi HD).lift (W.sort SD)

/-- Erasing the type decorations gives the original marked observation.
This transfers its beta readout without changing the payload predicate. -/
theorem Obs.forget (H : Obs P n Δ S e t o)
    (hS : ∀ i t key, S i t key → T i key) : SortOriginObservation.Obs P n T e o := by
  induction H generalizing T with
  | var _ _ hi => exact .var (hS _ _ _ hi)
  | payload _ HP => exact .payload HP
  | app _ _ _ ihf iha => exact .app (ihf hS) (fun key hk => iha key hk hS)
  | lam _ _ _ ih =>
    apply SortOriginObservation.Obs.lam
    apply ih
    intro i t key hi
    cases i with
    | zero => exact hi.2
    | succ i => exact hS i t key hi

/-- Empty control valuations read a universe with its level certificate. -/
theorem Obs.readout (H : Obs P 0 Δ (fun _ _ _ => False) e (.sort u) .sort) :
    ∃ v, P v ∧ BetaRed e (.sort v) :=
  (H.forget (T := fun _ _ => False) (fun _ _ _ h => h)).readout

/-- Opaque primitives cannot act on the control head of a marked demand. -/
theorem Obs.not_primitiveHead (H : Obs P n Δ S e t o) : ¬ PrimitiveHead e :=
  (H.forget (T := fun _ _ => True) (fun _ _ _ _ => trivial)).not_primitiveHead

/-- Literal Pi syntax carries no marked sort demand. -/
theorem Obs.not_forallE (H : Obs P n Δ S (.forallE A B) t o) : False := by cases H

/-- Literal projections carry no marked payload. -/
theorem Obs.not_proj (H : Obs P n Δ S (.proj s i e) t o) : False := by cases H

/-- Native eta preserves every typed marked demand. Sort payloads cannot
expand, while function demands pass through the retained fresh variable. -/
theorem Obs.native_eta (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs P n Δ S e t o) (R : NativeEtaExpansion Step Δ e out) :
    Obs P n Δ S out t o := by
  have HD := H.demand
  cases HD with
  | payload | neutral => exact (H.typing.no_eta_sort hstep R).elim
  | @fn keys A B o HK HO =>
    obtain ⟨D, rfl, HT, HB, HX, u, SD⟩ := H.typing.eta_parts hstep R
    apply Obs.lam HT HK
    apply Obs.app HB (H.lift SD)
    intro key hk
    exact Obs.var HX (HK key hk) ⟨rfl, hk⟩

/-- Every free control demand has its assigned ordinary typing. -/
def Sets.Typed (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i t o, S i t o → ControlTyping Δ (.bvar i) t

/-- A fresh typed control argument extends a well-typed valuation. -/
theorem Sets.Typed.cons (HS : S.Typed Δ) (HX : ControlTyping (D :: Δ) (.bvar 0) A)
    (SD : DomainSort Δ D u) : (Sets.cons A keys S).Typed (D :: Δ) := by
  intro i t o hi
  cases i with
  | zero => obtain ⟨rfl, _⟩ := hi; exact HX
  | succ i =>
    have H := HS i t o hi
    exact H.subst (H.weak_interpretation SD)

/-- Identity context interpretation changes typing decorations while keeping
the raw observation, payload depth, and valuation exactly fixed. -/
theorem Obs.context (H : Obs P n Δ S e t o) (W : ContextSubstitution Δ Δ' Subst.id) :
    Obs P n Δ' S e t o := by
  have HT : FixedTail n n Subst.id := by intro i; rfl
  simpa only [subst_id] using H.rename W HT (fun i t key hi => ⟨i, rfl, hi⟩)

/-- Beta replaces demanded control variables by the observed argument.
Typing of the free valuation suffices for the variables left untouched. -/
theorem Obs.beta_forward (H : Obs P n Δ S (.app (.lam D b) a) t o) (HS : S.Typed Δ) :
    Obs P n Δ S (b.inst a) t o := by
  cases H with
  | app HT HF HX =>
    cases HF with
    | lam HL HK HB =>
      have HF : FixedTail n n Subst.id := by intro i; rfl
      have R := HB.subst HT.beta_interpretation HF.cons (T := S) (fun i t key hi HD => by
        cases i with
        | zero =>
          obtain ⟨rfl, hk⟩ := hi
          exact HX key hk
        | succ i => exact .var (HS i t key hi) HD hi)
      simpa only [inst_eq_subst, Subst.liftN, Subst.one] using R

/-- The constant wrapper introduces no argument demand; its fixed domain
and whole function nevertheless retain their canonical control typings. -/
theorem Obs.constant_expansion (H : Obs P n Δ S e t o) :
    Obs P n Δ S (constantExpansion e) t o := by
  obtain ⟨HF, SD⟩ := H.typing.constant_frame
  have HT := H.typing.compute (Step := fun _ => ConstantExpansion) erased_constantExpansion_descent
    (.base (ConstantExpansion.intro H.typing.ne_proof))
  exact .app (keys := []) HT (.lam HF (by simp) (H.lift SD)) (by simp)

/-- A native identity wrapper demands exactly its original typed payload. -/
theorem Obs.native_identity (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs P n Δ S e t o) (R : NativeIdentityExpansion Step Δ e out) :
    Obs P n Δ S out t o := by
  have HT := H.typing.compute (erased_nativeIdentityExpansion_descent hstep) (.base R)
  cases R with
  | intro RN =>
    have HF := H.typing.identity_frame hstep RN
    apply Obs.app HT (keys := [o])
    · apply Obs.lam HF
      · intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact H.demand
      · exact .var HF.lam_parts.2 H.demand ⟨rfl, by simp⟩
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact H

end Lean4Lean.VEnv.Strengthening.ProofShape.SortControlObservation
