import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionVariableExposure

/-! # Joint observations retaining function parameters in native types

A lambda retains the type demand of each demanded input. A Pi retains the same
input demands and the dependent result-type demand under its fresh binder.
Unit-carrier, unit-function, universe and the special family-to-universe function-type
equalities are ordinary opaque witnesses; the record
family parameter is retained operationally by its demanded family application.
This extends the unit-parameter grammar: a function_type leaf admits only the
empty-input-demand unit endofunction type. It cannot admit an arbitrary record
family type from ordinary equality.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- The same grammar records value construction and annotation provenance.
There is no rule admitting an arbitrary ordinarily equal record-family type.
Full native recovery and computation preservation are not asserted here. -/
inductive Obs (unit record : AtomicControl.Atom) (uc ctor family : Name) :
    List ProofShape → Sets → ProofShape → Key → Prop where
  | var : HeterogeneousControl.ControlTyping Δ (.bvar i) (key.control unit record) →
      key.Valid unit record → S i key → Obs unit record uc ctor family Δ S (.bvar i) key
  | unit_ctor : HeterogeneousControl.ControlTyping Δ (.const uc []) (.atom unit) →
      Obs unit record uc ctor family Δ S (.const uc []) .unit
  | record_ctor : HeterogeneousControl.ControlTyping Δ (.const ctor []) (.arrow (.arrow (.atom unit) (.atom unit)) (.atom record)) →
      Obs unit record uc ctor family Δ S (.const ctor []) (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] .record)
  | family : HeterogeneousControl.ControlTyping Δ (.const family [])
      (.arrow (.arrow (.atom unit) (.atom unit)) (.sort (HeterogeneousControl.ControlType.atom record).level)) →
      Obs unit record uc ctor family Δ S (.const family []) (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] (.type .record))
  | family_type : TypeEquality Δ e (.arrow (.arrow (.atom unit) (.atom unit)) (.sort (HeterogeneousControl.ControlType.atom record).level)) →
      Obs unit record uc ctor family Δ S e (.type (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] (.type .record)))
  | function_type : TypeEquality Δ e (.arrow (.atom unit) (.atom unit)) →
      Obs unit record uc ctor family Δ S e (.type (.fn (.atom unit) [] .unit))
  | unit_type : TypeEquality Δ e (.atom unit) → Obs unit record uc ctor family Δ S e (.type .unit)
  | univ : key.Valid unit record → TypeEquality Δ e (.sort (key.control unit record).level) →
      Obs unit record uc ctor family Δ S e (.type (.type key))
  | app : HeterogeneousControl.ControlTyping Δ (.app f a) (result.control unit record) →
      Obs unit record uc ctor family Δ S f (.fn domain keys result) →
      (∀ key ∈ keys, Obs unit record uc ctor family Δ S a key) →
      Obs unit record uc ctor family Δ S (.app f a) result
  | lam : HeterogeneousControl.ControlTyping Δ (.lam A b) ((Key.fn domain keys result).control unit record) →
      TypeEquality Δ A domain → (∀ key ∈ keys, key.control unit record = domain) →
      (∀ key ∈ keys, Obs unit record uc ctor family Δ S A (.type key)) →
      Obs unit record uc ctor family (A :: Δ) (Sets.cons keys S) b result →
      Obs unit record uc ctor family Δ S (.lam A b) (.fn domain keys result)
  | pi : HeterogeneousControl.ControlTyping Δ (.forallE A B) ((Key.type (.fn domain keys result)).control unit record) →
      TypeEquality Δ A domain → (∀ key ∈ keys, key.control unit record = domain) →
      (∀ key ∈ keys, Obs unit record uc ctor family Δ S A (.type key)) →
      Obs unit record uc ctor family (A :: Δ) (Sets.cons keys S) B (.type result) →
      Obs unit record uc ctor family Δ S (.forallE A B) (.type (.fn domain keys result))

/-- Every observation retains its key's fixed ordinary control type. -/
theorem Obs.typing (H : Obs unit record uc ctor family Δ S e key) :
    HeterogeneousControl.ControlTyping Δ e (key.control unit record) := by
  cases H with
  | var HT | unit_ctor HT | record_ctor HT | family HT | app HT | lam HT | pi HT => exact HT
  | unit_type HE | family_type HE | function_type HE => exact HE.typing
  | univ _ HE => exact HE.typing

/-- Function inputs and result keys are compatible with their stored carriers. -/
theorem Obs.valid (H : Obs unit record uc ctor family Δ S e key) : key.Valid unit record := by
  induction H with
  | var _ HK => exact HK
  | unit_ctor | unit_type => simp only [Key.Valid]
  | function_type => simp [Key.Valid]
  | record_ctor | family | family_type => simp [Key.Valid, Key.control]
  | univ HK => simpa only [Key.Valid] using HK
  | app _ _ _ ihf _ =>
    simp only [Key.Valid] at ihf
    exact ihf.2
  | lam _ _ HK _ _ ihA ihb | pi _ _ HK _ _ ihA ihb =>
    simp only [Key.Valid] at ihA ihb ⊢
    exact ⟨fun key hk => ⟨HK key hk, ihA key hk⟩, ihb⟩

/-- Ordinary interpreted renaming transports annotation equalities as well as
all parameter and result demands. -/
theorem Obs.rename (H : Obs unit record uc ctor family Δ S e key)
    (W : ContextSubstitution Δ Δ' σ)
    (hσ : ∀ i key, S i key → ∃ j, σ i = .bvar j ∧ T j key) :
    Obs unit record uc ctor family Δ' T (e.subst σ) key := by
  induction H generalizing Δ' T σ with
  | var HT HK h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using HT.subst W) HK hj :
        Obs unit record uc ctor family Δ' T (.bvar j) _)
  | unit_ctor HT => exact .unit_ctor (HT.subst W)
  | record_ctor HT => exact .record_ctor (HT.subst W)
  | family HT => exact .family (HT.subst W)
  | family_type HE => exact .family_type (HE.subst W)
  | unit_type HE => exact .unit_type (HE.subst W)
  | function_type HE => exact .function_type (HE.subst W)
  | univ HK HE => exact .univ HK (HE.subst W)
  | app HT _ _ ihf iha => exact .app (HT.subst W) (ihf W hσ) (fun key hk => iha key hk W hσ)
  | @lam Δ A b domain keys result S HT HE HK _ _ ihA ihb =>
    refine .lam (HT.subst W) (HE.subst W) HK (fun key hk => ihA key hk W hσ) (ihb W.cons ?_)
    intro i key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i key hi
      exact ⟨j+1, by simp [ProofShape.Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm], hj⟩
  | @pi Δ A B domain keys result S HT HE HK _ _ ihA ihb =>
    refine .pi (HT.subst W) (HE.subst W) HK (fun key hk => ihA key hk W hσ) (ihb W.cons ?_)
    intro i key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i key hi
      exact ⟨j+1, by simp [ProofShape.Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm], hj⟩

/-- A fresh typed binder lifts all existing value and native-type demands. -/
theorem Obs.lift (H : Obs unit record uc ctor family Δ S e key) (SD : DomainSort Δ A u) :
    Obs unit record uc ctor family (A :: Δ) (Sets.cons keys S) (e.liftN 1) key := by
  have R := H.rename (H.typing.weak_interpretation SD)
    (T := Sets.cons keys S) (fun i key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
