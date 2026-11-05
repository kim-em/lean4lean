import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypePayload

/-! # Historical control programs with constructor payloads

Ordinary typed substitution transports constructor fields and independent type
histories on higher-order control annotations. This syntax includes arbitrary
applications and lambdas, not only the literal administrative frame grammar.
Full computation preservation is not asserted: constructor-prefix evolution
still requires an operational extension of the payload observation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

namespace ConstructorControlObservation
open PureObservation (Ob Sets)
variable {D : PureObservation.Definitions} {Γ : List VExpr} {origin : ProofShape}
variable {r : Name} {info : VProjectionInfo}

/-- Finite control demands terminate in constructor payloads. Demanded
inputs carry lower data-type histories at their written annotations, even when
the current arguments cannot recover those annotations exactly. -/
inductive Obs (D : PureObservation.Definitions) (Γ : List VExpr) (r : Name) (info : VProjectionInfo) (origin : ProofShape) :
    Nat → List ProofShape → Sets → ProofShape → Ob → Prop where
  | var : S i o → Obs D Γ r info origin n Δ S (.bvar i) o
  | payload : ConstructorTypePayload D Γ r info origin n Δ source →
      Obs D Γ r info origin n Δ S source .pi
  | app : Obs D Γ r info origin n Δ S f (.app keys o) →
      (∀ key ∈ keys, Obs D Γ r info origin n Δ S a key) → Obs D Γ r info origin n Δ S (.app f a) o
  | lam : DomainSort Δ A u →
      (∀ key ∈ keys, LowerTypeDemand D Γ origin key n Δ A) →
      Obs D Γ r info origin (n+1) (A :: Δ) (Sets.cons (fun key => key ∈ keys) S) b o →
      Obs D Γ r info origin n Δ S (.lam A b) (.app keys o)

/-- Renaming transports both the constructor payload and historical annotations. -/
theorem Obs.rename (H : Obs D Γ r info origin n Δ S e o)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → ∃ j, σ i = .bvar j ∧ T j key) :
    Obs D Γ r info origin m Δ' T (e.subst σ) o := by
  induction H generalizing m Δ' T σ with
  | var h => obtain ⟨j, E, hj⟩ := hσ _ _ h; simpa only [ProofShape.subst, E] using Obs.var hj
  | payload h => exact .payload (h.substitute W HT)
  | app _ _ ihf iha => exact .app (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ A u keys n S b o SD HD _ ih =>
    apply Obs.lam (W.sort SD) (fun key hk => (HD key hk).substitute W HT)
    apply ih W.cons HT.lift
    intro i key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i key hi
      exact ⟨j+1, by simp [ProofShape.Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm], hj⟩

/-- Adding one typed control binder preserves the original payload origin. -/
theorem Obs.lift (H : Obs D Γ r info origin n Δ S e o) (SD : DomainSort Δ A u) :
    Obs D Γ r info origin (n+1) (A :: Δ) (Sets.cons Q S) (e.liftN 1) o := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.rename SD.weak_interpretation HT
    (T := Sets.cons Q S) (fun i key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Supplying finite control demands by ordinary typed substitution preserves
the constructor and annotation histories. No image is required to recover an exact native type. -/
theorem Obs.subst (H : Obs D Γ r info origin n Δ S e o)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Obs D Γ r info origin m Δ' T (σ i) key) :
    Obs D Γ r info origin m Δ' T (e.subst σ) o := by
  induction H generalizing m Δ' T σ with
  | var h => exact hσ _ _ h
  | payload h => exact .payload (h.substitute W HT)
  | app _ _ ihf iha => exact .app (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ A u keys n S b o SD HD _ ih =>
    apply Obs.lam (W.sort SD) (fun key hk => (HD key hk).substitute W HT)
    apply ih W.cons HT.lift
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i => exact (hσ i key hi).lift (W.sort SD)

/-- Context conversion transports stored annotations and fixes raw syntax. -/
theorem Obs.context (H : Obs D Γ r info origin n Δ S e o)
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) : Obs D Γ r info origin n Δ' S e o := by
  have HT : FixedTail n n ProofShape.Subst.id := by intro i; rfl
  simpa only [ProofShape.subst_id] using H.rename W HT (fun i key hi => ⟨i, rfl, hi⟩)

/-- An observed control program cannot be a bare projection. Projections in
arbitrary constructor fields are permitted because the fields are opaque. -/
theorem Obs.not_proj (H : Obs D Γ r info origin n Δ S (.proj c j e) o) : False := by
  cases H with
  | payload HP => have E := HP.head; cases E

/-- A literal Pi is type syntax, not an observed constructor control term. -/
theorem Obs.not_forallE (H : Obs D Γ r info origin n Δ S (.forallE A B) o) : False := by
  cases H with
  | payload HP => have E := HP.head; cases E

/-- Root beta discharges the demanded arguments by ordinary substitution,
leaving the historical annotations on all remaining control frames intact. -/
theorem Obs.beta_forward (H : Obs D Γ r info origin n Δ S (.app (.lam A b) a) o)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one a)) :
    Obs D Γ r info origin n Δ S (b.inst a) o := by
  cases H with
  | payload HP => have E := HP.head; cases E
  | app HF HA =>
    cases HF with
    | lam _ _ HB =>
      have HT : FixedTail n n ProofShape.Subst.id := by intro i; rfl
      have R := HB.subst W HT.cons (T := S) (fun i key hi => by
        cases i with
        | zero => exact HA key hi
        | succ i => exact .var hi)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using R

/-- The generated constant frame demands no argument observations. -/
theorem Obs.constant_expansion (H : Obs D Γ r info origin n Δ S e o)
    (SD : DomainSort Δ (.sort (.succ .zero)) (.succ (.succ .zero))) :
    Obs D Γ r info origin n Δ S (constantExpansion e) o :=
  .app (keys := []) (.lam SD (by simp) (H.lift SD)) (by simp)

/-- Control valuations observe the raw lookup type of every demanded variable. -/
def Valuation (D : PureObservation.Definitions) (Γ : List VExpr) (origin : ProofShape)
    (n : Nat) (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i o, S i o → LowerTypeDemand D Γ origin o n Δ (contextOracle Δ i)

/-- A fresh demanded binder extends the valuation by its annotated type
history; older lookup histories lift by ordinary interpreted weakening. -/
theorem Valuation.cons {keys : List Ob} (H : Valuation D Γ origin n Δ S)
    (SD : DomainSort Δ A u) (HD : ∀ key ∈ keys, LowerTypeDemand D Γ origin key n Δ A) :
    Valuation D Γ origin (n+1) (A :: Δ) (Sets.cons (fun key => key ∈ keys) S) := by
  intro i key hi
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have liftDemand {o T} (H : LowerTypeDemand D Γ origin o n Δ T) :
      LowerTypeDemand D Γ origin o (n+1) (A :: Δ) (T.liftN 1) := by
    have R := H.substitute SD.weak_interpretation HT
    simpa only [← subst_bvar_liftN, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using R
  cases i with
  | zero => exact liftDemand (HD key hi)
  | succ i => exact liftDemand (H i key hi)

end ConstructorControlObservation
end Lean4Lean.VEnv.Strengthening
