import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerDomainDemand

/-! # Lambda-domain observations with historical control annotations

Payloads retain a lower domain history. Control lambdas retain recursive
observations of their written annotations, independently of the arguments that
will later supply their finite demands. Ordinary typed substitution transports
these annotations even when their images have lost exact native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A raw sort witness supplies ordinary weakening of every realization of
its context. This does not require a separately observed source term. -/
theorem ProofShape.DomainSort.weak_interpretation (SD : DomainSort Δ A u) :
    ContextSubstitution Δ (A :: Δ) (fun i => ProofShape.bvar (i+1)) := by
  obtain ⟨Γ, A₀, hΓ, rfl, hA, rfl⟩ := SD
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  intro Γ' hΓ' EΓ'
  simpa only [proofEraseCtx, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
    (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one).interpretation hΓ' EΓ'

namespace LambdaDomainObservation
open PureObservation (Ob Sets)
variable {D : PureObservation.Definitions} {Γ : List VExpr} {anchor : ProofShape}

/-- A finite lambda observation distinguishes marked payloads from control
functions. Every demanded control input carries its historical native-type
observation at the written annotation, without asserting native recovery of
the current argument at that annotation. -/
inductive Obs (D : PureObservation.Definitions) (Γ : List VExpr) (anchor : ProofShape) :
    Nat → List ProofShape → Sets → ProofShape → Ob → Prop where
  | var : S i o → Obs D Γ anchor n Δ S (.bvar i) o
  | payload : LowerDomainHistory D Γ anchor n Δ A b →
      Obs D Γ anchor n Δ S (.lam A b) .pi
  | app : Obs D Γ anchor n Δ S f (.app keys o) →
      (∀ key ∈ keys, Obs D Γ anchor n Δ S a key) → Obs D Γ anchor n Δ S (.app f a) o
  | lam : DomainSort Δ A u →
      (∀ key ∈ keys, LowerDomainDemand D Γ anchor key n Δ A) →
      Obs D Γ anchor (n+1) (A :: Δ) (Sets.cons (fun key => key ∈ keys) S) b o →
      Obs D Γ anchor n Δ S (.lam A b) (.app keys o)

/-- Renaming transports both the lower payload and historical annotations. -/
theorem Obs.rename (H : Obs D Γ anchor n Δ S e o)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → ∃ j, σ i = .bvar j ∧ T j key) :
    Obs D Γ anchor m Δ' T (e.subst σ) o := by
  induction H generalizing m Δ' T σ with
  | var h => obtain ⟨j, E, hj⟩ := hσ _ _ h; simpa only [ProofShape.subst, E] using Obs.var hj
  | payload h => exact .payload (lower_domain_history_substitution W HT h)
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

/-- Adding one typed control binder preserves the original payload anchor. -/
theorem Obs.lift (H : Obs D Γ anchor n Δ S e o) (SD : DomainSort Δ A u) :
    Obs D Γ anchor (n+1) (A :: Δ) (Sets.cons Q S) (e.liftN 1) o := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.rename SD.weak_interpretation HT
    (T := Sets.cons Q S) (fun i key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Supplying finite control demands by ordinary typed substitution preserves
the annotation histories. No image is required to recover an exact native type. -/
theorem Obs.subst (H : Obs D Γ anchor n Δ S e o)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Obs D Γ anchor m Δ' T (σ i) key) :
    Obs D Γ anchor m Δ' T (e.subst σ) o := by
  induction H generalizing m Δ' T σ with
  | var h => exact hσ _ _ h
  | payload h => exact .payload (lower_domain_history_substitution W HT h)
  | app _ _ ihf iha => exact .app (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ A u keys n S b o SD HD _ ih =>
    apply Obs.lam (W.sort SD) (fun key hk => (HD key hk).substitute W HT)
    apply ih W.cons HT.lift
    intro i key hi
    cases i with
    | zero => exact .var hi
    | succ i => exact (hσ i key hi).lift (W.sort SD)

/-- Context conversion transports stored annotations and fixes raw syntax. -/
theorem Obs.context (H : Obs D Γ anchor n Δ S e o)
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) : Obs D Γ anchor n Δ' S e o := by
  have HT : FixedTail n n ProofShape.Subst.id := by intro i; rfl
  simpa only [ProofShape.subst_id] using H.rename W HT (fun i key hi => ⟨i, rfl, hi⟩)

/-- Opaque computational heads cannot carry a lambda payload demand. -/
theorem Obs.not_primitiveHead (H : Obs D Γ anchor n Δ S e o) : ¬ PrimitiveHead e := by
  induction H with
  | var | payload | lam => exact id
  | app _ _ ih _ => exact ih

/-- Sorts, projections and Pi syntax do not carry lambda payload demands. -/
theorem Obs.not_sort (H : Obs D Γ anchor n Δ S (.sort u) o) : False := by cases H

/-- A projection is not a lambda-control observation. -/
theorem Obs.not_proj (H : Obs D Γ anchor n Δ S (.proj c i e) o) : False := by cases H

/-- A literal Pi is not a lambda-control observation. -/
theorem Obs.not_forallE (H : Obs D Γ anchor n Δ S (.forallE A B) o) : False := by cases H

/-- Root beta discharges the demanded arguments by ordinary substitution,
leaving the historical annotations on all remaining control frames intact. -/
theorem Obs.beta_forward (H : Obs D Γ anchor n Δ S (.app (.lam A b) a) o)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one a)) :
    Obs D Γ anchor n Δ S (b.inst a) o := by
  cases H with
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
theorem Obs.constant_expansion (H : Obs D Γ anchor n Δ S e o)
    (SD : DomainSort Δ (.sort (.succ .zero)) (.succ (.succ .zero))) :
    Obs D Γ anchor n Δ S (constantExpansion e) o :=
  .app (keys := []) (.lam SD (by simp) (H.lift SD)) (by simp)

/-- Control valuations observe the raw lookup type of every demanded variable. -/
def Valuation (D : PureObservation.Definitions) (Γ : List VExpr) (anchor : ProofShape)
    (n : Nat) (Δ : List ProofShape) (S : Sets) : Prop :=
  ∀ i o, S i o → LowerDomainDemand D Γ anchor o n Δ (contextOracle Δ i)

/-- A fresh demanded binder extends the valuation by its annotated type
history; older lookup histories lift by ordinary interpreted weakening. -/
theorem Valuation.cons {keys : List Ob} (H : Valuation D Γ anchor n Δ S)
    (SD : DomainSort Δ A u) (HD : ∀ key ∈ keys, LowerDomainDemand D Γ anchor key n Δ A) :
    Valuation D Γ anchor (n+1) (A :: Δ) (Sets.cons (fun key => key ∈ keys) S) := by
  intro i key hi
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have liftDemand {o T} (H : LowerDomainDemand D Γ anchor o n Δ T) :
      LowerDomainDemand D Γ anchor o (n+1) (A :: Δ) (T.liftN 1) := by
    have R := H.substitute SD.weak_interpretation HT
    simpa only [← subst_bvar_liftN, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using R
  cases i with
  | zero => exact liftDemand (HD key hi)
  | succ i => exact liftDemand (H i key hi)

end LambdaDomainObservation
end Lean4Lean.VEnv.Strengthening
