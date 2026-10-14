import Lean4Lean.Theory.Typing.Strengthening.EtaParallelDiamond
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaPhase

/-! # Exact confluence of finite typed eta expansion

Single compatible expansions serialize into parallel eta. The exact typed
parallel diamond gives a strip lemma and finite confluence. The common target
requires neither computation nor normal comparison, even with reparameterized
structure roots and converted function domains.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Finite closure of the original parallel eta relation. -/
abbrev EtaParallelRed (Γ : List VExpr) := ReflTransGen (EtaPar Γ)

/-- A single compatible typed expansion is one parallel eta step. -/
theorem TypedEtaStep.toEtaPar (R : TypedEtaStep Γ a b) : EtaPar Γ a b := by
  induction R with
  | root R =>
    cases R with
    | funEta ht => exact .funEta .rfl .rfl ht
    | structEta hi hp hx ht hc => exact .structEta .rfl rfl (fun _ _ _ => .rfl) hi hp hx ht hc
  | appL _ ih => exact .app ih .rfl
  | appR _ ih => exact .app .rfl ih
  | lamL _ ih => exact .lam ih .rfl
  | lamR _ ih => exact .lam .rfl ih
  | forallL _ ih => exact .forallE ih .rfl
  | forallR _ ih => exact .forallE .rfl ih
  | proj _ ih => exact .proj ih

/-- Finite compatible eta can be serialized without changing any endpoint. -/
theorem TypedEtaExpansion.toParallelRed (R : TypedEtaExpansion Γ a b) : EtaParallelRed Γ a b :=
  eta_induct_steps R .rfl (fun R H => H.tail R.toEtaPar)

theorem EtaParallelRed.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (R : EtaParallelRed Γ a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T := by
  induction R with
  | rfl => exact ht
  | tail _ R ih => exact (EtaPar.full hΓ R ih).hasType hΓ ih

/-- The parallel presentation converts back from a typed source. -/
theorem EtaParallelRed.toExpansion (hΓ : OnCtx Γ (env.IsType univs))
    (R : EtaParallelRed Γ a b) (ht : env.HasType univs Γ a T) : TypedEtaExpansion Γ a b := by
  induction R with
  | rfl => exact .refl
  | tail before R ih => exact ih.trans (TypedEtaExpansion.of_etaPar R hΓ (EtaParallelRed.hasType hΓ before ht))

/-- Strip one parallel eta step across a finite eta path. -/
theorem etaPar_strip (hΓ : OnCtx Γ (env.IsType univs)) (R1 : EtaPar Γ a b)
    (R2 : EtaParallelRed Γ a c) (ht : env.HasType univs Γ a T) :
    ∃ out, EtaParallelRed Γ b out ∧ EtaPar Γ c out := by
  induction R2 with
  | rfl => exact ⟨b, .rfl, R1⟩
  | tail before R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, R', HC'⟩ := etaPar_diamond hΓ R HC (EtaParallelRed.hasType hΓ before ht)
    exact ⟨out, HB.tail HC', R'⟩

/-- Exact finite confluence, with source typing propagated to each peak. -/
theorem EtaParallelRed.confluent (hΓ : OnCtx Γ (env.IsType univs))
    (R1 : EtaParallelRed Γ a b) (R2 : EtaParallelRed Γ a c)
    (ht : env.HasType univs Γ a T) :
    ∃ out, EtaParallelRed Γ b out ∧ EtaParallelRed Γ c out := by
  induction R1 with
  | rfl => exact ⟨c, R2, .rfl⟩
  | tail before R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, RB, RC⟩ := etaPar_strip hΓ R HB (EtaParallelRed.hasType hΓ before ht)
    exact ⟨out, RB, HC.tail RC⟩

/-- Arbitrary finite typed eta expansions from one typed source have an exact
common eta expansion. No canonical Eq or proposition-front premise is needed. -/
theorem TypedEtaExpansion.confluent (hΓ : OnCtx Γ (env.IsType univs))
    (R1 : TypedEtaExpansion Γ a b) (R2 : TypedEtaExpansion Γ a c)
    (ht : env.HasType univs Γ a T) :
    ∃ out, TypedEtaExpansion Γ b out ∧ TypedEtaExpansion Γ c out := by
  obtain ⟨out, HB, HC⟩ := EtaParallelRed.confluent hΓ R1.toParallelRed R2.toParallelRed ht
  exact ⟨out, HB.toExpansion hΓ (R1.simAt hΓ _ ht).hasType.2,
    HC.toExpansion hΓ (R2.simAt hΓ _ ht).hasType.2⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
