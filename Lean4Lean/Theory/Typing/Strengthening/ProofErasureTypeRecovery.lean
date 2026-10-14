import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK
import Lean4Lean.Theory.Typing.Strengthening.TypeRecoveryCore

/-! # Source-typed recovery on proof-erased syntax

Variable types are supplied by an erased context oracle. Application substitutes
the erased argument into the recovered codomain, including proof markers; its
original argument typing is recovered from the supplied source by uniqueness.
There is no rule assigning a type to a standalone proof marker. Projection
recovery and completeness are separate obligations, not assumed here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead

namespace ProofShape
/-- An oracle stores each free variable's type in the current de Bruijn context. -/
abbrev TypeOracle := Nat → ProofShape

/-- Extend the oracle beneath a displayed domain, lifting all stored types. -/
def TypeOracle.cons (σ : TypeOracle) (A : ProofShape) : TypeOracle
  | 0 => A.liftN 1
  | i+1 => (σ i).liftN 1
end ProofShape

variable [Params]

/-- Only actual variable lookups constrain a valid oracle. Entries beyond the
context length carry no typing assertion and cannot be used at a typed source. -/
def ErasedOracleValid (Γ : List VExpr) (σ : ProofShape.TypeOracle) : Prop :=
  ∀ {i A}, Lookup Γ i A → σ i = proofErase Γ A

/-- Valid erased variable types extend beneath each typed original domain. -/
theorem ErasedOracleValid.cons (H : ErasedOracleValid Γ σ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ErasedOracleValid (A :: Γ) (σ.cons (proofErase Γ A)) := by
  intro i T hl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  cases hl with
  | zero => exact (proofErase_liftN hΓ hΓA Ctx.LiftN.one hA).symm
  | succ hl =>
    obtain ⟨_, hT⟩ := IsType.lookup henv hΓ hl
    simp only [ProofShape.TypeOracle.cons, H hl]
    exact (proofErase_liftN hΓ hΓA Ctx.LiftN.one hT).symm

/-- Erase the types in a context while retaining their binding structure. -/
noncomputable def erasedTypeOracle : List VExpr → ProofShape.TypeOracle
  | [] => fun _ => .proof
  | A :: Γ => (erasedTypeOracle Γ).cons (proofErase Γ A)

/-- Every well-formed context supplies a valid oracle. -/
theorem erasedTypeOracle_valid (hΓ : OnCtx Γ (env.IsType univs)) :
    ErasedOracleValid Γ (erasedTypeOracle Γ) := by
  induction Γ with
  | nil => intro i A hl; cases hl
  | cons A Γ ih =>
    obtain ⟨hΓ, u, hA⟩ := hΓ
    exact ErasedOracleValid.cons (ih hΓ) hΓ hA

namespace ProofShape
/-- Finite recovery from retained syntax, declared types and computation on
recovered types. Source typing is used at replay, never invented for markers. -/
inductive TypeRecovery (Step : ProofShape → ProofShape → Prop) :
    TypeOracle → ProofShape → ProofShape → Prop where
  | bvar : TypeRecovery Step σ (.bvar i) (σ i)
  | sort : u.WF univs → TypeRecovery Step σ (.sort u) (.sort (.succ u))
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
      TypeRecovery Step σ (.const c ls) (proofErase [] (ci.type.instL ls))
  | lam : TypeRecovery Step (σ.cons A) b B →
      TypeRecovery Step σ (.lam A b) (.forallE A B)
  | app : TypeRecovery Step σ f (.forallE A B) →
      TypeRecovery Step σ (.app f a) (B.inst a)
  | forallE : TypeRecovery Step σ A (.sort u) →
      TypeRecovery Step (σ.cons A) B (.sort v) →
      TypeRecovery Step σ (.forallE A B) (.sort (.imax u v))
  | convert : TypeRecovery Step σ e T → Compute Step T T' → TypeRecovery Step σ e T'
end ProofShape

/-- Recovery at an erased source reconstructs an original result type and a
typing of that source. In particular, application can safely substitute a marker
because its typed original argument is still available. -/
theorem proofErase_typeRecovery_replay (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hσ : ErasedOracleValid Γ σ)
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step σ (proofErase Γ e) out) :
    ∃ A, env.HasType univs Γ e A ∧ proofErase Γ A = out := by
  generalize Ee : proofErase Γ e = source at R
  induction R generalizing Γ e T with
  | bvar =>
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    exact ⟨A, .bvar hl, (hσ hl).symm⟩
  | sort hu =>
    obtain rfl := erase_sort_inv Ee
    refine ⟨_, .sort hu, ?_⟩
    exact if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))
  | const hc hw hn =>
    obtain rfl := erase_const_inv Ee
    have hc0 := HasType.const (Γ := []) hc hw hn
    obtain ⟨_, hT⟩ := hc0.isType henv (by trivial)
    exact ⟨_, .const hc hw hn,
      proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ⟩
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨B, hB, EB⟩ := ih hΓA (EA ▸ hσ.cons hΓ hA) hb Eb
    refine ⟨.forallE A B, .lam hA hB, ?_⟩
    obtain ⟨_, hPi⟩ := (HasType.lam hA hB).isType henv hΓ
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPi), EA, EB]
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨F, hfF, EF⟩ := ih hΓ hσ hf Ef
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv EF
    obtain ⟨⟨_, hCA⟩, _⟩ := (hf.uniqU henv hΓ hfF).forallE_inv henv hΓ
    have haA := hCA.defeq ha
    obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfF.isType henv hΓ).forallE_inv henv
    refine ⟨B.inst a, .app hfF haA, ?_⟩
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    rw [proofErase_instN hΓA haA Ctx.InstN.zero hB, EB, Ea]
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨S, hAu, ES⟩ := ihA hΓ hσ hA EA
    obtain rfl := erase_sort_inv ES
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hAu⟩
    obtain ⟨S, hBv, ES⟩ := ihB hΓA (EA ▸ hσ.cons hΓ hAu) hB EB
    obtain rfl := erase_sort_inv ES
    refine ⟨_, .forallE hAu hBv, ?_⟩
    exact if_neg (not_isProof_of_sort hΓ
      (HasType.sort (l := .imax _ _) ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩))
  | convert _ RC ih =>
    obtain ⟨A, heA, EA⟩ := ih hΓ hσ ht Ee
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A', HAA, EA'⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hA
      (by simpa only [ProofShape.liftN_zero, EA] using RC)
    exact ⟨A', HAA.defeq heA, by simpa only [ProofShape.liftN_zero] using EA'⟩

end Lean4Lean.VEnv.Strengthening
