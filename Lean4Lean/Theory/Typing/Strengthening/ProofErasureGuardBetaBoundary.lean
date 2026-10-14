import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixOnly
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbe

/-! # A proof-marker obstruction to untyped guard transport

The marker eta rule can be applied to a raw identity retaining its bound
variable. Beta then exposes a marker/variable mismatch. No computational-root
primitive can repair that mismatch. This is an untyped certificate obstruction;
it does not refute transport from jointly typed original endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
namespace ProofShape

private theorem mkApps_ne_proof : mkApps (.const c ls) args ≠ .proof := by
  induction args using List.snoc_induction with
  | nil => simp [mkApps]
  | snoc args a ih => simp [mkApps_snoc]

private theorem mkApps_ne_bvar : mkApps (.const c ls) args ≠ .bvar i := by
  induction args using List.snoc_induction with
  | nil => simp [mkApps]
  | snoc args a ih => simp [mkApps_snoc]

private theorem mkApps_ne_lam : mkApps (.const c ls) args ≠ .lam A b := by
  induction args using List.snoc_induction with
  | nil => simp [mkApps]
  | snoc args a ih => simp [mkApps_snoc]

variable [Params]

private theorem struct_not_proof (H : StructureEtaHead .proof m) : False := by
  generalize E : ProofShape.proof = e at H
  cases H with | intro => exact mkApps_ne_proof E.symm

private theorem struct_not_bvar (H : StructureEtaHead (.bvar i) m) : False := by
  generalize E : ProofShape.bvar i = e at H
  cases H with | intro => exact mkApps_ne_bvar E.symm

private theorem struct_not_lam (H : StructureEtaHead (.lam A b) m) : False := by
  generalize E : ProofShape.lam A b = e at H
  cases H with | intro => exact mkApps_ne_lam E.symm

omit [Params] in
private theorem proof_fixed (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ComputeFixed Step .proof :=
  (show NormalSyntax Step .proof from ⟨fun _ H => (hroot H).elim, trivial⟩).fixed

omit [Params] in
private theorem bvar_fixed (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ComputeFixed Step (.bvar i) :=
  (show NormalSyntax Step (.bvar i) from ⟨fun _ H => (hroot H).elim, trivial⟩).fixed

private theorem Compare.not_proof_bvar
    (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : Compare Step mode .proof (.bvar i)) : False := by
  generalize EA : ProofShape.proof = a at H
  generalize EB : ProofShape.bvar i = b at H
  induction H with
  | refl => cases EA.trans EB.symm
  | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
  | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | structL H => exact struct_not_proof (EA ▸ H)
  | structR H => exact struct_not_bvar (EB ▸ H)
  | compute RA RB _ ih =>
    exact ih (proof_fixed hroot (EA ▸ RA)).symm (bvar_fixed hroot (EB ▸ RB)).symm
  | sort | const | app | proj | lam | forallE | etaLams => cases EA

/-- A proof marker never compares to a retained variable when primitives have
computational roots. This includes arbitrary finite computation in the guard. -/
theorem RawCheckedCompare.not_proof_bvar
    (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : RawCheckedCompare Step mode .proof (.bvar i)) : False := by
  generalize EA : ProofShape.proof = a at H
  generalize EB : ProofShape.bvar i = b at H
  induction H with
  | base H => exact Compare.not_proof_bvar hroot (EA ▸ EB ▸ H)
  | compute RA RB _ ih =>
    exact ih (proof_fixed hroot (EA ▸ RA)).symm (bvar_fixed hroot (EB ▸ RB)).symm
  | app | proj | lam | lamCommon | forallE => cases EA

namespace GuardBetaBoundary
/-- A raw identity retaining its bound variable. -/
def ident : ProofShape := .lam (.sort .zero) (.bvar 0)
/-- An unchecked marker eta expansion of that identity. -/
def expanded : ProofShape := .lam (.sort .zero) (.app (ident.liftN 1) .proof)
/-- Beta contraction exposes a marker in place of the retained variable. -/
def reduced : ProofShape := .lam (.sort .zero) .proof

omit [Params] in
private theorem reduced_fixed (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ComputeFixed Step reduced := by
  apply NormalSyntax.fixed
  exact ⟨fun _ H => (hroot H).elim,
    ⟨fun _ H => (hroot H).elim, trivial⟩,
    ⟨fun _ H => (hroot H).elim, trivial⟩⟩

omit [Params] in
private theorem ident_fixed (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ComputeFixed Step ident := by
  apply NormalSyntax.fixed
  exact ⟨fun _ H => (hroot H).elim,
    ⟨fun _ H => (hroot H).elim, trivial⟩,
    ⟨fun _ H => (hroot H).elim, trivial⟩⟩

omit [Params] in
private theorem eta_not_reduced (H : EtaHead reduced f) : False := by
  obtain ⟨_, _, E, _⟩ := H.shape
  cases E

omit [Params] in
private theorem eta_not_ident (H : EtaHead ident f) : False := by
  obtain ⟨_, _, E, _⟩ := H.shape
  cases E

private theorem Compare.not_reduced_ident
    (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : Compare Step mode reduced ident) : False := by
  generalize EA : reduced = a at H
  generalize EB : ident = b at H
  induction H with
  | refl => cases EA.trans EB.symm
  | lam HA HB => cases EA; cases EB; exact Compare.not_proof_bvar hroot HB
  | etaL H => exact eta_not_reduced (EA ▸ H)
  | etaR H => exact eta_not_ident (EB ▸ H)
  | structL H => exact struct_not_lam (EA ▸ H)
  | structR H => exact struct_not_lam (EB ▸ H)
  | etaLams _ H =>
    cases EA; cases EB
    exact H.elim eta_not_reduced eta_not_ident
  | compute RA RB _ ih =>
    exact ih (reduced_fixed hroot (EA ▸ RA)).symm (ident_fixed hroot (EB ▸ RB)).symm
  | sort | const | app | proj | forallE => cases EA

/-- The reduct and identity admit no raw checking guard in either mode. -/
theorem not_compare (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ¬ RawCheckedCompare Step mode reduced ident := by
  intro H
  generalize EA : reduced = a at H
  generalize EB : ident = b at H
  induction H with
  | base H => exact Compare.not_reduced_ident hroot (EA ▸ EB ▸ H)
  | lam HA HB => cases EA; cases EB; exact RawCheckedCompare.not_proof_bvar hroot HB
  | lamCommon HB => cases EA; cases EB; exact RawCheckedCompare.not_proof_bvar hroot HB
  | compute RA RB _ ih =>
    exact ih (reduced_fixed hroot (EA ▸ RA)).symm (ident_fixed hroot (EB ▸ RB)).symm
  | app | proj | forallE => cases EA

/-- The unchecked eta guard is accepted before beta contraction. -/
theorem guard : RawCheckedCompare Step true expanded ident := .base (.etaL .proof)

omit [Params] in
/-- A single compatible beta contraction produces the rejected endpoint. -/
theorem beta : BetaRed expanded reduced := by
  apply BetaRed.lam .refl
  simpa [ident, liftN, liftVar, inst] using
    (BetaRed.beta (A := .sort .zero) (b := .bvar 0) (a := .proof))

/-- Forward beta transport of raw checking guards fails for every primitive
relation with computational roots, including the empty primitive relation. -/
theorem no_forward_beta (hroot : ∀ {a b}, Step a b → ComputationalRoot a) :
    ¬ (∀ {a b a'}, RawCheckedCompare Step true a b → BetaRed a a' →
      RawCheckedCompare Step true a' b) := by
  intro H
  exact not_compare hroot (H guard beta)

/-- The accepted raw guard's expanded endpoint has no typed original at all.
Its retained identity requires a proposition as argument, whereas its argument
marker would require that proposition-valued term itself to be a proof. -/
theorem expanded_not_typed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (E : proofErase Γ e = expanded) : False := by
  obtain ⟨A, body, rfl, _, _, EB⟩ := erase_lam_inv E
  obtain ⟨⟨u, hA⟩, _, hbody⟩ := ht.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv EB
  obtain ⟨_, _, hf, hx⟩ := hbody.hasType.1.app_inv henv hΓA
  have EF' : proofErase (A :: Γ) f = .lam (.sort .zero) (.bvar 0) := by
    simpa [ident, liftN, liftVar] using EF
  obtain ⟨D, b, rfl, _, ED, _⟩ := erase_lam_inv EF'
  obtain rfl := erase_sort_inv ED
  obtain ⟨⟨v, hD⟩, _, hb⟩ := hf.lam_inv henv hΓA
  have hx' := argument_at_displayed_domain hΓA hf (HasType.lam hD hb) hx
  exact not_isProof_of_sort hΓA hx' (proofErase_eq_proof.1 EX)

end GuardBetaBoundary
end ProofShape

variable [Params]
/-- Enriched prefix stages still have only computational primitive roots. -/
theorem erased_prefix_K_stage_root : ∀ stage {a b}, ErasedPrefixKStage D stage a b →
    ProofShape.ComputationalRoot a := by
  intro stage
  induction stage with
  | zero => exact erased_compared_K_stage_root 0
  | succ stage ih =>
    intro a b H
    rcases H with H | H | H
    · exact ih H
    · cases H; trivial
    · cases H; trivial

/-- Adding any finite number of prefix/K stages cannot validate unrestricted
raw guard transport. The obstruction requires a typed-source invariant. -/
theorem erased_prefix_K_no_raw_beta_transport :
    ¬ (∀ {a b a'}, ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) true a b →
      ProofShape.BetaRed a a' →
      ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) true a' b) :=
  ProofShape.GuardBetaBoundary.no_forward_beta (erased_prefix_K_stage_root stage)

end Lean4Lean.VEnv.Strengthening
