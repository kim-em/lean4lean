import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierJoinedSubstitution

/-! # A neutral-application obstruction to full carrier paired substitution

Two neutral empty-structure arguments have a carrier comparison, but a neutral
function into Prop exposes those arguments in ordinary application checking.
Neither computation nor the recursive function-carrier rule repairs this: the
outputs have a literal universe carrier. This refutes full paired closure of
the current carrier language, not strengthening or joined paired substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-- A variable applied to a variable is fixed by every current scoped stage. -/
theorem ProofShape.ScopedCompute.bvar_app_fixed
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.app (.bvar f) (.bvar i)) out) :
    out = .app (.bvar f) (.bvar i) :=
  scoped_normal_fixed R (fun _ => ⟨fun _ H => hhead H,
    (fun _ _ H => nomatch H), ⟨fun _ H => hhead H, trivial⟩,
    ⟨fun _ H => hhead H, trivial⟩⟩)

variable [Params]
/-- Ordinary application checking cannot use a carrier comparison of distinct
variable arguments, even with arbitrarily many singleton computation stages. -/
theorem ProofShape.ScopedCompare.bvar_app_argument_injective
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode (.app (.bvar f) (.bvar i)) (.app (.bvar g) (.bvar j))) :
    i = j := by
  generalize EA : ProofShape.app (.bvar f) (.bvar i) = a at H
  generalize EB : ProofShape.app (.bvar g) (.bvar j) = b at H
  induction H generalizing f g i j with
  | leaf H =>
    cases H with
    | refl => exact ProofShape.bvar.inj (ProofShape.app.inj (EA.trans EB.symm)).2
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | app Hf Hx => cases EA; cases EB; exact Hx.bvar_injective hhead
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).bvar_app_fixed hhead).symm ((EB ▸ RB).bvar_app_fixed hhead).symm
  | symm H ih => exact (ih EB EA).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases EB
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA

/-- The unrestricted carrier version of finite paired instantiation. This law
is refuted below: arbitrary carrier-compared arguments need not have a literal
join, and the output language still checks neutral applications syntactically. -/
def CarrierFinitePairedInstantiation
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ A b b' B x y}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) b' B →
    env.HasType univs Γ x A → env.HasType univs Γ y A →
    StructureCarrierGuard (Stages 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) b') →
    StructureCarrierGuard (Stages 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y) →
    ∃ stage, StructureCarrierGuard (Stages stage) (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y))

/-- A registered positive empty structure refutes full carrier paired closure.
The witness is the body f z in a context containing f : S → Prop and two S
variables. Both inputs have stage-zero carrier guards; no finite output stage
has a carrier guard. The environment may have canonical Eq. -/
theorem not_carrier_finite_paired
    (hhead : ∀ stage {Δ a b}, Stages stage Δ a b → PrimitiveHead a)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ¬ CarrierFinitePairedInstantiation Stages := by
  intro Hinst
  let S := VExpr.const family ls
  let F := VExpr.forallE S (.sort .zero)
  let Γ := [S, S, F]
  have hF : env.HasType univs [] F (.sort (.imax (.succ u) (.succ .zero))) :=
    HasType.forallE hS (HasType.sort (by trivial))
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hF⟩, _, hS.weak0 henv.ordered⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hfun : env.HasType univs Γ (.bvar 2) F := .bvar (.succ (.succ .zero))
  have hfun' : env.HasType univs (S :: Γ) (.bvar 3) F :=
    .bvar (.succ (.succ (.succ .zero)))
  have hbody : env.HasType univs (S :: Γ) (.app (.bvar 3) (.bvar 0)) (.sort .zero) :=
    hfun'.app (HasType.bvar .zero)
  have HB : StructureCarrierGuard (Stages 0) (proofEraseCtx (S :: Γ))
      (proofErase (S :: Γ) (.sort .zero))
      (proofErase (S :: Γ) (.app (.bvar 3) (.bvar 0)))
      (proofErase (S :: Γ) (.app (.bvar 3) (.bvar 0))) := .checked .refl
  have HX : StructureCarrierGuard (Stages 0) (proofEraseCtx Γ)
      (proofErase Γ S) (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
    rw [show proofErase Γ S = .const family ls from if_neg (not_isProof_of_sort hΓ hSΓ)]
    exact .subsingleton (.unit hi hx hf (ps := []) hp.symm)
  obtain ⟨stage, H⟩ := Hinst hΓS hbody hbody h₀ h₁ HB HX
  change StructureCarrierGuard (Stages stage) (proofEraseCtx Γ)
    (proofErase Γ (.sort .zero))
    (proofErase Γ (.app (.bvar 2) (.bvar 0)))
    (proofErase Γ (.app (.bvar 2) (.bvar 1))) at H
  have Eprop : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  rw [Eprop] at H
  have Hcheck := H.sort_checked (hhead stage)
  have hleft : env.HasType univs Γ (.app (.bvar 2) (.bvar 0)) (.sort .zero) := hfun.app h₀
  have hright : env.HasType univs Γ (.app (.bvar 2) (.bvar 1)) (.sort .zero) := hfun.app h₁
  have hnfun := not_isProof_fn hΓ hfun h₀ (not_isProof_of_sort hΓ hleft)
  rw [show proofErase Γ (.app (.bvar 2) (.bvar 0)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hleft),
    show proofErase Γ (.app (.bvar 2) (.bvar 1)) = .app _ _ from if_neg (not_isProof_of_sort hΓ hright),
    show proofErase Γ (.bvar 2) = .bvar 2 from if_neg hnfun,
    show proofErase Γ (.bvar 0) = .bvar 0 from if_neg (not_proof_at_positive_type hΓ hSΓ h₀),
    show proofErase Γ (.bvar 1) = .bvar 1 from if_neg (not_proof_at_positive_type hΓ hSΓ h₁)] at Hcheck
  have Hbad := Hcheck.bvar_app_argument_injective (hhead stage)
  cases Hbad

/-- The obstruction persists at every actual structure/function singleton
stage; adding further stages cannot change the neutral application heads. -/
theorem not_structure_singleton_carrier_finite_paired
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ¬ CarrierFinitePairedInstantiation (ErasedStructureSingletonStage D) :=
  not_carrier_finite_paired erased_structure_singleton_stage_head hi hp hx hf hS

end Lean4Lean.VEnv.Strengthening
