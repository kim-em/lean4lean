import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveHeads
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGuardBetaBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta

/-! # Nested function eta is absent from every current raw prefix stage

The well-typed pair `fun x => g (fun y => x y)` and `g` is accepted by recursive
contextual eta. Its raw forms are fixed by every finite prefix stage, but have
no displayed head eta guard. Adding more K/prefix stages cannot supply it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private ProofShape.struct_not_bvar ProofShape.struct_not_lam
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureGuardBetaBoundary
namespace RecursiveEtaBoundary

def argumentType : VExpr := .forallE (.sort .zero) (.sort .zero)
def functionType : VExpr := .forallE argumentType (.sort .zero)
def ctx : List VExpr := [functionType]
def inner : VExpr := .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
def long : VExpr := .lam argumentType (.app (.bvar 1) inner)
def short : VExpr := .bvar 0

def rawArgumentType : ProofShape := .forallE (.sort .zero) (.sort .zero)
def rawInner : ProofShape := .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
def rawLong : ProofShape := .lam rawArgumentType (.app (.bvar 1) rawInner)
def rawShort : ProofShape := .bvar 0

private theorem rawLong_fixed
    (hhead : ∀ {a b}, Step a b → ProofShape.PrimitiveHead a) :
    ProofShape.ComputeFixed Step rawLong := by
  apply ProofShape.NormalSyntax.fixed
  simp only [rawLong, rawInner, rawArgumentType, ProofShape.NormalSyntax]
  repeat' constructor
  all_goals solve
    | (intro out H; exact hhead H)
    | (intro A b H; cases H)

private theorem rawShort_fixed
    (hhead : ∀ {a b}, Step a b → ProofShape.PrimitiveHead a) :
    ProofShape.ComputeFixed Step rawShort :=
  (show ProofShape.NormalSyntax Step rawShort from ⟨fun _ H => hhead H, trivial⟩).fixed

private theorem no_head_eta (H : ProofShape.EtaHead rawLong rawShort) : False := by
  generalize EA : rawLong = a at H
  generalize EB : rawShort = b at H
  cases H <;> subst_vars <;> cases EA

variable [Params]
private theorem compare_impossible
    (hhead : ∀ {a b}, Step a b → ProofShape.PrimitiveHead a)
    (H : ProofShape.Compare Step mode rawLong rawShort) : False := by
  generalize EA : rawLong = a at H
  generalize EB : rawShort = b at H
  induction H with
  | refl => cases EA.trans EB.symm
  | etaL H => exact no_head_eta (EA ▸ EB ▸ H)
  | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | structL H => exact ProofShape.struct_not_lam (EA ▸ H)
  | structR H => exact ProofShape.struct_not_bvar (EB ▸ H)
  | compute RA RB _ ih =>
    exact ih (rawLong_fixed hhead (EA ▸ RA)).symm (rawShort_fixed hhead (EB ▸ RB)).symm
  | sort | const | app | proj | forallE => cases EA
  | lam | etaLams => cases EB

/-- No raw checking certificate recognizes nested eta in either mode, whenever
primitive sources retain a constant or projection head. -/
theorem raw_not_compare
    (hhead : ∀ {a b}, Step a b → ProofShape.PrimitiveHead a) :
    ¬ ProofShape.RawCheckedCompare Step mode rawLong rawShort := by
  intro H
  generalize EA : rawLong = a at H
  generalize EB : rawShort = b at H
  induction H with
  | base H => exact compare_impossible hhead (EA ▸ EB ▸ H)
  | compute RA RB _ ih =>
    exact ih (rawLong_fixed hhead (EA ▸ RA)).symm (rawShort_fixed hhead (EB ▸ RB)).symm
  | app | proj | forallE => cases EA
  | lam | lamCommon => cases EB

/-- The counterexample persists at every enriched K/prefix stage and for every
closed-definition collection, not merely in the beta-only fragment. -/
theorem stages_not_compare :
    ¬ ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) mode rawLong rawShort :=
  raw_not_compare (erased_prefix_K_stage_head stage)

private theorem argumentType_typed : env.HasType univs Γ argumentType (.sort (.succ .zero)) := by
  have H : env.HasType univs Γ argumentType (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (.sort (by trivial)) (.sort (by trivial))
  exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq H

private theorem functionType_typed : env.HasType univs Γ functionType (.sort (.succ .zero)) := by
  have H : env.HasType univs Γ functionType (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE argumentType_typed (.sort (by trivial))
  exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq H

/-- The witness context is well formed in every parameter environment. -/
theorem ctx_wf : OnCtx ctx (env.IsType univs) := ⟨trivial, _, functionType_typed⟩

/-- Both witness endpoints share the same original function type. -/
theorem typings : env.HasType univs ctx long functionType ∧ env.HasType univs ctx short functionType := by
  have hg : env.HasType univs ctx short functionType := by
    simpa [short, ctx, functionType, argumentType, lift, liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := []) (ty := functionType)))
  have hx : env.HasType univs (argumentType :: ctx) (.bvar 0) argumentType := by
    simpa [argumentType, lift, liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := ctx) (ty := argumentType)))
  have hi : env.HasType univs (argumentType :: ctx) inner argumentType := by
    simpa [inner, argumentType, lift, liftN] using (IsDefEq.eta hx).hasType.1
  have hgw : env.HasType univs (argumentType :: ctx) (.bvar 1) functionType := by
    simpa [short, functionType, argumentType, lift, liftN] using (hg.weak henv.ordered (B := argumentType)).hasType.1
  exact ⟨HasType.lam argumentType_typed (HasType.app hgw hi), hg⟩

private theorem sort_erased (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.sort .zero) = .sort .zero :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))

private theorem argumentType_erased (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ argumentType = rawArgumentType := by
  classical
  have hn := not_isProof_of_sort hΓ (argumentType_typed (Γ := Γ))
  change (if IsProof Γ argumentType then _ else _) = _
  have hΓP : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [if_neg hn, sort_erased hΓ, sort_erased hΓP]
  rfl

private theorem etaArgument_one : ProofShape.etaArgument (.succ .zero) = .bvar 0 := by
  unfold ProofShape.etaArgument
  split
  · rename_i H
    have := VLevel.equiv_def.1 H []
    simp [VLevel.eval] at this
  · rfl

/-- Erasure retains every node of both typed endpoints in this example. -/
theorem erasures : proofErase ctx long = rawLong ∧ proofErase ctx short = rawShort := by
  classical
  have hΓ := ctx_wf
  have hΓA : OnCtx (argumentType :: ctx) (env.IsType univs) := ⟨hΓ, _, argumentType_typed⟩
  have hx : env.HasType univs (argumentType :: ctx) (.bvar 0) argumentType := by
    simpa [argumentType, lift, liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := ctx) (ty := argumentType)))
  have hi : env.HasType univs (argumentType :: ctx) inner argumentType := by
    simpa [inner, argumentType, lift, liftN] using (IsDefEq.eta hx).hasType.1
  have hgw : env.HasType univs (argumentType :: ctx) (.bvar 1) functionType := by
    simpa [short, functionType, argumentType, lift, liftN] using
      (typings.2.weak henv.ordered (B := argumentType)).hasType.1
  have hxE : proofErase (argumentType :: ctx) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_function_to_sort hΓA hx)
  have hiE : proofErase (argumentType :: ctx) inner = rawInner := by
    have hn := not_isProof_function_to_sort hΓA hi
    have Hbody := proofErase_eta_body hΓA (HasType.sort (by trivial)) hx
      (not_isProof_function_to_sort hΓA hx)
    rw [hxE, etaArgument_one] at Hbody
    change (if IsProof (argumentType :: ctx) inner then _ else _) = _
    rw [if_neg hn, sort_erased hΓA]
    exact congrArg (ProofShape.lam (.sort .zero)) Hbody
  have hgE : proofErase ctx short = rawShort :=
    if_neg (not_isProof_function_to_sort hΓ typings.2)
  have hgwE : proofErase (argumentType :: ctx) (.bvar 1) = .bvar 1 :=
    if_neg (not_isProof_function_to_sort hΓA hgw)
  have hbody : env.HasType univs (argumentType :: ctx) (.app (.bvar 1) inner) (.sort .zero) :=
    HasType.app hgw hi
  refine ⟨?_, hgE⟩
  have hn := not_isProof_function_to_sort hΓ typings.1
  change (if IsProof ctx long then _ else _) = _
  rw [if_neg hn, argumentType_erased hΓ]
  change ProofShape.lam rawArgumentType
    (if IsProof (argumentType :: ctx) (.app (.bvar 1) inner) then _ else _) = _
  rw [if_neg (not_isProof_of_sort hΓA hbody), hgwE, hiE]
  rfl

/-- Recursive contextual eta recognizes the witness without any computation. -/
theorem contextual : ProofShape.ContextCompare Step (proofEraseCtx ctx) true
    (proofErase ctx long) (proofErase ctx short) := by
  rw [erasures.1, erasures.2]
  have S := ProofShape.DomainSort.of_typed ctx_wf (argumentType_typed (Γ := ctx))
  rw [argumentType_erased ctx_wf] at S
  apply ProofShape.ContextCompare.etaBodyL S
  rw [etaArgument_one]
  apply ProofShape.ContextCompare.app .refl
  exact .base (.base (.etaL (by
    simpa [rawInner, ProofShape.liftN, liftVar] using
      (ProofShape.EtaHead.boundVar (A := .sort .zero) (f := .bvar 0)))))

/-- The original endpoints are definitionally equal by two ordinary typed eta
rules and application/lambda congruence. -/
theorem equality : env.IsDefEq univs ctx long short functionType := by
  have hx : env.HasType univs (argumentType :: ctx) (.bvar 0) argumentType := by
    simpa [argumentType, lift, liftN] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := ctx) (ty := argumentType)))
  have hgw : env.HasType univs (argumentType :: ctx) (.bvar 1) functionType := by
    simpa [short, functionType, argumentType, lift, liftN] using
      (typings.2.weak henv.ordered (B := argumentType)).hasType.1
  have hi : env.IsDefEq univs (argumentType :: ctx) inner (.bvar 0) argumentType := by
    simpa [inner, argumentType, lift, liftN] using IsDefEq.eta hx
  have H := IsDefEq.lamDF (argumentType_typed (Γ := ctx)) (IsDefEq.appDF hgw hi)
  exact H.trans (IsDefEq.eta typings.2)

/-- No finite current K/prefix stage supplies a raw certificate for these
common-typed, definitionally equal endpoints. -/
theorem erased_stages_not_compare :
    ¬ ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) mode
      (proofErase ctx long) (proofErase ctx short) := by
  rw [erasures.1, erasures.2]
  exact stages_not_compare

/-- Even allowing the stage to depend on the derivation cannot make the current
raw guard language complete for typed equality. Recursive eta needs new guard
rules, not additional repetitions of the present computational stages. -/
theorem no_raw_stage_completeness (D : PureObservation.Definitions) :
    ¬ (∀ {Γ a b T}, OnCtx Γ (env.IsType univs) →
      env.IsDefEq univs Γ a b T →
      ∃ stage, ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) true
        (proofErase Γ a) (proofErase Γ b)) := by
  intro H
  obtain ⟨stage, Hstage⟩ := H ctx_wf equality
  exact erased_stages_not_compare Hstage

end RecursiveEtaBoundary
end Lean4Lean.VEnv.Strengthening
