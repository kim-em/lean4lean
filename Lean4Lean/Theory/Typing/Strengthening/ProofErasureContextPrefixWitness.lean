import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextComposition
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # Common-typed partial recursors with different motives

These candidates test contextual composition at the prefix before the proof
major. The dependent and constant motives agree at the supplied endpoint, so
both partial recursors have a common type and eta-expand to the same payload.
No noncomparison claim is made in this module.
-/
namespace Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Only full Eq.rec applications compute, with beta-comparison endpoint guards. -/
def Step : ProofShape → ProofShape → Prop := ProofShape.ComparedKPrimitive (fun _ _ => False)

/-- The selected fragment has typed descent under canonical Eq. -/
theorem step_descent (heq : env.HasCanonicalEq) : ErasedPrimitiveDescent Step :=
  erased_compared_K_descent heq (by unfold ErasedPrimitiveDescent; intros; contradiction)

/-- Its endpoint guards and full recursor steps substitute. -/
theorem step_subst (H : Step a b) : Step (a.subst σ) (b.subst σ) :=
  H.subst (by intros; contradiction)

/-- Universe of the selected endpoint. -/
def level : VLevel := .succ (.succ .zero)
/-- A type-valued endpoint whose inhabitant is itself a sort. -/
def point : VExpr := .sort (.succ .zero)
/-- The shared payload of the partial eliminators. -/
def payload : VExpr := .sort .zero
/-- Domain of the proof argument still missing from both prefixes. -/
def proofDomain : VExpr := eqApp (.succ level) (.sort level) point point
/-- The motive returning its variable type endpoint. -/
def dependentMotive : VExpr := castMotive level point
/-- The motive returning the supplied endpoint constantly. -/
def constantMotive : VExpr := constantEqMotive (.succ level) (.sort level) point point
/-- The common type of both motives. -/
def motiveType : VExpr :=
  .forallE (.sort level) (.forallE (eqApp (.succ level) (.sort level) point (.bvar 0)) (.sort level))
/-- The recursor before its final proof argument, with a chosen motive. -/
def partialRec (M : VExpr) : VExpr :=
  mkApps (.const ``Eq.rec [level, .succ level]) [.sort level, point, M, payload, point]
/-- The common function type of the two prefixes. -/
def functionType : VExpr := .forallE proofDomain point
/-- Their shared eta-expanded value. -/
def bridge : VExpr := .lam proofDomain payload

/-- The equality-proof domain is a proposition in every context. -/
theorem proofDomain_typed (heq : env.HasCanonicalEq) :
    env.HasType univs Γ proofDomain (.sort .zero) :=
  HasType.eqApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial))

/-- Both motives have exactly the displayed common motive type. -/
theorem motives_typed (heq : env.HasCanonicalEq) :
    env.HasType univs Γ dependentMotive motiveType ∧
    env.HasType univs Γ constantMotive motiveType := by
  constructor
  · exact HasType.castMotive henv.ordered heq (by trivial) (.sort (by trivial))
  · exact constantEqMotive_typed henv.ordered heq (by trivial)
      (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial))

private theorem prefix_typed (heq : env.HasCanonicalEq)
    (hM : env.HasType univs Γ M motiveType)
    (hminor : env.IsDefEq univs Γ
      (.app (.app M point) (eqReflApp (.succ level) (.sort level) point)) point (.sort level))
    (hresult : env.IsDefEq univs (proofDomain :: Γ)
      (.app (.app M.lift point) (.bvar 0)) point (.sort level)) :
    env.HasType univs Γ (partialRec M) functionType := by
  have hm := hminor.symm.defeq (show env.HasType univs Γ payload point from .sort (by trivial))
  have h4 := HasType.eqRec4 heq (by trivial : level.WF univs)
    (by trivial : (VLevel.succ level).WF univs) (HasType.sort (by trivial))
    (show env.HasType univs Γ point (.sort level) from .sort (by trivial)) hM hm
  have h5 := h4.app (show env.HasType univs Γ point (.sort level) from .sort (by trivial))
  have h5' : env.HasType univs Γ (partialRec M)
      (.forallE proofDomain (.app (.app M.lift point) (.bvar 0))) := by
    simpa [partialRec, proofDomain, mkApps, inst, instVar, eqApp, point, lift, liftN, inst_liftN_lo, inst_lift, liftN_liftN] using h5
  exact (IsDefEq.forallEDF (proofDomain_typed heq) hresult).defeq h5'

/-- The dependent prefix has the constant displayed result type at its supplied
endpoint, even though its motive remains nonconstant before application. -/
theorem dependent_typed (heq : env.HasCanonicalEq) :
    env.HasType univs Γ (partialRec dependentMotive) functionType := by
  apply prefix_typed heq (motives_typed heq).1
  · exact IsDefEq.castMotive_app henv.ordered heq (by trivial)
      (.sort (by trivial)) (.sort (by trivial))
      (HasType.eqReflApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)))
  · have h := IsDefEq.castMotive_app henv.ordered heq (Γ := proofDomain :: Γ)
      (by trivial : level.WF univs)
      (show env.HasType univs (proofDomain :: Γ) point (.sort level) from .sort (by trivial))
      (show env.HasType univs (proofDomain :: Γ) point (.sort level) from .sort (by trivial))
      (show env.HasType univs (proofDomain :: Γ) (.bvar 0) proofDomain from
        by simpa [proofDomain, point, eqApp, lift, liftN] using (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := Γ) (ty := proofDomain))))
    simpa [dependentMotive, castMotive, point, eqApp, lift, liftN] using h

/-- The constant-motive prefix has the same function type. -/
theorem constant_typed (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs Γ (partialRec constantMotive) functionType := by
  apply prefix_typed heq (motives_typed heq).2
  · exact constantEqMotive_app henv heq (by trivial) hΓ
      (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial))
      (HasType.eqReflApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)))
  · have hΓ' : OnCtx (proofDomain :: Γ) (env.IsType univs) := ⟨hΓ, _, proofDomain_typed heq⟩
    have hp : env.HasType univs (proofDomain :: Γ) (.bvar 0) proofDomain := by
      have h : env.HasType univs (proofDomain :: Γ) (.bvar 0) proofDomain.lift := .bvar .zero
      simpa [proofDomain, point, eqApp, lift, liftN] using h
    have h := constantEqMotive_app henv heq (by trivial) hΓ'
      (show env.HasType univs (proofDomain :: Γ) (.sort level) (.sort (.succ level)) from .sort (by trivial))
      (show env.HasType univs (proofDomain :: Γ) point (.sort level) from .sort (by trivial))
      (show env.HasType univs (proofDomain :: Γ) point (.sort level) from .sort (by trivial))
      (show env.HasType univs (proofDomain :: Γ) point (.sort level) from .sort (by trivial)) hp
    simpa [constantMotive, constantEqMotive, point, eqApp, lift, liftN] using h

/-- The shared value has the same type as both prefixes. -/
theorem bridge_typed (heq : env.HasCanonicalEq) :
    env.HasType univs Γ bridge functionType :=
  HasType.lam (proofDomain_typed heq) (.sort (by trivial))

/-- A well-typed partial recursor with these fixed endpoint and payload arguments
compares to the shared lambda after applying the full K step under its binder. -/
theorem partial_bridge (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (partialRec M) functionType) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ bridge) (proofErase Γ (partialRec M)) := by
  have hE := proofDomain_typed (Γ := Γ) heq
  have hΓE : OnCtx (proofDomain :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
  have hp : env.HasType univs (proofDomain :: Γ) (.bvar 0) proofDomain := by
    have h : env.HasType univs (proofDomain :: Γ) (.bvar 0) proofDomain.lift := .bvar .zero
    simpa [proofDomain, point, eqApp, lift, liftN] using h
  have hx := HasType.app (hf.weak henv (B := proofDomain)) hp
  have hs : env.HasType univs (proofDomain :: Γ)
      (eqRecApp level (.succ level) (.sort level) point M.lift payload point (.bvar 0)) point := by
    simpa [partialRec, functionType, proofDomain, mkApps, eqApp, eqRecApp, point, payload,
      lift, liftN, inst] using hx
  have ES := proofErase_const_spine hΓE
    (args := [.sort level, point, M.lift, payload, point, .bvar 0]) hs
    (not_isProof_of_sort hΓE hs)
  change proofErase (proofDomain :: Γ)
    (eqRecApp level (.succ level) (.sort level) point M.lift payload point (.bvar 0)) = _ at ES
  have R : ProofShape.Compute Step
      (proofErase (proofDomain :: Γ)
        (eqRecApp level (.succ level) (.sort level) point M.lift payload point (.bvar 0)))
      (proofErase (proofDomain :: Γ) payload) := by
    rw [ES]
    exact .base (.intro .refl)
  apply proofErase_context_etaL hΓ hE
    (show env.HasType univs (proofDomain :: Γ) payload point from .sort (by trivial)) hf
  have R' : ProofShape.Compute Step
      (proofErase (proofDomain :: Γ) (.app (partialRec M).lift (.bvar 0)))
      (proofErase (proofDomain :: Γ) payload) := by
    simpa [partialRec, mkApps, eqRecApp, point, payload, lift, liftN] using R
  exact .compute .refl R' .refl

/-- Two contextual links have a common-typed original middle. The endpoints
use different motives but each contracts after receiving its proof argument.
Whether the two links compose in this fragment is deliberately left open here. -/
theorem typed_bridge (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs Γ (partialRec dependentMotive) functionType ∧
    env.HasType univs Γ bridge functionType ∧
    env.HasType univs Γ (partialRec constantMotive) functionType ∧
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ bridge) ∧
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ bridge) (proofErase Γ (partialRec constantMotive)) :=
  ⟨dependent_typed heq, bridge_typed heq, constant_typed heq hΓ,
    (partial_bridge heq hΓ (dependent_typed heq)).symm,
    partial_bridge heq hΓ (constant_typed heq hΓ)⟩

end Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
