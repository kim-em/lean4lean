import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorization
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Exact-demand factoring of a native domain template instantiated by its
whole constructor-index prefix. The finite ledger retains the actual original
index-expression observations removed at every parameter. No equality of raw
realizations is used to invent source support for another expression. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Parameters are in telescope order. The tail is factored first; the head
is then cut at its original de Bruijn depth. Original argument observations
remain explicit children of each `InstFootprint`. -/
inductive ParamsFootprint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) :
    List VExpr → Footprint → Footprint → Type where
  | nil (footprint : Footprint) : ParamsFootprint env U registry target locals σ [] footprint footprint
  | cons (tail : ParamsFootprint env U registry target locals σ arguments before middle)
      (head : InstFootprint env U registry target locals σ argument arguments.length middle after) :
      ParamsFootprint env U registry target locals σ (argument :: arguments) before after

private theorem ofList_tail (arguments : List VExpr) (σ : Subst) :
    Subst.lift_l (.skipN .refl arguments.length) ((Subst.ofList arguments).comp σ) = σ := by
  funext i
  simp only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.comp, Subst.ofList]
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel, subst_bvar]

private theorem ofList_cons (argument : VExpr) (arguments : List VExpr) (σ : Subst) :
    ((Subst.one argument).liftN arguments.length).comp ((Subst.ofList arguments).comp σ) =
      (Subst.ofList (argument :: arguments)).comp σ := by
  funext i
  have h := instOuter_eq_subst (.bvar i) (argument :: arguments)
  change ((VExpr.bvar i).inst argument arguments.length).instOuter arguments = _ at h
  rw [instOuter_eq_subst, instN_eq, subst_subst] at h
  simpa only [subst_bvar, Subst.comp, subst_subst] using
    congrArg (fun expression => expression.subst σ) h

/-- Return the original literal template, exact demanded code profile, and
all source operand cuts. Recursive calls are on the finite argument list;
individual cuts recurse only through the supplied original certificate. -/
theorem CodeCert.factorParams
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} {template : VExpr} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (template.instOuter arguments) demand footprint)
    (newLocals : List Nat) :
    ∃ required,
      Nonempty (CodeCert env U registry target newLocals
        ((Subst.ofList arguments).comp σ) template demand required) ∧
      Nonempty (ParamsFootprint env U registry target locals σ arguments footprint required) := by
  induction arguments generalizing template footprint with
  | nil =>
    have identity : (Subst.ofList []).comp σ = σ := by
      funext i
      simp [Subst.ofList, Subst.comp]
    refine ⟨footprint, ?_, ⟨.nil footprint⟩⟩
    rw [identity]
    exact ⟨by simpa [Footprint.sourceLift, Lift.liftVar] using
      certificate.renameSource .refl σ rfl newLocals⟩
  | cons argument arguments ih =>
    obtain ⟨middle, ⟨factored⟩, ⟨tail⟩⟩ := ih certificate
    obtain ⟨required, ⟨result⟩, ⟨head⟩⟩ := factored.factorInst template argument
      arguments.length rfl σ (ofList_tail arguments σ) locals newLocals
    rw [ofList_cons] at result
    exact ⟨required, ⟨result⟩, ⟨.cons tail head⟩⟩

end Lean4Lean.AnchoredSource.Adapted
