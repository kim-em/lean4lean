import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSimultaneous
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # Erasing instantiated recursor templates

A closed typed telescope supplies the simultaneous substitution used by erasure.
The actual captures of a stored recursor rule satisfy that telescope, including
dependent fields and restored constructor parameters.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Substitute a capture list in outermost-first order. -/
def Subst.ofList (args : List ProofShape) : Subst := fun k =>
  if h : k < args.length then args[args.length - 1 - k] else .bvar (k - args.length)

/-- Instantiate an erased template with captures in telescope order. -/
def instOuter (body : ProofShape) (args : List ProofShape) : ProofShape :=
  body.subst (Subst.ofList args)
end ProofShape

variable [Params]

/-- Telescope typing gives exactly the substitution needed by typed erasure. -/
theorem erasedTemplate_substEq (hΔ : OnCtx doms.reverse (env.IsType univs))
    (ha : TelInst env univs Γ doms args) :
    Ctx.SubstEq env univs Γ (VExpr.Subst.ofList args) (VExpr.Subst.ofList args) doms.reverse :=
  substEq_ofTel hΔ ha.1 ha.1 (fun j hj _ hd => ha.2 j hj hd)

/-- Erasure of a closed typed template is instantiated by erasing its captures.
Only in-range variables occur in the source telescope, so there is no condition
on the unused tail of the capture substitution. -/
theorem proofErase_instOuter (hΓ : OnCtx Γ (env.IsType univs))
    (hΔ : OnCtx doms.reverse (env.IsType univs))
    (he : env.HasType univs doms.reverse e T) (ha : TelInst env univs Γ doms args) :
    proofErase Γ (e.instOuter args) =
      (proofErase doms.reverse e).instOuter (args.map (proofErase Γ)) := by
  rw [VExpr.instOuter_eq_subst]
  apply proofErase_subst_with hΓ (erasedTemplate_substEq hΔ ha) he
  intro i A hl _
  have hi : i < args.length := by
    have := hl.lt
    have := ha.1
    simp only [List.length_reverse] at *
    omega
  simp only [VExpr.Subst.ofList, ProofShape.Subst.ofList, List.length_map, dif_pos hi,
    List.getElem_map]

/-- Equal erased captures determine equal erased template results even when
the captures live in different contexts. -/
theorem proofErase_instOuter_congr
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (hΔ : OnCtx doms.reverse (env.IsType univs))
    (he : env.HasType univs doms.reverse e T)
    (ha : TelInst env univs Γ₁ doms args) (hb : TelInst env univs Γ₂ doms args')
    (H : args.map (proofErase Γ₁) = args'.map (proofErase Γ₂)) :
    proofErase Γ₁ (e.instOuter args) = proofErase Γ₂ (e.instOuter args') := by
  rw [proofErase_instOuter hΓ₁ hΔ he ha, proofErase_instOuter hΓ₂ hΔ he hb, H]

/-- Actual recursor captures instantiate the stored rule's closed telescope.
All universe and constructor alignment hypotheses are those of args_typing. -/
theorem erasedTemplate_iota_captures (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams)
    (Hctor : VConstructorShape env ctorName ctorUvars cnparams nfields nindices indName)
    (Hrule : VIotaRuleTyped env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      indLevels nfields df ctorParams)
    (hrigid : env.Rigid indName) (hIL : indLevels.length = ctorUvars)
    (hls : ∀ l ∈ ls, l.WF univs) (hlsl : ls.length = recUvars)
    {pre : List VExpr} (hpre : pre.length = nparams + nmotives + nminors + nindices)
    {major : VExpr}
    (hwf : VExpr.WF env univs Γ (mkApps (.const recName ls) (pre ++ [major])))
    {cls : List VLevel} {P' fields : List VExpr}
    (hcls : cls.length = ctorUvars) (hclsw : ∀ l ∈ cls, l.WF univs)
    (hP' : P'.length = cnparams) (hf : fields.length = nfields)
    (hmajor : env.IsDefEqU univs Γ major (mkApps (.const ctorName cls) (P' ++ fields))) :
    TelInst env univs Γ (Hrule.doms.map (VExpr.instL ls))
      (pre.take (nparams + nmotives + nminors) ++ fields) := by
  refine ⟨?_, Hrule.args_typing henv hΓ Hrec Hctor hrigid hIL hls hlsl hpre hwf
    hcls hclsw hP' hf hmajor⟩
  simp only [List.length_append, List.length_take, List.length_map, Hrule.doms_length, hf]
  omega

/-- A stored recursor RHS body has a uniform erased template at each universe
instance. Its captures may include arbitrary proof-valued fields. -/
theorem proofErase_iota_body
    (Hrule : VIotaRuleTyped env recName recUvars nparams cnparams nmotives nminors nindices ctorName
      ctorLevels nfields df ctorParams)
    (hls : ∀ l ∈ ls, l.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : TelInst env univs Γ (Hrule.doms.map (VExpr.instL ls)) args) :
    proofErase Γ ((Hrule.rhsBody.instL ls).instOuter args) =
      (proofErase (Hrule.doms.map (VExpr.instL ls)).reverse (Hrule.rhsBody.instL ls)).instOuter
        (args.map (proofErase Γ)) := by
  have ⟨hΔ, _, ht⟩ := Hrule.body_typing henv (Γ := []) (by trivial) hls
  simp only [List.append_nil] at hΔ ht
  exact proofErase_instOuter hΓ hΔ ht ha

end Lean4Lean.VEnv.Strengthening
