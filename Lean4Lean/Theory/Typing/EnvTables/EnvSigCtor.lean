import Lean4Lean.Theory.Typing.EnvTables.EnvSigSchema
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.SchemaStructCompat

/-!
# Constructors of the semantic signature of a well-formed environment
-/

namespace Lean4Lean.EnvTables
open InductiveSignature

variable {env : VEnv}

/-- A registered structure is determined by its constructor (through the constructor table). -/
theorem projection_of_ctorName (H : env.WF) (h₁ : env.projections s₁ info₁)
    (h₂ : env.projections s₂ info₂) (hn : info₁.ctorName = info₂.ctorName) :
    s₁ = s₂ ∧ info₁ = info₂ := by
  have e₁ := ctorOf_projection H h₁
  have e₂ := ctorOf_projection H h₂
  rw [hn, e₂] at e₁
  have hs : s₂ = s₁ := (CtorData.mk.inj (Option.some.inj e₁)).1
  subst hs
  exact ⟨rfl, H.ordered.projections_unique h₁ h₂⟩

/-- The applied rule extracted from a generic equation reads the major constructor of the
equation. -/
theorem generates_ctorName {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {rule : CaseSchema.AppliedRule} (hgen : schema.Generates key owner rule)
    (hm : rule.equation.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    rule.application.ctorName = c := by
  obtain ⟨_, _, _, hextract⟩ := hgen
  have hb := (CaseSchema.Generates.body_exact ⟨_, ‹_›, ‹_›, hextract⟩).1
  have ha := CaseSchema.Application.extract_sound (CaseSchema.AppliedRule.extract_spec hextract).2.2.1
  rw [← hb, stripLams_wrapLams', ← ha] at hm
  simp only [CaseSchema.Application.expr, VExpr.stripLams] at hm
  exact (mkApps_const_inj (VExpr.app.inj hm).2).1

theorem ctorOf_shape' (H : env.WF) (h : ctorOf env c = some k) : CtorShape env c k :=
  ctorOf_shape H h

/-! ## The constructor lists of families -/

end Lean4Lean.EnvTables
