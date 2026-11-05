import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaTelescopeSyntax

/-! # Administrative beta cleanup for structure eta under telescopes

Only the supplied lambda prefix contracts. Neither parameters nor the residual
structure major are normalized.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaTelescope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Beta reduction of a major is compatible with its structure expansion,
even when it is copied into several dependent projections. -/
theorem beta_structExpand (R : VExpr.BetaRed a b) :
    VExpr.BetaRed (structExpand family info ls ps a) (structExpand family info ls ps b) := by
  apply VExpr.BetaRed.mkApps .refl
  apply List.Forall₂.append
  · induction ps with
    | nil => exact .nil
    | cons p ps ih => exact .cons .refl ih
  · have H : ∀ js : List Nat, List.Forall₂ VExpr.BetaRed
        (js.map fun j => .proj family j a) (js.map fun j => .proj family j b) := by
      intro js
      induction js with
      | nil => exact .nil
      | cons j js ih => exact .cons (.proj R) ih
    exact H _

/-- Instantiation of a generic structure expansion under a shifted telescope
restores all parameters, including ones depending on the telescope binders. -/
theorem generic_structure_inst (ds : List VExpr) (a : VExpr) :
    (VExpr.wrapLams (liftDomains ds 0)
      (structExpand family info ls (ps.map (·.liftN 1 ds.length))
        (etaOpen ds.length (.bvar 0)))).inst a =
      VExpr.wrapLams ds (structExpand family info ls ps (etaOpen ds.length a)) := by
  rw [VExpr.wrapLams_inst, liftDomains_length, inst_liftDomains, structExpand_inst]
  rw [etaOpen_instN]
  simp [List.map_map, Function.comp_def, VExpr.inst_liftN, VExpr.inst, VExpr.instVar]

/-- A supplied lambda prefix beta-cleans inside every projected field of the
generic structure expansion, at arbitrary finite dependent binder depth. -/
theorem generic_structure_inst_wrapLams_beta (ds : List VExpr) (m : VExpr) :
    VExpr.BetaRed
      ((VExpr.wrapLams (liftDomains ds 0)
        (structExpand family info ls (ps.map (·.liftN 1 ds.length))
          (etaOpen ds.length (.bvar 0)))).inst (VExpr.wrapLams ds m))
      (VExpr.wrapLams ds (structExpand family info ls ps m)) := by
  rw [generic_structure_inst]
  exact beta_wrapLams (beta_structExpand (etaOpen_wrapLams_beta ds m)) ds

end Lean4Lean.VEnv.Strengthening.EtaTelescope
