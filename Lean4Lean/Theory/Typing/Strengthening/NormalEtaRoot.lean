import Lean4Lean.Theory.Typing.Strengthening.EtaStep
import Lean4Lean.Theory.Typing.Strengthening.StructureEtaAdmissibility

/-! # Exchanging normal comparison with a root eta expansion

Function expansion is already represented by normal equality. Structure
expansion is replayed at the left endpoint using its reconstructed family
typing and the right endpoint's closed admissibility certificate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Normally related majors have normally related structure expansions at the
same parameters and levels, whenever the left expansion is typed. -/
theorem normal_structure_congr (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b)
    (ht : env.HasType univs Γ (structExpand family info levels params a) T) :
    NormalEq Γ (structExpand family info levels params a)
      (structExpand family info levels params b) := by
  obtain ⟨_, hhead⟩ := mkApps_head_type hΓ ht
  apply NormalEq.mkApps_spine hΓ (.refl hhead) (ht := ht)
  apply List.forall₂_of_getElem (by simp)
  intro i hi hi'
  obtain ⟨_, harg⟩ := mkApps_arg_type hΓ ht (List.getElem_mem hi)
  by_cases hp : i < params.length
  · simp only [List.getElem_append_left hp] at harg ⊢
    exact .refl harg
  · simp only [List.getElem_append_right (by omega : params.length ≤ i),
      List.getElem_map, List.getElem_range] at harg ⊢
    exact .projDF harg H

/-- A root expansion after normal comparison moves to before it. At a
structure root the exact original family and parameter instance is used on
the left. No front or canonical-Eq assumption is needed. -/
theorem normal_eta_root (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (R : TypedEtaRoot Γ b c) :
    ∃ a', TypedEtaExpansion Γ a a' ∧ NormalEq Γ a' c := by
  cases R with
  | funEta hf =>
    exact ⟨a, .refl, H.trans hΓ (.etaR hf (.refl (HasType.app (hf.weak henv) (.bvar .zero))))⟩
  | structEta hi hp hx hm hc =>
    have hm' := hm.defeqU_l henv hΓ (H.defeq hΓ).symm
    have hz := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc
    have hc' := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm').2 hz
    exact ⟨_, .structEta hi hp hx hm' hc', normal_structure_congr hΓ H hc'⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
