import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionTemplate

/-! # Closed proof masks for dependent structure expansion

A field's proof status is determined by its variable in the closed constructor
telescope. Typed telescope substitution preserves that status, even when later
fields depend on earlier proofs. The resulting raw expansion depends only on
its closed telescope, erased parameters, and erased major premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape Classical
variable [Params]

/-- Typed telescope arguments have exactly the proof status of their source
variables in the closed telescope. No independent field recovery is involved. -/
theorem isProof_telescope_argument
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (H : TelInst env univs Γ doms args) (hj : j < args.length) :
    IsProof Γ args[j] ↔ IsProof doms.reverse (.bvar (doms.length - 1 - j)) := by
  have hlen := H.1
  have hi : doms.length - 1 - j < doms.reverse.length := by simp only [List.length_reverse]; omega
  obtain ⟨A, hl⟩ := Lookup.ofLt hi
  have he : env.HasType univs doms.reverse (.bvar (doms.length - 1 - j)) A := .bvar hl
  have HH := isProof_subst hΓ (erasedTemplate_substEq hΔ H) he
  have hia : doms.length - 1 - j < args.length := by omega
  have Ej : args.length - 1 - (doms.length - 1 - j) = j := by omega
  simpa only [VExpr.subst, VExpr.Subst.ofList, dif_pos hia, Ej] using HH

namespace ProofShape
/-- The field is erased precisely when its closed telescope variable is a
proof. This mask does not depend on the occurrence context or major premise. -/
noncomputable def structureField (doms : List VExpr) (s : Lean.Name) (nparams : Nat)
    (m : ProofShape) (j : Nat) : ProofShape :=
  if IsProof doms.reverse (.bvar (doms.length - 1 - (nparams + j))) then .proof else .proj s j m

/-- Constructor application assembled from native parameters and masked
projections, including nonempty and dependent field telescopes. -/
noncomputable def nativeStructureExpansion (doms : List VExpr) (s : Lean.Name)
    (info : VProjectionInfo) (ls : List VLevel) (ps : List ProofShape) (m : ProofShape) : ProofShape :=
  mkApps (.const info.ctorName ls)
    (ps ++ (List.range info.numFields).map (structureField doms s info.nparams m))

/-- The closed field mask is unchanged by arbitrary raw substitution. -/
theorem structureField_subst : (structureField doms s np m j).subst σ =
    structureField doms s np (m.subst σ) j := by
  unfold structureField
  split <;> rfl

/-- Native structure expansion commutes with arbitrary raw substitution of
its dynamic parameters and major. There are no native-image premises. -/
theorem nativeStructureExpansion_subst : (nativeStructureExpansion doms s info ls ps m).subst σ =
    nativeStructureExpansion doms s info ls (ps.map (·.subst σ)) (m.subst σ) := by
  simp only [nativeStructureExpansion, ProofShape.subst_mkApps, ProofShape.subst,
    List.map_append, List.map_map, Function.comp_def, structureField_subst]

/-- Block insertion likewise leaves the closed mask fixed. -/
theorem nativeStructureExpansion_liftN : (nativeStructureExpansion doms s info ls ps m).liftN n k =
    nativeStructureExpansion doms s info ls (ps.map (·.liftN n k)) (m.liftN n k) := by
  simp only [nativeStructureExpansion, liftN_mkApps, ProofShape.liftN, List.map_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_def]
  unfold structureField
  split <;> rfl
end ProofShape

/-- The closed telescope mask computes the exact erasure of each projected
field in a typed parameter-and-projection instance. Later dependent fields
may refer to earlier proofs; no uniform positivity assumption is imposed. -/
theorem proofErase_structure_field_template
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (H : TelInst env univs Γ doms (ps ++ projsOf s m count))
    (hp : ps.length = np) (hj : j < count) :
    proofErase Γ (.proj s j m) = structureField doms s np (proofErase Γ m) j := by
  have hj' : np + j < (ps ++ projsOf s m count).length := by
    simp only [List.length_append, projsOf, List.length_map, List.length_range, hp]
    omega
  have HH := isProof_telescope_argument hΓ hΔ H hj'
  have E : (ps ++ projsOf s m count)[np + j] = .proj s j m := by
    simp only [List.getElem_append_right (by omega : ps.length ≤ np + j),
      hp, Nat.add_sub_cancel_left, projsOf, List.getElem_map, List.getElem_range]
  rw [E] at HH
  simp only [structureField, proofErase]
  rw [HH]

/-- A typed structure expansion has the exact raw constructor-and-projection
recipe. The closed telescope supplies every field's proof mask, including
proof fields used by later dependent fields. -/
theorem proofErase_structure_expansion_template
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hls : ∀ l ∈ ls, l.WF univs) (hlen : ls.length = info.uvars)
    (hexp : env.HasType univs Γ (structExpand s info ls ps m) (mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ (structExpand s info ls ps m)) :
    proofErase Γ (structExpand s info ls ps m) =
      nativeStructureExpansion doms s info ls (ps.map (proofErase Γ)) (proofErase Γ m) := by
  let args := ps ++ projsOf s m info.numFields
  have hargs : args.length = doms.length := by
    simp only [args, List.length_append, projsOf, List.length_map, List.length_range, hp, hd]
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hls hlen
  rw [T.shape] at hctor
  have HA : TelInst env univs Γ doms args :=
    ⟨hargs, (HasType.mkApps_wrapForalls henv hΓ hctor ⟨_, hexp⟩ hargs).1⟩
  have hΔ : OnCtx doms.reverse (env.IsType univs) := by
    simpa only [List.take_length] using T.ctx doms.length (Nat.le_refl _)
  have E := proofErase_const_spine hΓ hexp hn
  change proofErase Γ (structExpand s info ls ps m) =
    ProofShape.mkApps (.const info.ctorName ls) (args.map (proofErase Γ)) at E
  rw [E]
  simp only [nativeStructureExpansion, args, projsOf, List.map_append, List.map_map]
  apply congrArg (fun fields => ProofShape.mkApps (.const info.ctorName ls) ((ps.map (proofErase Γ)) ++ fields))
  apply List.map_congr_left
  intro j hj
  have hj : j < info.numFields := List.mem_range.1 hj
  exact proofErase_structure_field_template hΓ hΔ HA hp hj

end Lean4Lean.VEnv.Strengthening
