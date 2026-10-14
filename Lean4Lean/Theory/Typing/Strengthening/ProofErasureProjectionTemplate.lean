import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplates
import Lean4Lean.Theory.Typing.Strengthening.ProjectionRecoveryTotality
import Lean4Lean.Theory.Typing.Strengthening.ProjectionParameterTyping

/-! # Erased field types from closed constructor templates

Proof-valued earlier fields disappear from the erased template. Their raw images
may therefore remain projections: agreement is required only at retained source
variables. No synthetic proof inhabitant or field-proofness mask is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Raw earlier-field images used by the closed field-type template. -/
def projectionArgs (s : Lean.Name) (ps : List ProofShape) (m : ProofShape) (i : Nat) : List ProofShape :=
  ps ++ (List.range i).map (fun j => .proj s j m)
end ProofShape

variable [Params]

/-- Typed substitution into a closed telescope permits non-erased projection
images for earlier proof fields: those variables do not occur in the template. -/
theorem proofErase_projection_template_subst {doms : List VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ (VExpr.Subst.ofList (ps ++ projsOf s m i))
      (VExpr.Subst.ofList (ps ++ projsOf s m i)) doms.reverse)
    (hF : env.HasType univs doms.reverse F (.sort u))
    (ha : (ps ++ projsOf s m i).length = doms.length) :
    proofErase Γ (F.instOuter (ps ++ projsOf s m i)) =
      (proofErase doms.reverse F).instOuter
        (ProofShape.projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) i) := by
  rw [VExpr.instOuter_eq_subst]
  apply proofErase_subst_with hΓ W hF
  intro j A hl hn
  have hj : j < (ps ++ projsOf s m i).length := by
    have := hl.lt
    have := ha
    simp only [List.length_reverse] at *
    omega
  have hlen : (ProofShape.projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) i).length =
      (ps ++ projsOf s m i).length := by
    simp [ProofShape.projectionArgs, projsOf]
  simp only [VExpr.Subst.ofList, ProofShape.Subst.ofList,
    hlen, dif_pos hj]
  let k := (ps ++ projsOf s m i).length - 1 - j
  have hk : k < (ps ++ projsOf s m i).length := by dsimp [k]; omega
  change proofErase Γ (ps ++ projsOf s m i)[k] =
    (ProofShape.projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) i)[k]
  by_cases hkp : k < ps.length
  · have hkp' : k < (ps.map (proofErase Γ)).length := by simpa using hkp
    simp only [ProofShape.projectionArgs, List.getElem_append_left hkp,
      List.getElem_append_left hkp', List.getElem_map]
  · have hkf : k - ps.length < i := by
      simp only [List.length_append, projsOf, List.length_map, List.length_range] at hk
      omega
    have hnp : ¬ IsProof Γ (.proj s (k - ps.length) m) := by
      have H := mt (isProof_subst hΓ W (HasType.bvar hl)).1 hn
      simp only [VExpr.subst, VExpr.Subst.ofList, dif_pos hj] at H
      change ¬ IsProof Γ ((ps ++ projsOf s m i)[k]) at H
      simpa only [List.getElem_append_right (Nat.le_of_not_gt hkp), projsOf,
        List.getElem_map, List.getElem_range] using H
    have hkp' : (ps.map (proofErase Γ)).length ≤ k := by simp only [List.length_map]; omega
    simp only [ProofShape.projectionArgs,
      List.getElem_append_right (Nat.le_of_not_gt hkp), List.getElem_append_right hkp',
      List.length_map, projsOf,
      List.getElem_map, List.getElem_range]
    exact if_neg hnp

/-- Telescope argument typing supplies the substitution used by the field recipe. -/
theorem proofErase_projection_template
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (hF : env.HasType univs doms.reverse F (.sort u))
    (ha : TelInst env univs Γ doms (ps ++ projsOf s m i)) :
    proofErase Γ (F.instOuter (ps ++ projsOf s m i)) =
      (proofErase doms.reverse F).instOuter
        (ProofShape.projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) i) :=
  proofErase_projection_template_subst hΓ (erasedTemplate_substEq hΔ ha) hF ha.1

omit [Params] in
/-- The two existing outermost-first substitution presentations coincide. -/
theorem projection_argSubst_eq_ofList (args : List VExpr) :
    VExpr.argSubst args = VExpr.Subst.ofList args := by
  funext i
  rw [VExpr.argSubst, VExpr.foldl_cons_apply]
  rfl

/-- Parameters and the preceding primitive projections instantiate the closed
constructor context. Never-zero result universes make every preceding projection
available, even for an indexed major. -/
theorem projection_prefix_subst
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hls : ∀ l ∈ ls, l.WF univs) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero)
    (T : ProjTele env univs s info ls doms result)
    (hps : ArgsTyped env univs Γ (info.ctorType.instL ls) ps tail)
    (hp : ps.length = info.nparams) (hidx : idx.length = info.nindices)
    (hm : env.HasType univs Γ m (mkApps (.const s ls) (ps ++ idx)))
    (hj : info.nparams + j ≤ doms.length) :
    Ctx.SubstEq env univs Γ (VExpr.argSubst (ps ++ projsOf s m j))
      (VExpr.argSubst (ps ++ projsOf s m j)) (doms.take (info.nparams + j)).reverse := by
  obtain ⟨c, levels, args, hresult⟩ := T.head
  have hhead : ∀ (σ : VExpr.Subst) A B, result.subst σ ≠ .forallE A B := by
    rw [hresult]
    intro σ A B
    rw [VExpr.subst_mkApps]
    exact VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) _
  have hshape : info.ctorType.instL ls = (wrapForalls doms result).subst (VExpr.argSubst []) := by
    rw [T.shape]
    exact VExpr.subst_id.symm
  have hps' := hps
  rw [hshape] at hps'
  obtain ⟨_, W₀, _⟩ := ArgsTyped.substEq T.doms hhead ps [] .nil (by simp) hps'
  have hclosed := henv.ordered.closedC (henv.ordered.projectionConstructor hi)
  have hfields := proj_typed henv hΓ hi hclosed hls hlen hnz T hps hp hidx hm
  induction j with
  | zero => simpa only [Nat.add_zero, projsOf, List.range_zero, List.map_nil,
      List.append_nil, List.nil_append, List.length_nil, Nat.zero_add, hp] using W₀
  | succ j ih =>
    have hk : info.nparams + j < doms.length := by omega
    have W := ih (by omega)
    obtain ⟨F, hfield, _, hproj, _⟩ := hfields j (by rw [T.numFields]; omega)
    rw [T.fieldType hlen hp m hk, Option.some.injEq] at hfield
    rw [← hfield] at hproj
    rw [projsOf_succ, ← List.append_assoc,
      show info.nparams + (j + 1) = (info.nparams + j) + 1 by omega,
      List.take_succ_eq_append_getElem hk, List.reverse_append, List.reverse_singleton,
      List.singleton_append, VExpr.argSubst_append_one]
    obtain ⟨u, hdom⟩ := T.doms _ hk
    exact .cons (by rw [VExpr.Subst.cons_tail]; exact W) hdom
      (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact hproj)

/-- Actual field selection has the erased closed-template recipe. Its parameter
and major images determine the output even when earlier fields are proofs. -/
theorem proofErase_projection_field
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hls : ∀ l ∈ ls, l.WF univs) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero)
    (T : ProjTele env univs s info ls doms result)
    (hps : ArgsTyped env univs Γ (info.ctorType.instL ls) ps tail)
    (hp : ps.length = info.nparams) (hidx : idx.length = info.nindices)
    (hm : env.HasType univs Γ m (mkApps (.const s ls) (ps ++ idx)))
    (hj : info.nparams + j < doms.length)
    (hfield : info.fieldType s ls ps j m = some F) :
    proofErase Γ F = (proofErase (doms.take (info.nparams + j)).reverse doms[info.nparams + j]).instOuter
      (ProofShape.projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j) := by
  have W := projection_prefix_subst hΓ hi hls hlen hnz T hps hp hidx hm (Nat.le_of_lt hj)
  rw [projection_argSubst_eq_ofList] at W
  obtain ⟨u, hdom⟩ := T.doms _ hj
  rw [T.fieldType hlen hp m hj, Option.some.injEq] at hfield
  rw [← hfield, projection_argSubst_eq_ofList, ← VExpr.instOuter_eq_subst]
  exact proofErase_projection_template_subst hΓ W hdom (by
    simp only [List.length_append, projsOf, List.length_map, List.length_range,
      List.length_take, hp, Nat.min_eq_left (Nat.le_of_lt hj)])

/-- Source projection typing and any recovered major family supply all dynamic
premises of the erased field recipe. Earlier fields need no separate certificates,
and the major family may have indices or convertible parameter annotations. -/
theorem proofErase_projection_at_recovered_family
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (T : ProjTele env univs s info ls doms result)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (hm : env.HasType univs Γ m (mkApps (.const s ls) args)) :
    ∃ (hj : info.nparams + j < doms.length) (F : VExpr),
      env.HasType univs Γ (.proj s j m) F ∧
      proofErase Γ F = (proofErase (doms.take (info.nparams + j)).reverse doms[info.nparams + j]).instOuter
        (ProofShape.projectionArgs s ((args.take info.nparams).map (proofErase Γ)) (proofErase Γ m) j) := by
  obtain ⟨info₀, ls₀, ps₀, idx₀, sm₀, F₀, u₀, hi₀, hw₀, hl₀, hp₀, hiLen₀,
    hfield₀, hF₀, hm₀, hclosed, hguard⟩ := ht.proj_inv henv hΓ
  obtain rfl := henv.ordered.projections_unique hi₀ hi
  obtain ⟨_, hfamily₀⟩ := hm₀.hasType.2.isType henv hΓ
  obtain ⟨hls, hargs⟩ := (hm₀.hasType.2.uniqU henv hΓ hm).rigidApp_inv
    henv hΓ (henv.projectionRigid hi₀) hfamily₀
  have hlevels : ls.length = info₀.uvars := hls.length_eq.symm.trans hl₀
  have hp : (args.take info₀.nparams).length = info₀.nparams := by
    have hh := hargs.length_eq
    simp only [List.length_append] at hh
    simp only [List.length_take]
    omega
  have hidx : (args.drop info₀.nparams).length = info₀.nindices := by
    have hh := hargs.length_eq
    simp only [List.length_append] at hh
    simp only [List.length_drop]
    omega
  have hnz₀ : (info₀.resultLevel.inst ls₀).IsNeverZero := by
    rcases hguard with hguard | hguard
    · exact hguard
    · have hpj : env.HasType univs Γ (.proj s j m) F₀ :=
        .projDF hi₀ hw₀ hl₀ hp₀ hiLen₀ hfield₀ hF₀ hm₀ hm₀ hclosed (.inr hguard)
      have hFprop : env.HasType univs Γ F₀ (.sort .zero) :=
        (IsDefEq.sortDF (hF₀.sort_r henv hΓ) (by trivial) hguard).defeq hF₀
      exact (hn ⟨F₀, hpj, hFprop⟩).elim
  have hnz : (info₀.resultLevel.inst ls).IsNeverZero :=
    hnz₀.of_equiv (VLevel.inst_congr (by rfl) hls)
  obtain ⟨_, hfamily⟩ := hm.isType henv hΓ
  obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (mkApps (.const s ls) args) from ⟨_, hfamily⟩).of_mkApps henv hΓ
  obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ hhead
  have hm' : env.HasType univs Γ m
      (mkApps (.const s ls) (args.take info₀.nparams ++ args.drop info₀.nparams)) := by
    simpa only [List.take_append_drop] using hm
  obtain ⟨tail, hps⟩ := projection_parameters_typed henv hΓ hi₀ hp hm'
  have hj : info₀.nparams + j < doms.length := by
    have h := ht.proj_index_lt henv hΓ hi₀
    rw [T.numFields] at h
    omega
  obtain ⟨F, hfield, hproj⟩ := projection_at_recovered_family_exists henv hΓ hi₀ ⟨_, ht⟩ hm
  exact ⟨hj, F, hproj, proofErase_projection_field hΓ hi₀ hw hlevels hnz T hps hp hidx hm' hj hfield⟩

end Lean4Lean.VEnv.Strengthening
