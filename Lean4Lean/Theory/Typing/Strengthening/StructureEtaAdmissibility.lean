import Lean4Lean.Theory.Typing.Strengthening.StructureReconstruction
import Lean4Lean.Theory.Typing.ProjectionProofResult

/-! # Recovering structure-eta admissibility from a typed expansion

An actual projection at a source universe which is not never zero has a
proposition as its result type. Applying this to every argument of a typed
structure expansion recovers the closed proof-field certificate. This uses
universe uniqueness after telescope instantiation, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv} {info : VProjectionInfo}

/-- At a source universe which can be zero, every well-typed projection has a
propositional result type. The source need not itself be a proof at this universe
specialization. -/
theorem projection_result_prop (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hi : env.projections family info) (hl : levels.length = info.uvars)
    (hp : params.length = info.nparams) (hx : indices.length = info.nindices)
    (hm : env.HasType U Γ major (mkApps (.const family levels) (params ++ indices)))
    (hn : ¬ (info.resultLevel.inst levels).IsNeverZero)
    (H : env.HasType U Γ (.proj family index major) T) :
    env.HasType U Γ T (.sort .zero) := by
  obtain ⟨info', ls, ps, idx, source, F, u, hi', hw, hl', hp', hx', hf, hF, hs, hc, hg⟩ :=
    HasType.proj_inv henv hΓ H
  obtain rfl := henv.ordered.projections_unique hi hi'
  have hS := HasType.projectionFamily_sort henv hΓ hi hl' hp' hx'
    (let ⟨_, ht⟩ := hs.isType henv.ordered hΓ; ⟨_, ht⟩)
  have hS' := HasType.projectionFamily_sort henv hΓ hi hl hp hx
    (let ⟨_, ht⟩ := hm.isType henv.ordered hΓ; ⟨_, ht⟩)
  have hsame := hS.defeqU_l henv hΓ (hs.hasType.2.uniqU henv hΓ hm)
  have hlevels := (hsame.uniqU henv hΓ hS').sort_inv henv hΓ
  have hz : u ≈ .zero := by
    rcases hg with hg | hg
    · exact (hn (hg.of_equiv hlevels)).elim
    · exact hg
  have hproj : env.HasType U Γ (.proj family index major) F :=
    .projDF hi hw hl' hp' hx' hf hF hs hs hc hg
  have hgiven := hF.defeqU_l henv hΓ (hproj.uniqU henv hΓ H)
  obtain ⟨_, hsort⟩ := hgiven.isType henv.ordered hΓ
  exact .defeqDF (.sortDF (hsort.sort_inv henv.ordered) trivial hz) hgiven

/-- A typed projected constructor at a potentially-zero universe forces every
field domain of its closed telescope to be a proposition. Only the expansion's
typability is used; its type need not be supplied as the major family. -/
theorem proofFields_of_expansion (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType U Γ major (mkApps (.const family levels) params))
    (hn : ¬ (info.resultLevel.inst levels).IsNeverZero)
    (H : VExpr.WF env U Γ (structExpand family info levels params major)) :
    ProofFields env U info levels := by
  let args := params ++ (List.range info.numFields).map (fun j => .proj family j major)
  change VExpr.WF env U Γ (mkApps (.const info.ctorName levels) args) at H
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ H).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  intro doms result hshape hlen j hj hjp
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hctor
  have hal : args.length = doms.length := by simp [args, hp, hlen]
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hctor H (by simpa using hal)
  have hfield := hargs j (by omega) (by simpa using hj)
  simp only [List.getElem_map] at hfield
  have hjf : j - info.nparams < info.numFields := by omega
  have hproj : args[j] = .proj family (j - info.nparams) major := by
    simp only [args, List.getElem_append_right (by omega : params.length ≤ j),
      List.getElem_map, List.getElem_range, hp]
  rw [hproj] at hfield
  have hprop := projection_result_prop (indices := []) henv hΓ hi hl hp (by simpa using hx.symm)
    (by simpa only [List.append_nil] using hm) hn hfield
  have hc0 := HasType.const (Γ := []) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hc0
  have hctx := (IsType.wrapForalls_inv henv (by trivial)
    (hc0.isType henv.ordered (by trivial))).1
  simp only [List.append_nil] at hctx
  have hprefix : OnCtx ((doms.map (instL levels)).take j).reverse (env.IsType U) := by
    have he : (doms.map (instL levels)).reverse =
        ((doms.map (instL levels)).drop j).reverse ++ ((doms.map (instL levels)).take j).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [he] at hctx
    exact hctx.of_append
  have hctx' : OnCtx ((doms.map (instL levels)).reverse ++ []) (env.IsType U) := by
    simpa only [List.append_nil] using hctx
  obtain ⟨u, hdom⟩ := hctx'.reverse_getElem j (by simpa using hj)
  simp only [List.getElem_map, List.append_nil] at hdom
  have hprior : TelInst env U Γ ((doms.map (instL levels)).take j) (args.take j) := by
    refine ⟨by simp [hal], ?_⟩
    intro k hk hk'
    simp only [List.length_take] at hk
    have hh := hargs k (by omega) (by simp; omega)
    simpa only [List.getElem_take, List.getElem_map, List.take_take,
      Nat.min_eq_left (show k ≤ j by omega)] using hh
  have hinst := HasType.closed_instOuter henv hprefix hdom hprior
  simp only [instOuter_sort] at hinst
  have hz := (hinst.uniqU henv hΓ hprop).sort_inv henv hΓ
  obtain ⟨_, hsort⟩ := hdom.isType henv.ordered hprefix
  exact .defeqDF (.sortDF (hsort.sort_inv henv.ordered) trivial hz) hdom

/-- The projection reconstruction criterion is necessary as well as sufficient
for actual unindexed structure expansions. -/
theorem expansion_typed_iff (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType U Γ major (mkApps (.const family levels) params)) :
    env.HasType U Γ (structExpand family info levels params major)
        (mkApps (.const family levels) params) ↔
      (info.resultLevel.inst levels).IsNeverZero ∨ ProofFields env U info levels := by
  constructor
  · intro H
    by_cases hn : (info.resultLevel.inst levels).IsNeverZero
    · exact .inl hn
    · exact .inr (proofFields_of_expansion henv hΓ hi hp hx hm hn ⟨_, H⟩)
  · rintro (hn | hf)
    · exact structure_constructor_neverZero henv hΓ hi hp hx hn hm
    · exact structure_constructor_proofFields henv hΓ hi hp hx hf hm

end Lean4Lean.VEnv.Strengthening.StructureReplay
