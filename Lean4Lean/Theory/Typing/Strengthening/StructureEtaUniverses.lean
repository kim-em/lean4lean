import Lean4Lean.Theory.Typing.Strengthening.StructureEtaAdmissibility
import Lean4Lean.Theory.Typing.LevelEquiv

/-! # Universe transport for closed structure-eta certificates

Pattern matching forgets constructor levels, while typed structure eta does not.
Closed proof-field certificates respect equivalent well-formed universe lists;
a typed constructor major aligns its actual list with its family's instance.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Pointwise level variants of a well-formed context give actual context
conversion. No context entry is removed. -/
theorem level_context (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : List.Forall₂ (LEquiv U) Γ Δ) : env.IsDefEqCtx U [] Γ Δ := by
  induction H with
  | nil => exact .zero
  | cons h _ ih =>
    obtain ⟨hΓ, u, ht⟩ := hΓ
    exact .succ (ih hΓ) ((h.defeq henv hΓ ⟨_, ht⟩).of_l henv hΓ ht)

/-- Equivalent universe instances preserve the closed proof-field certificate.
The constructor declaration supplies context well-formedness, independently of
any occurrence of the structure. -/
theorem ProofFields.level_congr (henv : env.WF) (hi : env.projections family info)
    (hw : ∀ l ∈ levels, l.WF U) (hw' : ∀ l ∈ levels', l.WF U)
    (hl : levels.length = info.uvars) (he : List.Forall₂ (· ≈ ·) levels levels')
    (H : ProofFields env U info levels) : ProofFields env U info levels' := by
  intro doms result hs hn j hj hp
  have hc := HasType.const (Γ := []) (henv.ordered.projectionConstructor hi) hw hl
  rw [hs, instL_wrapForalls] at hc
  have hctx := (IsType.wrapForalls_inv henv (by trivial)
    (hc.isType henv.ordered (by trivial))).1
  simp only [List.append_nil] at hctx
  have hprefix : OnCtx ((doms.map (instL levels)).take j).reverse (env.IsType U) := by
    have heq : (doms.map (instL levels)).reverse =
        ((doms.map (instL levels)).drop j).reverse ++ ((doms.map (instL levels)).take j).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [heq] at hctx
    exact hctx.of_append
  have hvariants : List.Forall₂ (LEquiv U)
      ((doms.map (instL levels)).take j).reverse
      ((doms.map (instL levels')).take j).reverse := by
    rw [← List.map_take, ← List.map_take, ← List.map_reverse, ← List.map_reverse]
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map]
    exact LEquiv.instL_expr _ hw hw' he
  have hdom := H doms result hs hn j hj hp
  have hd := (LEquiv.instL_expr doms[j] hw hw' he).defeq henv hprefix ⟨_, hdom⟩
  exact (hdom.defeqU_l henv hprefix hd).defeqDFC henv.ordered
    (level_context henv hprefix hvariants)

/-- A saturated typed projection constructor aligns its actual universe levels
with the family instance at which its major is used. -/
theorem constructor_levels (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hi : env.projections family info) (hlen : args.length = info.nparams + info.numFields)
    (H : env.HasType U Γ (mkApps (.const info.ctorName ctorLevels) args)
      (mkApps (.const family levels) params)) :
    (∀ l ∈ ctorLevels, l.WF U) ∧ ctorLevels.length = info.uvars ∧
      (∀ l ∈ levels, l.WF U) ∧ List.Forall₂ (· ≈ ·) ctorLevels levels := by
  obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := hraw.forallArity
  have hshape' : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  have hdomlen : args.length = doms.length := by
    change args.length = info.nparams + (info.ctorType.forallArity - info.nparams) at hlen
    rw [← hctorType, harity] at hlen
    omega
  obtain ⟨hwc, hlc, _, _, idx, hres⟩ := VProjectionInfo.ctorApp_typing henv hΓ
    (henv.ordered.projectionConstructor hi) hshape' (by simpa only [hname] using hvalid)
    (by simpa only [hname] using hhead) hnparams huvars (by omega) H hdomlen
  have ⟨_, hsort⟩ := hres.isType henv.ordered hΓ
  have he := ((hres.uniqU henv hΓ H).structApp_inv henv hΓ hi hsort).1
  obtain ⟨_, htarget⟩ := H.isType henv.ordered hΓ
  obtain ⟨_, _, hw, _⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, htarget⟩).const_inv henv hΓ
  exact ⟨hwc, hlc, hw, he⟩

end Lean4Lean.VEnv.Strengthening.StructureReplay
