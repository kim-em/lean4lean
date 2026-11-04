import Lean4Lean.Theory.Typing.Strengthening.StructureProofField
import Lean4Lean.Theory.Typing.Strengthening.StructureEtaUniverses

/-! # Universe transport of individual closed proof-field certificates

Equivalent well-formed universe instances preserve each field's proof status,
including conversion of all preceding dependent constructor domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- An individual closed proof field remains a proof field at an equivalent
universe instance. Constructor typing supplies the closed prefix context;
no inverse substitution or strengthening is used. -/
theorem StructureReplay.ProofField.congr_levels
    (hi : env.projections family info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : StructureReplay.ProofField env univs info ls i) :
    StructureReplay.ProofField env univs info ls' i := by
  obtain ⟨doms, result, hj, hshape, hlen, hprop⟩ := H
  refine ⟨doms, result, hj, hshape, hlen, ?_⟩
  have hc := HasType.const (Γ := []) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hc
  have hctx := (IsType.wrapForalls_inv henv (by trivial)
    (hc.isType henv.ordered (by trivial))).1
  simp only [List.append_nil] at hctx
  let j := info.nparams + i
  have hprefix : OnCtx ((doms.map (instL ls)).take j).reverse (env.IsType univs) := by
    have E : (doms.map (instL ls)).reverse =
        ((doms.map (instL ls)).drop j).reverse ++ ((doms.map (instL ls)).take j).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [E] at hctx
    exact hctx.of_append
  have HV : List.Forall₂ (LEquiv univs)
      ((doms.map (instL ls)).take j).reverse ((doms.map (instL ls')).take j).reverse := by
    rw [← List.map_take, ← List.map_take, ← List.map_reverse, ← List.map_reverse]
    apply List.forall₂_of_getElem (by simp)
    intro k hk hk'
    simp only [List.getElem_map]
    exact LEquiv.instL_expr _ hw hw' he
  have HD := (LEquiv.instL_expr doms[j] hw hw' he).defeq henv hprefix ⟨_, hprop⟩
  exact (hprop.defeqU_l henv hprefix HD).defeqDFC henv.ordered
    (StructureReplay.level_context henv hprefix HV)

/-- Static proof status is identical at two equivalent well-formed universe
instances; this preserves exactly which fields a carrier checker may omit. -/
theorem StructureReplay.proofField_congr_levels_iff
    (hi : env.projections family info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls') :
    StructureReplay.ProofField env univs info ls i ↔ StructureReplay.ProofField env univs info ls' i :=
  ⟨fun H => H.congr_levels hi hw hw' hl he,
    fun H => H.congr_levels hi hw' hw (he.length_eq.symm.trans hl) (he.flip.imp (fun _ _ H => H.symm))⟩

/-- A typed structure-family constant supplies well-formed universe arguments
and the constructor's universe arity. The arities agree by the typed constructor
result, rather than by assuming a syntactic equality of stored declarations. -/
theorem StructureReplay.family_instance_levels
    (hi : env.projections family info) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.const family ls) T) :
    (∀ l ∈ ls, l.WF univs) ∧ ls.length = info.uvars := by
  obtain ⟨ci, hc, hw, hl⟩ := ht.const_inv henv hΓ
  obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, _, _, _, _, _, hlookup,
    hwctor, _, Hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hsh, _, _, hhead, _⟩ := Hraw.forallArity
  rw [hsh] at hwctor
  obtain ⟨hdctx, _, hres⟩ := IsType.wrapForalls_inv henv (by trivial) hwctor
  have E : result = mkApps (.const fam.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (mkApps_getAppFnArgs_eq result).symm
  rw [E] at hres
  obtain ⟨_, hci, _, hcount⟩ := (VExpr.WF.of_mkApps henv hdctx ⟨_, hres⟩).const_inv henv hdctx
  rw [hname, hlookup] at hci
  cases hci
  rw [hlookup] at hc
  cases hc
  exact ⟨hw, hl.trans ((by simpa using hcount.symm) : fam.uvars = decl.uvars) |>.trans huvars⟩

end Lean4Lean.VEnv.Strengthening
