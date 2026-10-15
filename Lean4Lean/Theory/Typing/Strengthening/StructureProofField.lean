import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralStructure

/-! # Individual proof fields of a structure

A closed constructor-telescope certificate identifies a proof field independently
of its occurrence parameters and major. At any typed structure expansion the
certificate is equivalent to proofness of that projection, so mixed data/proof
structures need no raw comparisons for their proof fields.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- One field domain is a proposition in the closed specialized constructor
prefix. The certificate contains no occurrence parameters or context entries. -/
def StructureReplay.ProofField (env : VEnv) (U : Nat) (info : VProjectionInfo)
    (ls : List VLevel) (i : Nat) : Prop :=
  ∃ doms result, ∃ (hj : info.nparams + i < doms.length),
    info.ctorType = wrapForalls doms result ∧ doms.length = info.nparams + info.numFields ∧
    env.HasType U ((doms.map (instL ls)).take (info.nparams + i)).reverse
      (doms[info.nparams + i].instL ls) (.sort .zero)

private theorem constructor_field_prop_iff
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls doms result)
    (hlen : args.length = doms.length) (hj : j < doms.length)
    (ht : env.HasType univs Γ (mkApps (.const info.ctorName ls) args) T) :
    env.HasType univs ((doms.map (instL ls)).take j).reverse
      (doms[j].instL ls) (.sort .zero) ↔ IsProof Γ (args[j]'(by omega)) := by
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hctor
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hctor ⟨_, ht⟩ (by simpa using hlen)
  have hfield := hargs j (by omega) (by simpa using hj)
  simp only [List.getElem_map] at hfield
  have hc0 := HasType.const (Γ := []) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hc0
  have hctx := (IsType.wrapForalls_inv henv (by trivial)
    (hc0.isType henv.ordered (by trivial))).1
  simp only [List.append_nil] at hctx
  have hprefix : OnCtx ((doms.map (instL ls)).take j).reverse (env.IsType univs) := by
    have he : (doms.map (instL ls)).reverse =
        ((doms.map (instL ls)).drop j).reverse ++ ((doms.map (instL ls)).take j).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [he] at hctx
    exact hctx.of_append
  have hprior : TelInst env univs Γ ((doms.map (instL ls)).take j) (args.take j) := by
    refine ⟨by simp [hlen], ?_⟩
    intro k hk hk'
    simp only [List.length_take] at hk
    have hh := hargs k (by omega) (by simp; omega)
    simpa only [List.getElem_take, List.getElem_map, List.take_take,
      Nat.min_eq_left (show k ≤ j by omega)] using hh
  constructor
  · intro hprop
    have hinst := HasType.closed_instOuter henv hprefix hprop hprior
    simp only [instOuter_sort] at hinst
    exact ⟨_, hfield, hinst⟩
  · rintro ⟨P, hp, hP⟩
    have hprop := hP.defeqU_l henv hΓ (hp.uniqU henv hΓ hfield)
    have hctx' : OnCtx ((doms.map (instL ls)).reverse ++ []) (env.IsType univs) := by
      simpa only [List.append_nil] using hctx
    obtain ⟨u, hdom⟩ := hctx'.reverse_getElem j (by simpa using hj)
    simp only [List.getElem_map, List.append_nil] at hdom
    have hinst := HasType.closed_instOuter henv hprefix hdom hprior
    simp only [instOuter_sort] at hinst
    have hz := (hinst.uniqU henv hΓ hprop).sort_inv henv hΓ
    obtain ⟨_, hsort⟩ := hdom.isType henv.ordered hprefix
    exact .defeqDF (.sortDF (hsort.sort_inv henv.ordered) trivial hz) hdom

/-- A certified proof field is a proof at every typed projected expansion. -/
theorem StructureReplay.ProofField.projection (H : ProofField env univs info ls i)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams)
    (ht : env.HasType univs Γ (structExpand family info ls ps m) T) :
    IsProof Γ (.proj family i m) := by
  obtain ⟨doms, result, hj, hshape, hlen, hprop⟩ := H
  have hargslen : (ps ++ (List.range info.numFields).map (fun i => VExpr.proj family i m)).length =
      doms.length := by simp [hp, hlen]
  have H := (constructor_field_prop_iff hΓ hi hshape hargslen hj ht).1 hprop
  simpa only [List.getElem_append_right (by omega : ps.length ≤ info.nparams + i), hp,
    Nat.add_sub_cancel_left, List.getElem_map, List.getElem_range] using H

/-- Proofness at one typed projected expansion determines the closed field
certificate. Universe uniqueness, rather than inverse substitution, removes
all dependence on that occurrence's parameters and earlier projections. -/
theorem StructureReplay.ProofField.of_projection
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hj : i < info.numFields)
    (ht : env.HasType univs Γ (structExpand family info ls ps m) T)
    (H : IsProof Γ (.proj family i m)) : ProofField env univs info ls i := by
  obtain ⟨decl, family', ctor, _, _, _, _, _, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := hraw.forallArity
  have hlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hshape' : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  have hargslen : (ps ++ (List.range info.numFields).map (fun i => VExpr.proj family i m)).length =
      doms.length := by simp [hp, hlen]
  refine ⟨doms, result, by omega, hshape', hlen, ?_⟩
  apply (constructor_field_prop_iff hΓ hi hshape' hargslen (by omega) ht).2
  simpa only [List.getElem_append_right (by omega : ps.length ≤ info.nparams + i), hp,
    Nat.add_sub_cancel_left, List.getElem_map, List.getElem_range] using H

/-- A typed structure expansion makes the static field certificate exact. -/
theorem structure_proofField_iff
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hj : i < info.numFields)
    (ht : env.HasType univs Γ (structExpand family info ls ps m) T) :
    StructureReplay.ProofField env univs info ls i ↔ IsProof Γ (.proj family i m) :=
  ⟨fun H => H.projection hΓ hi hp ht, StructureReplay.ProofField.of_projection hΓ hi hp hj ht⟩

end Lean4Lean.VEnv.Strengthening
