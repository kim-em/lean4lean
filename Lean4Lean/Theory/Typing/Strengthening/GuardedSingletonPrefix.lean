import Lean4Lean.Theory.Typing.Strengthening.SingletonPrefixArguments
import Lean4Lean.Theory.Typing.Strengthening.ClosedProofIndexUnfolding

/-! # Registered prefix replay from the family guard

The actual generated unfolding check follows from source typing and one
conversion between two already typed family propositions in the opened context.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim
variable {env : VEnv} {data : RecursorData} {S : SingletonLayout} {E : PropElim}

/-- The complete registered unfolding check follows from its one family guard.
All capture typing, major typing and recursor-spine checks are derived here. -/
theorem check_of_family_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env U levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const data.name levels) args))
    (hguard :
      let all := data.openedArguments args
      let ps := all.take data.numParams
      let idx := (all.drop data.indexOffset).take data.numIndices
      env.IsDefEq U (program.domains.reverse ++ Γ)
        (transportedFamily S (data.propParams levels) E ps idx (.bvar 0))
        (mkApps E.family (ps ++ idx)) (.sort .zero)) :
    UnfoldingCheck env U Γ (mkApps (.const data.name levels) args) program := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨name, ls, hfamily, hrigid⟩ := RecursorData.propElim_family_rigid henv H hlarge hzero howner hE
  have hslot := RecursorData.singleton_slot_lt H hlarge hzero howner hS
  obtain ⟨D, lb, rb, tb, X, hgen, hseq, hext, hD, hX, hlb, hio, hrt, hXdef⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  let P := data.propParams levels
  let all := data.openedArguments args
  let ps := all.take data.numParams
  let xs := (all.drop data.numParams).take 2
  let idx := (all.drop data.indexOffset).take data.numIndices
  let Δ := program.domains.reverse ++ Γ
  let fs := (occ S P E ps idx (.bvar 0) S.fields.length).2
  obtain ⟨hctx, hps, hxs, hidx, hall, hprefix, hargs⟩ :=
    registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg ht W
  rw [← hXdef] at hxs hprefix
  change ps.length = P.length at hps
  change xs.length = X.length at hxs
  change idx.length = S.indices.length at hidx
  change all = ps ++ xs ++ idx ++ [.bvar 0] at hall
  have hrec := reconstruction_of_family_conversion henv heq W hctx hfamily hrigid hslot hps hargs hguard
  obtain ⟨hfields, heta⟩ := hrec
  change TelInst env U Δ (P ++ S.fields) (ps ++ fs) at hfields
  change env.IsDefEq U Δ (.bvar 0) (mkApps E.ctor (ps ++ fs)) (mkApps E.family (ps ++ idx)) at heta
  obtain ⟨hbound, hnon, hlv, _, hseq', hbody, hcaplen⟩ := RecursorData.singletonUnfolding_spec hg
  rw [hseq, hgen] at hseq'
  have heqn := (Option.some.inj hseq').symm
  rw [heqn, hext] at hbody
  have hbodyEq := (Option.some.inj hbody).symm
  obtain ⟨S'', E'', hS'', hE'', hdomlen, hctor, hcaps⟩ := RecursorData.singletonUnfolding_layout hg
  cases Option.some.inj (hS''.symm.trans hS)
  cases Option.some.inj (hE''.symm.trans hE)
  change program.constructor = mkApps E.ctor (ps ++ fs) at hctor
  change program.captures = all.take data.indexOffset ++ fs at hcaps
  have htake : all.take data.indexOffset = ps ++ xs := by
    rw [hall, List.append_assoc (ps ++ xs), List.take_left' (by simp [hps, hxs, hX, P, hio])]
  rw [htake] at hcaps
  have hcapT : TelInst env U Δ (D.map (·.instL levels)) program.captures := by
    rw [hcaps, hD]
    have hh := ClosedSingleton.captures_typed hprefix hfields hps hxs W.typed.scope.fields
    simpa only [hX] using hh
  have hflen : fs.length = S.fields.length := (occ_length S P E ps idx (.bvar 0) S.fields.length).2
  have hC := RecursorData.propElim_closed henv H hlarge hzero hS hE
  have hleft : (lb.instL levels).instOuter program.captures =
      .app (mkApps (.const data.name levels)
        (ps ++ xs ++ E.ctorIndices.map (·.instOuter (ps ++ fs)))) (mkApps E.ctor (ps ++ fs)) := by
    rw [hlb, hio, hcaps]
    exact ProofIndexedSingleton.lhs_instOuter W.ctor_closed hC.ctorIndices hps (hxs.trans hX) hflen
  change TelInst env U Δ (P ++ S.indices ++ [majorTy S P E]) (ps ++ idx ++ [.bvar 0]) at hargs
  have hia : TelInst env U Δ (P ++ S.indices) (ps ++ idx) := by
    have hh := hargs.take (doms := P ++ S.indices) (more := [majorTy S P E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using hh
  have hcf := W.major_typed hps (W.literal_args henv hps hfields)
  have hpf := W.family_prop henv hps (W.literal_args henv hps hfields)
  have hconv := (hcf.uniqU henv hctx heta.hasType.2).of_l henv hctx hpf
  have hidxeq : List.Forall₂ (env.IsDefEqU U Δ) idx
      (E.ctorIndices.map (·.instOuter (ps ++ fs))) := by
    apply Lean4Lean.List.forall₂_of_getElem (by simp [hidx, W.ctorIndices_length])
    intro j hj hj'
    have hh := indices_of_family_conversion henv W hctx hfamily hrigid hps hia hconv
      (k := j) (by omega)
    rw [getD_of_lt hj, getD_of_lt (by rw [W.ctorIndices_length]; omega)] at hh
    exact ⟨_, by simpa only [List.getElem_map] using hh⟩
  have hprefixeq : List.Forall₂ (env.IsDefEqU U Δ) (ps ++ xs) (ps ++ xs) :=
    Lean4Lean.List.forall₂_of_getElem rfl fun j hj _ =>
      ⟨_, hprefix.2 j hj (by rw [← hprefix.1]; exact hj)⟩
  have hopenEq : etaOpen program.domains.length (mkApps (.const data.name levels) args) =
      mkApps (.const data.name levels) (ps ++ xs ++ idx ++ [.bvar 0]) := by
    rw [etaOpen_spine, liftN_mkApps]
    simpa only [liftN, ← mkApps_append, hdomlen, all, RecursorData.openedArguments] using
      congrArg (mkApps (.const data.name levels)) hall
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr hnon
  have he := etaOpen_succ (program.domains.length - 1) (mkApps (.const data.name levels) args)
  rw [show program.domains.length - 1 + 1 = program.domains.length by omega, hopenEq,
    mkApps_snoc] at he
  have hfn := (VExpr.app.inj he).1.symm
  have hsource := H.prefixType henv hΓ hw hg ht
  refine ⟨hsource, hnon, ?_, ?_, ?_, ?_, hcaplen, ?_, ?_, ?_⟩
  · rw [heqn]
    exact H.patEquation_of_empty henv (RecursorData.singletonSignature H hlarge hzero).restoration hgen
  · exact (RecursorData.singletonUnfolding_spec hg).2.2.2.2.2.1
  · rwa [hlv]
  · exact (RecursorData.singletonUnfolding_spec hg).2.2.2.1
  · intro j hj hd
    have hh := hcapT.2 j hj (by simpa only [hbodyEq, List.length_map] using hd)
    simp only [List.getElem_map] at hh
    simpa only [hbodyEq, hlv] using hh
  · rw [hctor]
    exact ⟨_, W.family_prop henv hps hargs, heta.hasType.1, heta.hasType.2⟩
  · rw [hbodyEq, hlv, hleft, hfn, hctor, ← mkApps_snoc, ← mkApps_snoc]
    exact ⟨_, _, _, _, _, rfl, rfl, hw, hw,
      Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl),
      (hprefixeq.append' hidxeq).append' (.cons ⟨_, heta.hasType.2⟩ .nil)⟩

/-- Every checked generated prefix has the single family conversion guard.
Thus the new criterion preserves the exact check, rather than restricting it. -/
theorem family_conversion_of_check (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env U levels args = some program)
    (HC : UnfoldingCheck env U Γ (mkApps (.const data.name levels) args) program) :
    let all := data.openedArguments args
    let ps := all.take data.numParams
    let idx := (all.drop data.indexOffset).take data.numIndices
    env.IsDefEq U (program.domains.reverse ++ Γ)
      (transportedFamily S (data.propParams levels) E ps idx (.bvar 0))
      (mkApps E.family (ps ++ idx)) (.sort .zero) := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨name, ls, hfamily, hrigid⟩ := RecursorData.propElim_family_rigid henv H hlarge hzero howner hE
  have hslot := RecursorData.singleton_slot_lt H hlarge hzero howner hS
  obtain ⟨D, lb, rb, tb, X, hgen, hseq, hext, hD, hX, hlb, hio, hrt, hXdef⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  let P := data.propParams levels
  let all := data.openedArguments args
  let ps := all.take data.numParams
  let xs := (all.drop data.numParams).take 2
  let idx := (all.drop data.indexOffset).take data.numIndices
  let Δ := program.domains.reverse ++ Γ
  let fs := (occ S P E ps idx (.bvar 0) S.fields.length).2
  obtain ⟨hctx, hps, hxs, hidx, hall, _, hargs⟩ :=
    registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg ⟨_, HC.source_typed⟩ W
  rw [← hXdef] at hxs
  change ps.length = P.length at hps
  change xs.length = X.length at hxs
  change idx.length = S.indices.length at hidx
  change all = ps ++ xs ++ idx ++ [.bvar 0] at hall
  obtain ⟨_, _, hlv, _, hseq', hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  rw [hseq, hgen] at hseq'
  have heqn := (Option.some.inj hseq').symm
  rw [heqn, hext] at hbody
  have hbodyEq := (Option.some.inj hbody).symm
  obtain ⟨S'', E'', hS'', hE'', _, hctor, hcaps⟩ := RecursorData.singletonUnfolding_layout hg
  cases Option.some.inj (hS''.symm.trans hS)
  cases Option.some.inj (hE''.symm.trans hE)
  change program.constructor = mkApps E.ctor (ps ++ fs) at hctor
  change program.captures = all.take data.indexOffset ++ fs at hcaps
  have htake : all.take data.indexOffset = ps ++ xs := by
    rw [hall, List.append_assoc (ps ++ xs), List.take_left' (by simp [hps, hxs, hX, P, hio])]
  rw [htake] at hcaps
  have hcapT : TelInst env U Δ (D.map (·.instL levels)) program.captures := by
    refine ⟨by simpa only [hbodyEq, List.length_map] using HC.captures_length, ?_⟩
    intro j hj hd
    have hh := HC.captures_typed j hj (by simpa only [hbodyEq, List.length_map] using hd)
    simpa only [hbodyEq, hlv, List.getElem_map] using hh
  rw [hD, hcaps] at hcapT
  have hfields : TelInst env U Δ (P ++ S.fields) (ps ++ fs) := by
    apply TelInst.drop_mid (M := X) (m := xs) ?_ hps hxs W.typed.scope.fields
    simpa only [insertBinders_eq_mapIdx, hX] using hcapT
  obtain ⟨A, hp, hm, hc⟩ := HC.major_prop
  have heta : env.IsDefEq U Δ (.bvar 0) (mkApps E.ctor (ps ++ fs)) (mkApps E.family (ps ++ idx)) := by
    have hh : env.IsDefEqU U Δ (.bvar 0) program.constructor := ⟨_, IsDefEq.proofIrrel hp hm hc⟩
    rw [hctor] at hh
    exact hh.of_l henv hctx (W.major_typed hps hargs)
  exact (reconstruction_iff_family_conversion henv heq W hctx hfamily hrigid hslot hps hargs).1
    ⟨hfields, heta⟩

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
