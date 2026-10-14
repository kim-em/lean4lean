import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
import Lean4Lean.Theory.Typing.Strengthening.ProofShapeRetraction
import Lean4Lean.Theory.Typing.Strengthening.StructureEtaUniverses
import Lean4Lean.Theory.Typing.Strengthening.StructureFamilyArity

/-! # Typed reflection of erased structure eta

Visible fields must be the corresponding projections of the short endpoint;
hidden fields must be proofs. The closed projection-admissibility certificate
is retained, so reconstruction does not assume a deleted context entry exists.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_proj_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Argument comparison may wait until the preceding spine has aligned the two
domains. This handles dependent proof fields without heterogeneous irrelevance. -/
theorem mkApps_common_arguments (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (fun a b => ∀ T, env.HasType univs Γ a T →
      env.HasType univs Γ b T → env.IsDefEqU univs Γ a b) args args')
    (hf : env.IsDefEqU univs Γ f g)
    (ha : VExpr.WF env univs Γ (mkApps f args))
    (hb : VExpr.WF env univs Γ (mkApps g args')) :
    env.IsDefEqU univs Γ (mkApps f args) (mkApps g args') := by
  induction H generalizing f g with
  | nil => exact hf
  | @cons a b args args' h _ ih =>
    obtain ⟨_, _, hF, hA⟩ := (VExpr.WF.of_mkApps henv hΓ (f := .app f a) ha).app_inv henv hΓ
    obtain ⟨_, _, hG, hB⟩ := (VExpr.WF.of_mkApps henv hΓ (f := .app g b) hb).app_inv henv hΓ
    have Hfg := hf.of_l henv hΓ hF
    obtain ⟨⟨_, HD⟩, _⟩ := (hG.uniqU henv hΓ Hfg.hasType.2).forallE_inv henv hΓ
    have hab := h _ hA (HD.defeq hB)
    exact ih ⟨_, IsDefEq.appDF Hfg (hab.of_l henv hΓ hA)⟩ ha hb

/-- A hidden proof field or a visible projection compares at the aligned field
type. Exact erased major reflection supplies the visible case. -/
theorem proofErase_structure_field (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m M) (ha : env.HasType univs Γ a T)
    (hp : env.HasType univs Γ (.proj family i m) T)
    (H : proofErase Γ a = .proof ∨
      proofErase Γ a = .proj family i (proofErase Γ m)) :
    env.IsDefEqU univs Γ a (.proj family i m) := by
  rcases H with H | H
  · obtain ⟨P, haP, hP⟩ := proofErase_eq_proof.1 H
    have hpP := hp.defeqU_r henv hΓ (ha.uniqU henv hΓ haP)
    exact ⟨_, IsDefEq.proofIrrel hP haP hpP⟩
  · obtain ⟨m', rfl, hn, HE⟩ := erase_proj_inv H
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := ha.proj_inv henv hΓ
    have hnm' := not_isProof_major hΓ ha hn
    obtain ⟨_, Hm⟩ := (proofErase_reflect hΓ hm'.hasType.2 hm HE).2 hnm'
    have Hproj := (SimAt.proj henv.orderedStrong hΓ
      (fun T ht => (Hm.defeq hΓ).of_l henv hΓ ht)) _ ha
    exact ⟨_, Hproj⟩

/-- Once the projected constructor is typed, its erased field tests identify
any other constructor at the same family instance. -/
theorem proofErase_structure_spine (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hps : ps.length = info.nparams)
    (hx : info.nindices = 0) (hf : fields.length = info.numFields)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (he : env.HasType univs Γ (mkApps (.const info.ctorName ls) (ps ++ fields))
      (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps))
    (H : ∀ i (h : i < fields.length), proofErase Γ fields[i] = .proof ∨
      proofErase Γ fields[i] = .proj family i (proofErase Γ m)) :
    env.IsDefEqU univs Γ (mkApps (.const info.ctorName ls) (ps ++ fields)) m := by
  have hfields : List.Forall₂ (fun a b => ∀ T, env.HasType univs Γ a T →
      env.HasType univs Γ b T → env.IsDefEqU univs Γ a b)
      fields ((List.range info.numFields).map (fun i => .proj family i m)) := by
    apply Lean4Lean.List.forall₂_of_getElem (by simp [hf])
    intro i hi hi' T ha hb
    simp only [List.getElem_map, List.getElem_range] at hb ⊢
    exact proofErase_structure_field hΓ hm ha hb (H i hi)
  have hparams : List.Forall₂ (fun a b => ∀ T, env.HasType univs Γ a T →
      env.HasType univs Γ b T → env.IsDefEqU univs Γ a b) ps ps :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ _ ht _ => ⟨_, ht⟩)
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, he⟩
  have Hctor := mkApps_common_arguments hΓ (hparams.append' hfields) ⟨_, hhead⟩ ⟨_, he⟩ ⟨_, hexp⟩
  exact Hctor.trans henv hΓ ⟨_, IsDefEq.structEta hi hps hx hm hexp⟩

/-- Saturation and the registered family arity recover the canonical unindexed
family of a constructor, independently of its supplied result type. -/
theorem structure_constructor_family (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hlen : args.length = info.nparams + info.numFields)
    (he : env.HasType univs Γ (mkApps (.const info.ctorName ls) args) T) :
    env.HasType univs Γ (mkApps (.const info.ctorName ls) args)
      (mkApps (.const family ls) (args.take info.nparams)) := by
  obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := hraw.forallArity
  have hshape' : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  have hdomlen : args.length = doms.length := by
    change args.length = info.nparams + (info.ctorType.forallArity - info.nparams) at hlen
    rw [← hctorType, harity] at hlen
    omega
  obtain ⟨_, _, _, _, idx, hres⟩ := VProjectionInfo.ctorApp_typing henv hΓ
    (henv.ordered.projectionConstructor hi) hshape' (by simpa only [hname] using hvalid)
    (by simpa only [hname] using hhead) hnparams huvars (by omega) he hdomlen
  have hl := StructureReplay.family_arity henv hΓ hi (hres.isType henv hΓ)
  have hidx : idx.length = 0 := by
    simp only [List.length_append, List.length_take] at hl
    omega
  have hi0 := List.eq_nil_of_length_eq_zero hidx
  simpa only [hi0, List.append_nil] using hres

namespace ProofShape
/-- A structure head comparison retains its registry, saturation, closed
projection guard and one proof-or-projection check at each field position. -/
inductive StructureEtaHead : ProofShape → ProofShape → Prop where
  | intro {family : Name} {info : VProjectionInfo} {ls : List VLevel}
      {ps fields : List ProofShape} {m : ProofShape}
      (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i (h : i < fields.length), fields[i] = .proof ∨ fields[i] = .proj family i m) :
      StructureEtaHead (mkApps (.const info.ctorName ls) (ps ++ fields)) m
/-- The field tests and closed declaration guard survive arbitrary substitution. -/
theorem StructureEtaHead.subst (H : StructureEtaHead a b) :
    StructureEtaHead (a.subst σ) (b.subst σ) := by
  cases H with
  | intro hi hx hp hf hadm Hfields =>
    simp only [ProofShape.subst_mkApps, List.map_append]
    apply StructureEtaHead.intro hi hx (by simpa only [List.length_map] using hp)
      (by simpa only [List.length_map] using hf) hadm
    intro i hj
    simp only [List.length_map] at hj
    simp only [List.getElem_map]
    rcases Hfields i hj with h | h
    · exact .inl (by rw [h]; rfl)
    · exact .inr (by rw [h]; rfl)

/-- The same head test weakens through block insertion. -/
theorem StructureEtaHead.liftN (H : StructureEtaHead a b) :
    StructureEtaHead (a.liftN n k) (b.liftN n k) := by
  rw [← ProofShape.lift'_consN_skipN, ← ProofShape.lift'_consN_skipN]
  rw [lift'_eq_subst, lift'_eq_subst]
  exact H.subst

/-- Raw retraction reflects head structure eta through inserted variables. -/
theorem StructureEtaHead.of_liftN (H : StructureEtaHead (a.liftN n k) (b.liftN n k)) :
    StructureEtaHead a b :=
  relation_liftN_reflect (fun σ H => H.subst (σ := σ)) H
end ProofShape

/-- A common type and the retained declaration guard justify erased structure
eta at independently typed original endpoints. -/
theorem proofErase_structure_eta_reflect (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hm : env.HasType univs Γ m T)
    (H : ProofShape.StructureEtaHead (proofErase Γ e) (proofErase Γ m)) :
    env.IsDefEq univs Γ e m T := by
  generalize Ee : proofErase Γ e = er at H
  generalize Em : proofErase Γ m = mr at H
  cases H with
  | @intro family info ls ps fields major hi hx hp hf hadm Hfields =>
    obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ee
    let ps₀ := args.take info.nparams
    let fs₀ := args.drop info.nparams
    have Hps : ps₀.map (proofErase Γ) = ps := by
      simp only [ps₀, List.map_take, ← Hargs, ← hp, List.take_left]
    have Hfs : fs₀.map (proofErase Γ) = fields := by
      simp only [fs₀, List.map_drop, ← Hargs, ← hp, List.drop_left]
    have hps : ps₀.length = info.nparams := by simpa only [List.length_map, hp] using congrArg List.length Hps
    have hfs : fs₀.length = info.numFields := by simpa only [List.length_map, hf] using congrArg List.length Hfs
    have Hsplit : args = ps₀ ++ fs₀ := (List.take_append_drop info.nparams args).symm
    rw [Hsplit] at he ⊢
    have hnat := structure_constructor_family hΓ hi hx (by simp [hps, hfs]) he
    rw [List.take_left' hps] at hnat
    have hm' := hm.defeqU_r henv hΓ (he.uniqU henv hΓ hnat)
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hps hx hm').2 hadm
    have HH := proofErase_structure_spine hΓ hi hps hx hfs hm' hnat hexp (by
      intro i hj
      have hj' : i < fields.length := by omega
      have HH := Hfields i hj'
      simpa only [← Hfs, List.getElem_map, ← Em] using HH)
    exact HH.of_l henv hΓ he

/-- Every typed original structure expansion yields identity or the guarded
erased head comparison. The declaration guard is recovered from its typing. -/
theorem proofErase_structure_eta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : ps.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps)) :
    proofErase Γ (structExpand family info ls ps m) = proofErase Γ m ∨
      ProofShape.StructureEtaHead (proofErase Γ (structExpand family info ls ps m)) (proofErase Γ m) := by
  have HE := IsDefEq.structEta hi hp hx hm hexp
  by_cases hproof : IsProof Γ m
  · exact .inl ((proofErase_eq_proof.2 ((isProof_congr hΓ HE).2 hproof)).trans
      (proofErase_eq_proof.2 hproof).symm)
  have hn := mt (isProof_congr hΓ HE).1 hproof
  apply Or.inr
  rw [show structExpand family info ls ps m =
    mkApps (.const info.ctorName ls) (ps ++ (List.range info.numFields).map (fun i => .proj family i m)) from rfl]
  rw [proofErase_const_spine hΓ hexp hn, List.map_append]
  apply ProofShape.StructureEtaHead.intro hi hx (by simp [hp]) (by simp)
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hexp)
  intro i hj
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range]
  by_cases h : IsProof Γ (.proj family i m)
  · exact .inl (proofErase_eq_proof.2 h)
  · exact .inr (if_neg h)

end Lean4Lean.VEnv.Strengthening
