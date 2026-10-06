import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.NativeRegistryInstallation
import Lean4Lean.Theory.Typing.QuotPatternTyping

/-! The major family of a registered native recursor owning a constructor is
a rigid constant. The proof traces an installed native equation of that
owner, whose constructor returns the family. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

private theorem install_base_le' (H : VInductBlock.install base block = some installed) :
    base ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
    VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

theorem NativeRecursorRegistered.family_head_rigid {data : NativeRecursorData} (henv : env.WF)
    (H : NativeRecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size)
    {owner : Fin data.schema.signature.families.size}
    (hown : data.schema.signature.constructors[index].owner = owner) :
    (∃ ci, env.constants
      (data.schema.restoration.headName data.schema.signature.families[owner].name) =
        some ci) ∧
    env.Rigid (data.schema.restoration.headName data.schema.signature.families[owner].name) := by
  subst hown
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, _, _, _, hi, he⟩ := H
  have hle : base ≤ env := hbase.trans ((install_base_le' hi).trans he)
  rw [hr]
  rcases hdata.family_head_origin hprior index with
    ⟨family, hsrc, hfn, hhn, fc, hfc, hcn⟩ |
    ⟨cctor, equation, hdefeq, hmaj, hconst, ls, hres⟩
  · rw [hfn, hhn]
    have hgenerated : g.equation index ∈ g.equations :=
      List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
    obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (List.mapM_eq_some.mp hdata.equations) _ hgenerated
    have hmajor := Instance.restored_equation_major hdata index hrestore
    rw [hcn] at hmajor
    have hdf : env.defeqs actual := he.defeqs (VInductBlock.install_rule hi hmem)
    obtain ⟨ci, hci, F, ls', hF, ⟨ciF, hciF⟩, hFr⟩ :=
      henv.native_constructor_result_rigid hdf hmajor
    have hfcc : fc ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨family, hsrc, hfc⟩
    have hconst : env.constants fc.name = some fc.toVConstant :=
      he.constants (VInductBlock.install_ctor_lookup hi (by rw [hdata.ctors]; exact hfcc))
    rw [hconst] at hci
    cases hci
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw family hsrc fc hfc
    have h2 := hhead
    rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
    obtain rfl := (VExpr.const.inj (hF.symm.trans h2)).1
    exact ⟨⟨ciF, hciF⟩, hFr⟩
  · have hdf : env.defeqs equation := hle.defeqs hdefeq
    obtain ⟨ci, hci, F, ls', hF, ⟨ciF, hciF⟩, hFr⟩ :=
      henv.native_constructor_result_rigid hdf hmaj
    rw [hle.constants hconst] at hci
    cases hci
    obtain rfl := (VExpr.const.inj (hF.symm.trans hres)).1
    exact ⟨⟨ciF, hciF⟩, hFr⟩

end VEnv
end Lean4Lean

namespace Lean4Lean.InductiveSignature

theorem Restoration.wrapForalls_forall₂ {r : Restoration}
    (H : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧
      List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body' := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, rfl, .nil, H⟩
  | cons domain domains ih =>
    change (do let domain' ← r.expr domain; let body' ← r.expr (VExpr.wrapForalls domains body)
               pure (.forallE domain' body')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨domain', hd, out, hout, H⟩ := H
    cases H
    obtain ⟨domains', body', rfl, hrel, hb⟩ := ih hout
    exact ⟨domain' :: domains', body', rfl, .cons hd hrel, hb⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open InductiveSignature

private theorem forall₂_snoc_inv' {R : α → β → Prop} :
    ∀ {l₀ : List α} {x : α} {l : List β}, List.Forall₂ R (l₀ ++ [x]) l →
    ∃ l₀' x', l = l₀' ++ [x'] ∧ List.Forall₂ R l₀ l₀' ∧ R x x'
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t =>
    let ⟨l₀', x', e, t', h'⟩ := forall₂_snoc_inv' t
    ⟨_ :: l₀', x', by rw [e]; rfl, .cons h t', h'⟩

/-- The restored native recursor type is a telescope whose major domain is an
application of the restored family head of its owner. -/
theorem NativeRecursorData.recursorType_major {data : NativeRecursorData}
    (H : data.recursorType = some type) :
    ∃ domains body levels args, type = VExpr.wrapForalls domains body ∧
      domains.length = data.majorOffset + 1 ∧
      domains[data.majorOffset]? = some (VExpr.mkApps (.const
        (data.schema.restoration.headName data.schema.signature.families[data.owner].name)
        levels) args) := by
  unfold NativeRecursorData.recursorType Instance.recursorType at H
  obtain ⟨domains, body, rfl, hrel, _⟩ := Restoration.wrapForalls_forall₂ H
  obtain ⟨pre', x', rfl, hpre, hx⟩ := forall₂_snoc_inv' hrel
  have hpl := Lean4Lean.List.Forall₂.length_eq hpre
  have hoff : pre'.length = data.majorOffset := by
    rw [← hpl]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
      NativeRecursorData.majorOffset, NativeRecursorData.indexOffset,
      NativeRecursorData.numParams, NativeRecursorData.numIndices, Nat.add_assoc]
  obtain ⟨levels, args, hmajor⟩ := Restoration.const_mkApps hx
  refine ⟨pre' ++ [x'], body, levels, args, rfl, by simp [hoff], ?_⟩
  rw [List.getElem?_append_right (by omega)]
  simp [hoff, hmajor]

/-- The major of a typed native recursor application at its major offset is
never a function: its type is an application of the owner's family head,
which is rigid when the owner has a constructor. -/
theorem NativeRecursorRegistered.major_not_pi {data : NativeRecursorData} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : NativeRecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size)
    (hown : data.schema.signature.constructors[index].owner = data.owner)
    (ht : env.HasType U Γ (.app (VExpr.mkApps (.const data.name ls) vs) M) T)
    (hlen : vs.length = data.majorOffset) :
    ¬ env.HasType U Γ M (.forallE A B) := by
  intro hpi
  obtain ⟨type, htype⟩ := H.recursorType_exists
  have hconst := H.recursorType htype
  obtain ⟨domains, body, levels, args, rfl, hdl, hdom⟩ :=
    NativeRecursorData.recursorType_major htype
  have happ : VExpr.mkApps (.const data.name ls) (vs ++ [M]) =
      .app (VExpr.mkApps (.const data.name ls) vs) M := by
    simp [VExpr.mkApps, List.foldl_append]
  have hWF : VExpr.WF env U Γ (VExpr.mkApps (.const data.name ls) (vs ++ [M])) :=
    ⟨_, happ ▸ ht⟩
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hWF
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
  rw [hconst] at hci
  cases hci
  have hcT : env.HasType U Γ (.const data.name ls) (VExpr.wrapForalls
      (domains.map (·.instL ls)) (body.instL ls)) := by
    rw [← VExpr.instL_wrapForalls]; exact .const hconst hw hl
  have hlen' : (vs ++ [M]).length = (domains.map (·.instL ls)).length := by
    simp [hdl, hlen]
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hcT hWF hlen'
  have hM := hargs data.majorOffset (by simp; omega) (by simp; omega)
  have hlt : data.majorOffset < domains.length := by omega
  have hd : domains[data.majorOffset] = _ := (List.getElem?_eq_some_iff.mp hdom).2
  simp only [List.getElem_append_right (show vs.length ≤ data.majorOffset by omega),
    List.getElem_map, hlen, Nat.sub_self, List.getElem_singleton,
    List.take_left' hlen] at hM
  rw [hd, VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps, VExpr.instOuter_const] at hM
  have hrigid := (H.family_head_rigid henv index hown).2
  have ⟨_, hsort⟩ := hM.isType henv.ordered hΓ
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ hrigid hsort (hM.uniqU henv hΓ hpi)

theorem QuotRegistered.quot_rigid (henv : env.WF) (hr : QuotRegistered env) :
    env.Rigid ``Quot := by
  have hmk : quotDefEq.HasConstructorMajor ``Quot.mk :=
    ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
  obtain ⟨ci, hci, F, ls, hF, _, hFr⟩ := henv.native_constructor_result_rigid hr.equation hmk
  rw [hr.constructor] at hci
  cases hci
  have : quotMkConst.type.forallResult.getAppFnArgs.1 = .const ``Quot [.param 0] := rfl
  obtain rfl := (VExpr.const.inj (hF.symm.trans this)).1
  exact hFr

set_option maxHeartbeats 1000000 in
theorem QuotRegistered.major_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U)
    (H : VExpr.WF env U Γ (VExpr.mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, major])) :
    env.HasType U Γ major (VExpr.mkApps (.const ``Quot [u]) [alpha, relation]) := by
  obtain ⟨result, hw⟩ := quotient_walk henv hΓ hr hu hv H
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            cases hw with | cons hmajor hw =>
              simp [VExpr.instL, VExpr.inst, VLevel.inst, VExpr.inst_lift,
                ← VExpr.lift_instN_lo] at hmajor
              simpa [VExpr.mkApps] using hmajor

end Lean4Lean.VEnv
