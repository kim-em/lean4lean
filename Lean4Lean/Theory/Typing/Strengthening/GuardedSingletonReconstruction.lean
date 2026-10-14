import Lean4Lean.Theory.Typing.Strengthening.ProofIndexReconstruction
import Lean4Lean.Theory.Typing.Strengthening.ComparedEtaComputation
import Lean4Lean.Theory.Typing.RecursorMajorFamily
import Lean4Lean.Theory.Typing.Confluence.SingletonCoverage

/-! # A single family guard for arbitrary indexed reconstruction

The transported fields are always typed. For a rigid family, conversion of their
result family to the requested family supplies all index and literal-field
alignments needed by the original generated occurrence. No index domain is
required to be propositional.
-/
namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable {ps idx f : List VExpr} {familyName : Name}
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Expand the transported family at its actual typed field list. -/
theorem transportedFamily_eq (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m])) :
    transportedFamily S params E ps idx m =
      mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter
        (ps ++ transportedFields S params E ps idx m S.fields.length))) := by
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hlen : (ps ++ transportedFields S params E ps idx m S.fields.length).length =
      params.length + S.fields.length := by simpa using hf.1
  unfold transportedFamily branchFamily
  simp only [instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append, branchPa]
  rw [instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; exact Nat.le_refl _), hlen,
    Nat.sub_self, List.drop_zero, List.take_left' hps]

/-- Rigid family conversion determines each requested index at its declared
dependent domain, even when that domain contains data. -/
theorem indices_of_family_conversion (henv : env.WF) (W : E.WF S params env U)
    (hΓ : OnCtx Γ (env.IsType U)) (hfamily : E.family = .const familyName levels)
    (hrigid : env.Rigid familyName) (hps : ps.length = params.length)
    (hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx))
    (hconv : env.IsDefEq U Γ
      (mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))))
      (mkApps E.family (ps ++ idx)) (.sort .zero)) (hk : k < S.indices.length) :
    env.IsDefEq U Γ (idx.getD k default) ((E.ctorIndices.getD k default).instOuter (ps ++ f))
      ((S.indices.getD k default).instOuter (ps ++ idx.take k)) := by
  have hidx : idx.length = S.indices.length := by
    have := hia.1; simp only [List.length_append] at this; omega
  rw [hfamily] at hconv
  obtain ⟨_, hrel⟩ := IsDefEqU.rigidApp_inv henv hΓ hrigid ⟨_, hconv.symm⟩ hconv.hasType.2
  have h := Lean4Lean.List.forall₂_getElem hrel (params.length + k)
    (by simp [hps, hidx]; omega) (by simp [hps, W.ctorIndices_length]; omega)
  simp only [List.getElem_append_right (show ps.length ≤ params.length + k by omega), hps,
    Nat.add_sub_cancel_left, List.getElem_map] at h
  have hh : env.IsDefEqU U Γ (idx.getD k default)
      ((E.ctorIndices.getD k default).instOuter (ps ++ f)) := by
    simpa only [getD_of_lt (show k < idx.length by omega),
      getD_of_lt (show k < E.ctorIndices.length by rw [W.ctorIndices_length]; exact hk)] using h
  have ht := hia.getD (j := params.length + k) (by simp; omega)
  rw [getD_append_right' (by omega), getD_append_right' (by omega), List.take_append,
    List.take_of_length_le (by omega), hps, Nat.add_sub_cancel_left] at ht
  exact hh.of_l henv hΓ ht

/-- Componentwise result-index alignment supplies every literal data slot. -/
theorem alignment_of_indices (henv : env.WF) (W : E.WF S params env U)
    (hΓ : OnCtx Γ (env.IsType U))
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hps : ps.length = params.length)
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (hidx : ∀ k, k < S.indices.length → env.IsDefEqU U Γ (idx.getD k default)
      ((E.ctorIndices.getD k default).instOuter (ps ++ f)))
    (hs : S.slot.getD l none = some k) :
    env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
      ((S.fields.getD l default).instOuter (ps ++ f.take l)) := by
  have hfl : f.length = S.fields.length := by
    have := hf.1; simp only [List.length_append] at this; omega
  have hl := hslot l k hs
  have hk := W.typed.scope.slot_lt l k hs
  have h := (hidx k hk).symm
  rw [W.slot_literal l k hs, instOuter_bvar _ (by simp [hps, hfl]; omega)] at h
  have he : (ps ++ f)[(ps ++ f).length - 1 - (S.fields.length - 1 - l)]'(by
      simp only [List.length_append]; omega) = f.getD l default := by
    rw [List.getElem_append_right (by simp [hfl]; omega), getD_of_lt (by omega)]
    congr 1
    simp only [List.length_append]
    omega
  rw [he] at h
  have ht := hf.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by omega), getD_append_right' (by omega), List.take_append,
    List.take_of_length_le (by omega), hps, Nat.add_sub_cancel_left] at ht
  exact h.of_l henv hΓ ht

/-- One conversion between two already typed family propositions validates the
original generated fields and constructor at arbitrary data indices. -/
theorem reconstruction_of_family_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hfamily : E.family = .const familyName levels) (hrigid : env.Rigid familyName)
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hconv : env.IsDefEq U Γ (transportedFamily S params E ps idx m)
      (mkApps E.family (ps ++ idx)) (.sort .zero)) :
    TelInst env U Γ (params ++ S.fields)
      (ps ++ (occ S params E ps idx m S.fields.length).2) ∧
    env.IsDefEq U Γ m (mkApps E.ctor (ps ++ (occ S params E ps idx m S.fields.length).2))
      (mkApps E.family (ps ++ idx)) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  rw [transportedFamily_eq henv heq W hΓ hps hargs] at hconv
  have hix := fun k hk => indices_of_family_conversion henv W hΓ hfamily hrigid hps hia hconv (k := k) hk
  have halign := fun l k hs => alignment_of_indices henv W hΓ hslot hps hf
    (fun j hj => ⟨_, hix j hj⟩) (l := l) (k := k) hs
  have hfields := (occ_typed params henv heq W hΓ hps hargs hf halign
    S.fields.length (Nat.le_refl _)).2.1
  rw [List.take_length] at hfields
  have heta := singleton_eta params henv heq W hΓ hps hargs hf halign hix
  rw [majorTy_at W hps hidx] at heta
  exact ⟨hfields, heta⟩

/-- Once the original generated fields are typed, their literal slots make
them an aligned instance and identify the transported constructor with them. -/
theorem transportedCtor_eq_occ (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hf : TelInst env U Γ (params ++ S.fields)
      (ps ++ (occ S params E ps idx m S.fields.length).2)) :
    env.IsDefEqU U Γ (transportedCtor S params E ps idx m)
      (mkApps E.ctor (ps ++ (occ S params E ps idx m S.fields.length).2)) := by
  let f := (occ S params E ps idx m S.fields.length).2
  have hfl : f.length = S.fields.length := (occ_length S params E ps idx m S.fields.length).2
  have halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)) := by
    intro l k hs
    have hl := hslot l k hs
    have ht := hf.getD (j := params.length + l) (by simp; omega)
    rw [getD_append_right' (by omega), getD_append_right' (by omega), List.take_append,
      List.take_of_length_le (by omega), hps, Nat.add_sub_cancel_left] at ht
    change env.HasType U Γ (f.getD l default) _ at ht
    have he : f.getD l default = idx.getD k default := occ_getD_data ps idx m hs hl
    rw [← he]
    exact ht
  have ht := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at ht
  have hctx : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  have hcf := IsDefEq.closed_instOuter_congr' henv hΓ hctx W.ctor_typed ht.1 hf.1
    (fun j hj => by
      by_cases hjP : j < params.length
      · rw [getD_append_left' (by omega), getD_append_left' (by omega)]
        have hh := ht.getD hj
        rwa [getD_append_left' (by omega)] at hh
      · have hl : j - params.length < S.fields.length := by simp at hj; omega
        have he := transportedFields_eq_occ henv heq W hΓ hps hargs hf halign
          (Nat.le_refl S.fields.length) hl
        have hh := ht.getD hj
        rw [getD_append_right' (by omega), hps] at hh
        rw [getD_append_right' (by omega), getD_append_right' (by omega), hps]
        exact he.of_l henv hΓ hh)
  have hctor : (ctorApp S params E).instOuter (ps ++ f) = mkApps E.ctor (ps ++ f) := by
    unfold ctorApp
    rw [bvarRange_split]
    exact mkApps_instOuter_heads W.ctor_closed ps f params.length S.fields.length hps hfl
  change env.IsDefEq U Γ (transportedCtor S params E ps idx m) ((ctorApp S params E).instOuter (ps ++ f)) _ at hcf
  rw [hctor] at hcf
  exact ⟨_, hcf⟩

/-- For rigid families, the one family guard is equivalent to validity of the
original generated reconstruction. It is not merely a stronger sufficient test. -/
theorem reconstruction_iff_family_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hfamily : E.family = .const familyName levels) (hrigid : env.Rigid familyName)
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m])) :
    (TelInst env U Γ (params ++ S.fields)
        (ps ++ (occ S params E ps idx m S.fields.length).2) ∧
      env.IsDefEq U Γ m (mkApps E.ctor (ps ++ (occ S params E ps idx m S.fields.length).2))
        (mkApps E.family (ps ++ idx))) ↔
    env.IsDefEq U Γ (transportedFamily S params E ps idx m)
      (mkApps E.family (ps ++ idx)) (.sort .zero) := by
  constructor
  · rintro ⟨hf, he⟩
    have hc := transportedCtor_eq_occ henv heq W hΓ hslot hps hargs hf
    exact (bare_constructor_iff_family_conversion henv heq W hΓ hps hargs).1
      ((show env.IsDefEqU U Γ m _ from ⟨_, he⟩).trans henv hΓ hc.symm)
  · exact reconstruction_of_family_conversion henv heq W hΓ hfamily hrigid hslot hps hargs

/-- The transported family commutes with any substitution of occurrence
providers. Its declaration and closed proof extractors remain fixed. -/
theorem transportedFamily_subst (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (τ : Subst) :
    (transportedFamily S params E ps idx m).subst τ =
      transportedFamily S params E (ps.map (·.subst τ)) (idx.map (·.subst τ)) (m.subst τ) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hctx : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  have hc := (branchFamily_prop henv W).closedN henv.ordered (CtxWF.closed henv.ordered hctx)
  unfold transportedFamily
  rw [instOuter_subst_closed _ _ (by simpa only [List.length_reverse, ← hf.1] using hc),
    List.map_append, transportedFields_subst henv heq W hps hidx (Nat.le_refl _) τ]

/-- In particular the family guard's two endpoints are exact lifts of the
endpoints typed below the inserted binders. -/
theorem transportedFamily_lift' (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (ρ : Lift) :
    (transportedFamily S params E ps idx m).lift' ρ =
      transportedFamily S params E (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) (m.lift' ρ) := by
  simpa only [← InductiveSignature.RecursorData.lift'_eq_subst] using
    transportedFamily_subst henv heq W hΓ hps hargs (Subst.lift_r .id ρ)

end Lean4Lean.PropElim

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv
variable {levels : List VLevel}

/-- A registered singleton's extraction family is a rigid constant, from the
installed constructor provenance. This premise is not an extra user guard. -/
theorem propElim_family_rigid (henv : env.WF) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hE : data.propElim levels = some E) :
    ∃ name ls, E.family = .const name ls ∧ env.Rigid name := by
  obtain ⟨k, _, _, _, hrest, _, hE0, _⟩ := singleton_shape H hlarge hzero howner
  rw [hE0] at hE
  cases Option.some.inj hE
  have hr := (H.family_head_rigid henv index howner).2
  rw [hrest] at hr
  exact ⟨_, _, rfl, hr⟩

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim
variable [Params]
variable {S : SingletonLayout} {P ps idx : List VExpr} {E : PropElim}

/-- A descending comparison of the two typed family propositions validates
reconstruction below. The same guard handles arbitrary data indices; its
completeness is not asserted here. -/
theorem singleton_reconstruction_below
    (heq : env.HasCanonicalEq) (hcmp : EndpointDescent Cmp)
    (W : E.WF S P env univs)
    (hfamily : E.family = .const familyName levels) (hrigid : env.Rigid familyName)
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hps : ps.length = P.length)
    (hargs : TelInst env univs Γ (P ++ S.indices ++ [majorTy S P E]) (ps ++ idx ++ [m]))
    (H : Cmp Γ'
      (transportedFamily S P E (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) (m.lift' ρ))
      (mkApps E.family (ps.map (·.lift' ρ) ++ idx.map (·.lift' ρ)))) :
    TelInst env univs Γ (P ++ S.fields)
      (ps ++ (occ S P E ps idx m S.fields.length).2) ∧
    env.IsDefEq univs Γ m (mkApps E.ctor (ps ++ (occ S P E ps idx m S.fields.length).2))
      (mkApps E.family (ps ++ idx)) := by
  have ht := (transportedFamily_typings henv heq W hΓ hps hargs).1
  have hp := W.family_prop henv hps hargs
  rw [← transportedFamily_lift' henv heq W hΓ hps hargs] at H
  have hh : mkApps E.family (ps.map (·.lift' ρ) ++ idx.map (·.lift' ρ)) =
      (mkApps E.family (ps ++ idx)).lift' ρ := by
    rw [lift'_mkApps, W.family_closed.lift'_eq .zero, List.map_append]
  rw [hh] at H
  have hconv := (hcmp hW hΓ hΓ' ht hp H).of_l henv hΓ ht
  exact reconstruction_of_family_conversion henv heq W hΓ hfamily hrigid hslot hps hargs hconv

/-- Concrete finite recovered-comparison certificates discharge the family
guard for registered singletons, including arbitrary data-index telescopes.
Registration supplies family rigidity, slot bounds and extraction typing. -/
theorem registered_singleton_reconstruction_below
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hreg : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    (hw : ∀ l ∈ ls, l.WF univs) (hlen : ls.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env ls = some S) (hE : data.propElim ls = some E)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hps : ps.length = (data.propParams ls).length)
    (hargs : TelInst env univs Γ
      (data.propParams ls ++ S.indices ++ [majorTy S (data.propParams ls) E]) (ps ++ idx ++ [m]))
    (H : RecoveryComparisonGuard (ComparedEtaCompute D kdepth stage) Γ'
      (transportedFamily S (data.propParams ls) E
        (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) (m.lift' ρ))
      (mkApps E.family (ps.map (·.lift' ρ) ++ idx.map (·.lift' ρ)))) :
    TelInst env univs Γ (data.propParams ls ++ S.fields)
      (ps ++ (occ S (data.propParams ls) E ps idx m S.fields.length).2) ∧
    env.IsDefEq univs Γ m
      (mkApps E.ctor (ps ++ (occ S (data.propParams ls) E ps idx m S.fields.length).2))
      (mkApps E.family (ps ++ idx)) := by
  obtain ⟨S', E', hS', hE', W⟩ := InductiveSignature.RecursorData.propElim_wf henv Hreg
    hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨name, levels, hfamily, hrigid⟩ :=
    InductiveSignature.RecursorData.propElim_family_rigid henv Hreg hlarge hzero howner hE
  exact singleton_reconstruction_below heq
    (RecoveryComparisonGuard.descends (ComparedEtaCompute.computeDescent heq hs stage))
    W hfamily hrigid
    (InductiveSignature.RecursorData.singleton_slot_lt Hreg hlarge hzero howner hS)
    hW hΓ hΓ' hps hargs H

end Lean4Lean.VEnv.Strengthening
