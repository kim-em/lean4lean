import Lean4Lean.Theory.Typing.NativeSingletonPropElim
import Lean4Lean.Theory.Typing.NativeEquationCoverage
import Lean4Lean.Theory.Typing.NativeSingletonProofFields
import Lean4Lean.Theory.Typing.NativePrefixLayout

/-! # Coverage of zero-source native singleton equations

At a universe specialization where the source of a large-eliminating
native recursor is `Prop`, its installed equation is joined by the singleton
prefix unfolding at the recursor's prefix (all arguments before the
constructor major), a beta step with the constructor major, and proof
irrelevance for the reconstructed proof fields. The replay of the singleton
program at this literal instance is typed by the `Eq`-cast extraction
(`SingletonExtraction.lean`), which needs canonical `Eq`. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr VEnv
open private extract_wrap_const from Lean4Lean.Theory.Typing.NativeSingletonProofFields

variable {env : VEnv} {data : NativeRecursorData} {ls : List VLevel}

/-- The explicit extraction data of a registered native singleton at an
occurrence where its source is `Prop`. -/
theorem singleton_shape (H : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    (hlen : ls.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner) :
    ∃ k, data.target = .param k ∧
      data.schema.signature.families.size = 1 ∧ data.schema.signature.constructors.size = 1 ∧
      data.schema.restoration = {} ∧
      data.castSpec env ls = some ((data.nativeInstance.specialize 0 (ls.set k .zero)).singletonCast
        data.owner data.schema.signature.constructors[index]
        ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))) ∧
      data.propElim ls = some ((data.nativeInstance.specialize 0 (ls.set k .zero)).singletonElim
        data.owner data.schema.signature.constructors[index] (.const data.name (ls.set k .zero))) ∧
      data.propParams ls = (data.nativeInstance.specialize 0 (ls.set k .zero)).params ∧
      (data.nativeInstance.specialize 0 (ls.set k .zero)).levels = data.levels.map (·.inst ls) ∧
      data.singletonEquation = data.equation index := by
  have F := singletonFacts H hlarge hzero
  obtain ⟨k, hk, hkU, hfree⟩ := F.free
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := index.isLt; omega
  have hfam := F.families
  have htp : data.targetParam = some k := by simp [targetParam, hk]
  have hsc : data.singletonCtor = some index := by
    unfold singletonCtor
    have hfr : List.finRange data.schema.signature.constructors.size = [index] := by
      apply List.ext_getElem (by simp [hcs])
      intro n h1 h2
      simp only [List.length_finRange, hcs] at h1
      simp only [List.getElem_finRange, List.getElem_singleton]
      ext; simp; omega
    rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using howner), List.filter_nil]
  have hlev : data.levels.map (·.inst (ls.set k .zero)) = data.levels.map (·.inst ls) :=
    List.map_congr_left fun l hl => hfree l hl ls .zero
  let gp := data.nativeInstance.specialize 0 (ls.set k .zero)
  have hgpl : gp.levels = data.levels.map (·.inst ls) := hlev
  refine ⟨k, hk, hfam, hcs, F.restoration, ?_, ?_, ?_, hgpl, ?_⟩
  · have hFeq : (data.nativeInstance.sFields data.schema.signature.constructors[index]).map
        (·.instL ls) = gp.sFields data.schema.signature.constructors[index] := by
      simp [gp, Instance.sFields, Instance.specialize, nativeInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hIeq : (data.nativeInstance.sIndices data.owner).map (·.instL ls) =
        gp.sIndices data.owner := by
      simp [gp, Instance.sIndices, Instance.specialize, nativeInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hCIeq : (data.nativeInstance.sCtorIndices data.schema.signature.constructors[index]).map
        (·.instL ls) = gp.sCtorIndices data.schema.signature.constructors[index] := by
      simp [gp, Instance.sCtorIndices, Instance.specialize, nativeInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    simp only [castSpec, castSpecGeneric, hsc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.map_some]
    simp only [CastSpec.instL, Instance.singletonCast, Option.some.injEq, CastSpec.mk.injEq]
    refine ⟨hFeq, hIeq, ?_, trivial⟩
    rw [← hFeq, ← hCIeq, List.length_map]
    congr 1; funext j; exact (fieldSlot_instL _ _ _ _).symm
  · simp only [propElim, htp, hsc, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · simp [gp, propParams, Instance.params, Instance.specialize, nativeInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  · unfold singletonEquation NativeRecursorData.equation
    have hfr : (List.finRange data.schema.signature.constructors.size).filter
        (fun i => data.schema.signature.constructors[i].owner == data.owner) = [index] := by
      have hfr : List.finRange data.schema.signature.constructors.size = [index] := by
        apply List.ext_getElem (by simp [hcs])
        intro n h1 h2
        simp only [List.length_finRange, hcs] at h1
        simp only [List.getElem_finRange, List.getElem_singleton]
        ext; simp; omega
      rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using howner), List.filter_nil]
    simp only [hfr]

/-- The syntax of the installed equation of a registered native singleton,
at a universe specialization where its source is `Prop`, in terms of its
extraction data. -/
theorem singleton_equation_syntax (H : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel ls ≈ .zero)
    (hlen : ls.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    {S : CastSpec} {E : PropElim}
    (hS : data.castSpec env ls = some S) (hE : data.propElim ls = some E) :
    ∃ D lb rb tb X, data.equation index = some ⟨data.uvars, wrapLams D lb, wrapLams D rb,
        wrapForalls D tb⟩ ∧
      data.singletonEquation = data.equation index ∧
      CaseSchema.EquationBody.extract (wrapLams D lb) (wrapLams D rb) (wrapForalls D tb) =
        some ⟨D, lb, rb, tb⟩ ∧
      D.map (·.instL ls) = data.propParams ls ++ X ++ insertBinders S.fields 2 ∧ X.length = 2 ∧
      lb.instL ls = .app
        (mkApps (.const data.name ls) (vars data.indexOffset S.fields.length ++
          E.ctorIndices.map (·.liftN 2 S.fields.length)))
        (mkApps E.ctor (vars (data.propParams ls).length (2 + S.fields.length) ++
          vars S.fields.length 0)) ∧
      data.indexOffset = (data.propParams ls).length + 2 ∧
      data.recursorType = some (data.nativeInstance.recursorType data.owner) := by
  obtain ⟨k, hk, hfam, hcs, hres, hS0, hE0, hP, hgl, hseq⟩ :=
    singleton_shape H hlarge hzero hlen howner
  rw [hS0] at hS; cases Option.some.inj hS
  rw [hE0] at hE; cases Option.some.inj hE
  have F := singletonFacts H hlarge hzero
  let s := data.schema.signature
  let c := s.constructors[index]
  let g := data.nativeInstance
  have hextra : s.families.size + s.constructors.size = 2 := by simp [s, hfam, hcs]
  have hlev : data.levels.map (·.inst (ls.set k .zero)) = data.levels.map (·.inst ls) := hgl
  refine ⟨g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes c).map (·.instL g.levels)) (s.families.size + s.constructors.size),
    mkApps (g.recursorHead .native c.owner)
      (vars (s.params.length + (s.families.size + s.constructors.size)) c.fields.length ++
        c.indices.map (fun e => (e.instL g.levels).liftN (s.families.size + s.constructors.size)
          c.fields.length) ++
        [g.constructorApp c (s.families.size + s.constructors.size) 0]),
    ?rb, ?tb, (g.motives ++ g.minors).map (·.instL ls), ?h1, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7, ?h8⟩
  case h1 =>
    unfold NativeRecursorData.equation
    rw [hres, Restoration.equation_empty]
    rfl
  case h2 => exact hseq
  case h3 => exact extract_wrap_const (by exact VExpr.getAppFnArgs_mkApps_head _ _) _
  case h4 =>
    have hpar : g.params.map (·.instL ls) =
        (data.nativeInstance.specialize 0 (ls.set k .zero)).params := by
      simp only [Instance.params, Instance.specialize, g, nativeInstance, List.map_map,
        Function.comp_def, VExpr.instL_instL, hlev]
    have hins : (insertBinders ((s.fieldTypes c).map (·.instL g.levels))
        (s.families.size + s.constructors.size)).map (·.instL ls) =
        insertBinders ((data.nativeInstance.specialize 0 (ls.set k .zero)).singletonCast data.owner
          data.schema.signature.constructors[index]
          ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))).fields 2 := by
      rw [hextra]
      simp only [insertBinders, Instance.singletonCast, Instance.sFields, List.map_map,
        Function.comp_def, VExpr.instL_liftN, VExpr.instL_instL, hgl, List.zipIdx_map]
      simp [g, nativeInstance, c, s, Function.comp_def, VExpr.instL_instL, hgl, Instance.specialize]
    rw [hP]
    simp only [List.map_append, List.append_assoc, hpar, hins]
  case h5 => simp [Instance.motives, Instance.minors, s, hfam, hcs]
  case h7 =>
    rw [hP]; simp [indexOffset, numParams, Instance.params, Instance.specialize, hfam, hcs]
  case h8 =>
    unfold NativeRecursorData.recursorType
    rw [hres, Restoration.expr_empty]
  case h6 =>
    have hnf : ((data.nativeInstance.specialize 0 (ls.set k .zero)).singletonCast data.owner
        data.schema.signature.constructors[index]
        ((data.genericSorts env data.schema.signature.constructors[index]).map (·.inst ls))).fields.length =
        c.fields.length := by
      simp [Instance.singletonCast, Instance.sFields, InductiveSignature.fieldTypes, c, s]
    have hnp : (data.propParams ls).length = s.params.length := by
      rw [hP]; simp [Instance.params, s]
    have hname : g.recursorName c.owner = data.name := by
      have := congrArg (fun o : Fin _ => (data.schema.signature.families[o]).name.str "rec") howner
      simpa [g, nativeInstance, NativeRecursorData.name, hres, Restoration.recursorName, c, s] using this
    have hio : data.indexOffset = s.params.length + (s.families.size + s.constructors.size) := by
      simp [indexOffset, numParams, Nat.add_assoc, s]
    rw [hnf, hnp, hio, hextra]
    simp only [VEnv.mkApps_snoc, VExpr.instL, VExpr.instL_mkApps, List.map_append, Instance.recursorHead,
      hname, VEnv.vars_instL, List.map_map, Function.comp_def, VExpr.instL_liftN, VExpr.instL_instL,
      Instance.constructorApp, Instance.singletonElim, Instance.sCtorIndices]
    have hu : (VLevel.params g.uvars).map (VLevel.inst ls) = ls := VLevel.inst_map_id hlen
    have hgl' : (data.nativeInstance.specialize 0 (ls.set k .zero)).levels =
        g.levels.map (VLevel.inst ls) := hgl
    rw [hu, hgl']
    rfl

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem instOuter_liftN_skip {X : VExpr} {A B : List VExpr} {P r : Nat}
    (hX : X.ClosedN (P + B.length)) (hA : A.length = P + r) :
    (X.liftN r B.length).instOuter (A ++ B) = X.instOuter (A.take P ++ B) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  have hAt : (A.take P).length = P := by simp; omega
  by_cases hik : i < B.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ (by simp; omega),
      VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_lt _ (by simp; omega),
      VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_take]
    congr 1; simp; omega


theorem TelInst.instOuter_args {env : VEnv} {U : Nat} (henv : env.WF)
    {doms' doms args args' : List VExpr} {Γ : List VExpr}
    (hctx : OnCtx doms'.reverse (env.IsType U))
    (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j)
    (H : TelInst env U doms'.reverse doms args) (H' : TelInst env U Γ doms' args') :
    TelInst env U Γ doms (args.map (·.instOuter args')) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_map] at hj
  have h := HasType.closed_instOuter henv hctx (H.2 j hj hj') H'
  rw [instOuter_instOuter _ _ _ (by simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using hcl j hj')] at h
  simpa [List.map_take] using h


theorem InstForallsC.supplyType_eq {env : VEnv} {U : Nat} {Γ : List VExpr} {T : VExpr}
    {args : List VExpr} {res : VExpr} (H : InstForallsC env U Γ T args res) :
    NativeRecursorData.supplyType args T = some res := by
  induction H with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem instOuter_vars_lift {X : VExpr} {n k : Nat} (hX : X.ClosedN n) :
    X.instOuter (vars n k) = X.liftN k := by
  rw [vars_eq_bvarRange, instOuter_range_bvar' _ _ _ hX (by omega), Nat.add_sub_cancel_left]

section
variable [Params]
open Params

theorem FullReduction.wrapLams' {domains : List VExpr} {body body' : VExpr} {Γ : List VExpr}
    (H : FullReduction (domains.reverse ++ Γ) body body') :
    FullReduction Γ (VExpr.wrapLams domains body) (VExpr.wrapLams domains body') := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons d ds ih =>
    exact FullReduction.lam .rfl (ih (Γ := d :: Γ) (by simpa using H))

end

section Literal
variable {env : VEnv} {U : Nat} {S : CastSpec} {P : List VExpr} {E : PropElim}

theorem _root_.Lean4Lean.PropElim.WF.instOuter_branch (W : E.WF S P env U) {ps f : List VExpr}
    (hl : (ps ++ f).length = P.length + S.fields.length) (hpsl : ps.length = P.length) :
    (PropElim.branchPa S P).map (·.instOuter (ps ++ f)) = ps := by
  unfold PropElim.branchPa
  rw [instOuter_bvarRange _ _ _ (by omega) (by omega)]
  simp [hl, List.take_left' hpsl]

/-- At a literal constructor instance, the indices are the constructor's own
indices and the major is the constructor application. -/
theorem _root_.Lean4Lean.PropElim.WF.literal_args (henv : env.WF) (W : E.WF S P env U)
    {Δ ps f : List VExpr} (hpsl : ps.length = P.length)
    (hf : TelInst env U Δ (P ++ S.fields) (ps ++ f)) :
    TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [VExpr.mkApps E.ctor (ps ++ f)]) := by
  have T := W.typed
  have hl : (ps ++ f).length = P.length + S.fields.length := by
    have := hf.1; simpa using this
  have hctx : OnCtx (P ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hclI := T.prefix_closed (rest := S.indices) fun i h => T.scope.indices i h
  have hci := TelInst.instOuter_args henv hctx hclI W.ctorIndices_typed hf
  rw [List.map_append, W.instOuter_branch hl hpsl] at hci
  refine hci.append_one ?_
  have hM := HasType.closed_instOuter henv hctx W.ctor_typed hf
  have hctor : (PropElim.ctorApp S P E).instOuter (ps ++ f) = VExpr.mkApps E.ctor (ps ++ f) := by
    unfold PropElim.ctorApp
    rw [← hl]
    exact instOuter_bvarRange_apps W.ctor_closed _
  rw [hctor] at hM
  have hmaj : (PropElim.majorTy S P E).instOuter (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) =
      VExpr.mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) := by
    unfold PropElim.majorTy
    exact PropElim.mkApps_instOuter_heads W.family_closed _ _ [] _ _ hpsl
      (by simp [W.ctorIndices_length])
  rw [hmaj]
  simpa only [VExpr.instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append,
    W.instOuter_branch hl hpsl] using hM


theorem TelInst.getD_mid {Γ A B C a b c : List VExpr} (H : TelInst env U Γ (A ++ B ++ C) (a ++ b ++ c))
    (ha : a.length = A.length) (hb : b.length = B.length) {j : Nat} (hj : j < B.length) :
    env.HasType U Γ (b.getD j default) ((B.getD j default).instOuter (a ++ b.take j)) := by
  have h := H.getD (j := A.length + j) (by simp; omega)
  simp only [List.append_assoc] at h
  rw [getD_append_right' (l₁ := a) (by omega), getD_append_right' (l₁ := A) (by omega), ha,
    Nat.add_sub_cancel_left, getD_append_left' (l₁ := b) (by omega),
    getD_append_left' (l₁ := B) (by omega), ← ha, List.take_append,
    List.take_of_length_le (l := a) (by omega), List.take_append, Nat.add_sub_cancel_left,
    show j - b.length = 0 by omega, List.take_zero, List.append_nil] at h
  exact h

theorem _root_.Lean4Lean.PropElim.WF.literal_index (W : E.WF S P env U) {ps f : List VExpr}
    (hl : (ps ++ f).length = P.length + S.fields.length) (hpsl : ps.length = P.length)
    {l k : Nat} (hs : S.slot.getD l none = some k) (hlf : l < S.fields.length) :
    (E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default = f.getD l default := by
  have hk : k < E.ctorIndices.length := by
    rw [W.ctorIndices_length]; exact W.typed.scope.slot_lt l k hs
  have hfl : f.length = S.fields.length := by simp at hl; omega
  rw [getD_of_lt (by simpa using hk), List.getElem_map, ← getD_of_lt hk, W.slot_literal l k hs,
    VExpr.instOuter_bvar _ (by simp; omega), getD_of_lt (by omega)]
  rw [List.getElem_append_right (by simp; omega)]
  congr 1; simp; omega

/-- The singleton reconstruction at a literal constructor instance, for any
major typed at the instance's type. -/
theorem _root_.Lean4Lean.PropElim.WF.literal_occ (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    {Δ ps f : List VExpr} {m : VExpr} (hΔ : OnCtx Δ (env.IsType U))
    (hpsl : ps.length = P.length) (hf : TelInst env U Δ (P ++ S.fields) (ps ++ f))
    (hm : env.HasType U Δ m ((PropElim.majorTy S P E).instOuter
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))))) :
    TelInst env U Δ (P ++ S.fields)
        (ps ++ (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2) ∧
      (∀ l, l < S.fields.length → env.IsDefEq U Δ
        ((PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2.getD l default)
        (f.getD l default)
        ((S.fields.getD l default).instOuter (ps ++
          (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2.take l))) ∧
      env.IsDefEq U Δ m (VExpr.mkApps E.ctor (ps ++
        (PropElim.occ S P E ps (E.ctorIndices.map (·.instOuter (ps ++ f))) m S.fields.length).2))
        ((PropElim.majorTy S P E).instOuter (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)))) := by
  have hl : (ps ++ f).length = P.length + S.fields.length := by
    have := hf.1; simpa using this
  have hfl : f.length = S.fields.length := by simp at hl; omega
  have hargs0 := W.literal_args henv hpsl hf
  have hidxl : (E.ctorIndices.map (·.instOuter (ps ++ f))).length = S.indices.length := by
    simp [W.ctorIndices_length]
  have hargs : TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)) ++ [m]) := by
    have h1 := hargs0.take
    have hlen : (P ++ S.indices).length =
        (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))).length := by
      simp [hpsl, W.ctorIndices_length]
    rw [hlen, List.take_left] at h1
    exact h1.append_one hm
  have halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Δ (f.getD l default) ((E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)) := by
    intro l k hs
    have hlf := hslot l k hs
    rw [W.literal_index hl hpsl hs hlf]
    exact TelInst.getD_mid (C := []) (c := []) (by simpa using hf) hpsl hfl hlf
  have hidx : ∀ k, k < S.indices.length →
      env.IsDefEq U Δ ((E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default)
        ((E.ctorIndices.getD k default).instOuter (ps ++ f))
        ((S.indices.getD k default).instOuter (ps ++ (E.ctorIndices.map (·.instOuter (ps ++ f))).take k)) := by
    intro k hk
    have h := TelInst.getD_mid hargs0 hpsl hidxl hk
    have he : (E.ctorIndices.map (·.instOuter (ps ++ f))).getD k default =
        (E.ctorIndices.getD k default).instOuter (ps ++ f) := by
      rw [getD_of_lt (by rw [hidxl]; exact hk), getD_of_lt (by rw [W.ctorIndices_length]; exact hk),
        List.getElem_map]
    rw [← he]; exact h
  obtain ⟨_, h2, h3, _⟩ := PropElim.occ_typed P henv heq W hΔ hpsl hargs hf halign
    S.fields.length (Nat.le_refl _)
  rw [List.take_length] at h2
  exact ⟨h2, h3, PropElim.singleton_eta P henv heq W hΔ hpsl hargs hf halign hidx⟩

theorem _root_.Lean4Lean.PropElim.WF.majorTy_instOuter (W : E.WF S P env U) {ps idx : List VExpr}
    (hpsl : ps.length = P.length) (hidx : idx.length = S.indices.length) :
    (PropElim.majorTy S P E).instOuter (ps ++ idx) = VExpr.mkApps E.family (ps ++ idx) := by
  unfold PropElim.majorTy
  exact PropElim.mkApps_instOuter_heads W.family_closed _ _ [] _ _ hpsl hidx

theorem TelInst.drop_mid {Γ A M B a m b : List VExpr}
    (H : TelInst env U Γ (A ++ M ++ B.mapIdx (fun l d => d.liftN M.length l)) (a ++ m ++ b))
    (ha : a.length = A.length) (hm : m.length = M.length)
    (hcl : ∀ k (h : k < B.length), (B[k]).ClosedN (A.length + k)) :
    TelInst env U Γ (A ++ B) (a ++ b) := by
  have hbl : b.length = B.length := by have := H.1; simp at this; omega
  have HA : TelInst env U Γ A a := by
    have h := (show TelInst env U Γ (A ++ (M ++ B.mapIdx (fun l d => d.liftN M.length l)))
      (a ++ (m ++ b)) by simpa only [List.append_assoc] using H).take
    rwa [← ha, List.take_left] at h
  refine HA.append hbl fun j hj => ?_
  have h := TelInst.getD_mid (A := A ++ M) (a := a ++ m) (B := B.mapIdx (fun l d => d.liftN M.length l))
    (b := b) (C := []) (c := []) (by simpa using H) (by simp [ha, hm])
    (by simp [hbl]) (j := j) (by simpa using hj)
  have hX : (B.getD j default).ClosedN (A.length + j) := by
    rw [getD_of_lt hj]; exact hcl j hj
  have htl : (b.take j).length = j := by simp; omega
  have hsk := instOuter_liftN_skip (X := B.getD j default) (A := a ++ m) (B := b.take j)
    (P := A.length) (r := M.length) (by rw [htl]; exact hX) (by simp [ha, hm])
  rw [htl, List.take_left' ha] at hsk
  rw [getD_of_lt (l := B.mapIdx (fun l d => d.liftN M.length l)) (by simpa using hj),
    List.getElem_mapIdx, ← getD_of_lt hj, hsk] at h
  exact h

theorem _root_.Lean4Lean.PropElim.occ_getD_prefix (ps idx : List VExpr) (m : VExpr) {l : Nat} :
    ∀ n, l < n → (PropElim.occ S P E ps idx m n).2.getD l default =
      (PropElim.occ S P E ps idx m (l + 1)).2.getD l default := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hl : l = n
    · subst hl; rfl
    · rw [← ih (by omega)]
      have hlen := (PropElim.occ_length S P E ps idx m n).2
      simp only [PropElim.occ]
      split <;> rw [getD_append_left' (by omega)]

theorem _root_.Lean4Lean.PropElim.occ_getD_data (ps idx : List VExpr) (m : VExpr) {l k n : Nat}
    (hs : S.slot.getD l none = some k) (hl : l < n) :
    (PropElim.occ S P E ps idx m n).2.getD l default = idx.getD k default := by
  rw [PropElim.occ_getD_prefix ps idx m n hl]
  have hlen := (PropElim.occ_length S P E ps idx m l).2
  simp only [PropElim.occ, hs]
  rw [getD_append_right' (by omega), hlen, Nat.sub_self]
  rfl

end Literal

end Lean4Lean.VEnv
