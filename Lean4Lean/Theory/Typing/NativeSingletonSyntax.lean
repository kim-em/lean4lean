import Lean4Lean.Theory.Typing.NativeSingletonDefs
import Lean4Lean.Theory.Typing.SingletonExtractionCongr

/-! # Syntax of the native singleton extraction

Universe instantiation and level congruence of the cast specification, the elimination
into `Prop` and the reconstruction of a registered native recursor
(`NativeRecursorData.castSpec`, `propElim`, `PropElim.occ`). -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr VEnv

namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s)

theorem specialize_specialize (U U' : Nat) (ls ls' : List VLevel) :
    (g.specialize U ls).specialize U' ls' = g.specialize U' (ls.map (·.inst ls')) := by
  simp [specialize, List.map_map, Function.comp_def, VLevel.inst_inst]

theorem instL_wrapLams (ds : List VExpr) (b : VExpr) (ls : List VLevel) :
    (VExpr.wrapLams ds b).instL ls = VExpr.wrapLams (ds.map (·.instL ls)) (b.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    show VExpr.instL ls (.lam d (VExpr.wrapLams ds b)) =
      .lam (d.instL ls) (VExpr.wrapLams (ds.map (·.instL ls)) (b.instL ls))
    simp only [VExpr.instL, ih]

theorem instL_instDomains (ds : List VExpr) (a : VExpr) (k : Nat) (ls : List VLevel) :
    (VExpr.instDomains ds a k).map (·.instL ls) =
      VExpr.instDomains (ds.map (·.instL ls)) (a.instL ls) k := by
  induction ds generalizing k <;> simp [VExpr.instDomains, *]

theorem sFields_specialize (c : Constructor s.families.size) (U ls) :
    (g.specialize U ls).sFields c = (g.sFields c).map (·.instL ls) := by
  simp [sFields, specialize, List.map_map, Function.comp_def, VExpr.instL_instL]

theorem sIndices_specialize (owner : Fin s.families.size) (U ls) :
    (g.specialize U ls).sIndices owner = (g.sIndices owner).map (·.instL ls) := by
  simp [sIndices, specialize, List.map_map, Function.comp_def, VExpr.instL_instL]

theorem sCtorIndices_specialize (c : Constructor s.families.size) (U ls) :
    (g.specialize U ls).sCtorIndices c = (g.sCtorIndices c).map (·.instL ls) := by
  simp [sCtorIndices, specialize, List.map_map, Function.comp_def, VExpr.instL_instL]

theorem sHyps_specialize (c : Constructor s.families.size) (U ls) :
    (g.specialize U ls).sHyps c = (g.sHyps c).map (·.instL ls) := by
  simp [sHyps, List.map_map, Function.comp_def, hypothesis_specialize g U ls]

theorem params_specialize' (U ls) : (g.specialize U ls).params = g.params.map (·.instL ls) :=
  (params_specialize g U ls).symm

/-- The elimination at an instantiated instance is the instantiated elimination. -/
theorem singletonElim_instL (owner : Fin s.families.size) (c : Constructor s.families.size)
    (h : VExpr) (U : Nat) (ls : List VLevel) :
    PropElim.Rel (fun x y => y = x.instL ls) (g.singletonElim owner c h)
      ((g.specialize U ls).singletonElim owner c (h.instL ls)) where
  family := by simp [singletonElim, specialize, VExpr.instL]
  ctor := by simp [singletonElim, specialize, VExpr.instL]
  ctorIndices := by
    simp only [singletonElim, sCtorIndices_specialize]
    exact forall₂_instL_of
  elimHead := rfl
  minorOf := by
    intro M M' b b' hM hb
    subst hM hb
    simp only [singletonElim, instL_wrapLams, instL_instDomains, VExpr.instL_liftN,
      sFields_specialize, sHyps_specialize, List.length_map, List.map_append,
      instL_insertBinders]

/-- Elimination at two lists of equivalent universes gives related eliminations. -/
theorem singletonElim_levels (owner : Fin s.families.size) (c : Constructor s.families.size)
    {h h' : VExpr} {U U₀ : Nat} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls')
    (hh : EqUpToLevels U h h') :
    PropElim.Rel (EqUpToLevels U) ((g.specialize U₀ ls).singletonElim owner c h)
      ((g.specialize U₀ ls').singletonElim owner c h') := by
  have hgl : ∀ l ∈ (g.specialize U₀ ls).levels, l.WF U := by
    simp only [specialize, List.mem_map]
    rintro _ ⟨l, _, rfl⟩; exact VLevel.WF.inst hls
  have hgl' : ∀ l ∈ (g.specialize U₀ ls').levels, l.WF U := by
    simp only [specialize, List.mem_map]
    rintro _ ⟨l, _, rfl⟩; exact VLevel.WF.inst hls'
  have hgeq : List.Forall₂ (· ≈ ·) (g.specialize U₀ ls).levels (g.specialize U₀ ls').levels := by
    simp only [specialize]
    generalize g.levels = L
    induction L with
    | nil => exact .nil
    | cons l L ih => exact .cons (VLevel.inst_congr rfl heq) ih
  have hlist : ∀ (l : List VExpr), List.Forall₂ (EqUpToLevels U)
      (l.map (·.instL ls)) (l.map (·.instL ls')) := by
    intro l
    induction l with
    | nil => exact .nil
    | cons x l ih => exact .cons (EqUpToLevels.instL_expr x hls hls' heq) ih
  refine {
    family := .const hgl hgl' hgeq
    ctor := .const hgl hgl' hgeq
    ctorIndices := ?_
    elimHead := hh
    minorOf := ?_ }
  · simp only [singletonElim, sCtorIndices_specialize]
    exact hlist _
  · intro M M' b b' hM hb
    simp only [singletonElim, sFields_specialize, sHyps_specialize, List.length_map,
      ← instL_insertBinders, ← List.map_append]
    apply (SynRel.levels U).wrapLams (hb.weakN)
    have hd := hlist (insertBinders (g.sFields c) 1 ++ g.sHyps c)
    generalize (insertBinders (g.sFields c) 1 ++ g.sHyps c).map (·.instL ls) = D at hd
    generalize (insertBinders (g.sFields c) 1 ++ g.sHyps c).map (·.instL ls') = D' at hd
    suffices ∀ k, List.Forall₂ (EqUpToLevels U) (VExpr.instDomains D M k)
        (VExpr.instDomains D' M' k) from this 0
    induction hd with
    | nil => intro k; exact .nil
    | cons hx _ ih => intro k; exact .cons (EqUpToLevels.instN hM hx) (ih (k + 1))

end InductiveSignature.Instance
namespace CastSpec

theorem instL_instL (S : CastSpec) (ls ls' : List VLevel) :
    (S.instL ls).instL ls' = S.instL (ls.map (·.inst ls')) := by
  cases S
  simp [CastSpec.instL, List.map_map, Function.comp_def, VExpr.instL_instL, VLevel.inst_inst]

theorem getD_sorts_map (l : List VLevel) (ls : List VLevel) (i : Nat) :
    (l.map (·.inst ls)).getD i .zero = (l.getD i .zero).inst ls := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [VLevel.inst]

theorem rel_instL (S : CastSpec) (ls : List VLevel) :
    Rel (fun x y => y = x.instL ls) (fun u v => v = u.inst ls) S (S.instL ls) where
  fields := forall₂_instL_of
  indices := forall₂_instL_of
  slot := rfl
  sorts i := by simp only [CastSpec.instL]; exact getD_sorts_map _ _ _

theorem rel_levels (S : CastSpec) {U : Nat} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    Rel (EqUpToLevels U) (fun u v => u.WF U ∧ v.WF U ∧ u ≈ v) (S.instL ls) (S.instL ls') where
  fields := by
    simp only [CastSpec.instL]
    generalize S.fields = l
    induction l with
    | nil => exact .nil
    | cons x l ih => exact .cons (EqUpToLevels.instL_expr x hls hls' heq) ih
  indices := by
    simp only [CastSpec.instL]
    generalize S.indices = l
    induction l with
    | nil => exact .nil
    | cons x l ih => exact .cons (EqUpToLevels.instL_expr x hls hls' heq) ih
  slot := rfl
  sorts i := by
    simp only [CastSpec.instL, getD_sorts_map]
    exact ⟨VLevel.WF.inst hls, VLevel.WF.inst hls', VLevel.inst_congr rfl heq⟩

end CastSpec

namespace InductiveSignature.NativeRecursorData
variable {env : VEnv} {data : NativeRecursorData}

theorem castSpec_instL (ls packed : List VLevel) :
    data.castSpec env (ls.map (·.inst packed)) = (data.castSpec env ls).map (·.instL packed) := by
  simp only [castSpec, Option.map_map]
  congr 1
  funext S
  simp [CastSpec.instL_instL]

theorem propParams_instL (ls packed : List VLevel) :
    data.propParams (ls.map (·.inst packed)) = (data.propParams ls).map (·.instL packed) := by
  simp [propParams, List.map_map, Function.comp_def, VExpr.instL_instL]

theorem set_zero_map (ls packed : List VLevel) (k : Nat) :
    (ls.map (·.inst packed)).set k .zero = (ls.set k .zero).map (·.inst packed) := by
  rw [List.map_set]; rfl

theorem propElim_instL {ls : List VLevel} {E : PropElim} (hE : data.propElim ls = some E)
    (packed : List VLevel) :
    ∃ E', data.propElim (ls.map (·.inst packed)) = some E' ∧
      PropElim.Rel (fun x y => y = x.instL packed) E E' := by
  unfold propElim at hE ⊢
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hE
  obtain ⟨k, hk, i, hi, rfl⟩ := hE
  refine ⟨(data.nativeInstance.specialize 0 ((ls.map (·.inst packed)).set k .zero)).singletonElim
    data.owner data.schema.signature.constructors[i]
    (.const data.name ((ls.map (·.inst packed)).set k .zero)), by simp [hk, hi], ?_⟩
  rw [set_zero_map, ← Instance.specialize_specialize]
  exact Instance.singletonElim_instL _ _ _ _ 0 packed

theorem forall₂_set {R : α → α → Prop} (hd : R d d) :
    ∀ {l l' : List α}, List.Forall₂ R l l' → ∀ k, List.Forall₂ R (l.set k d) (l'.set k d)
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, 0 => .cons hd t
  | _, _, .cons h t, k + 1 => .cons h (forall₂_set hd t k)

theorem wf_set {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (k : Nat) :
    ∀ l ∈ ls.set k .zero, l.WF U := by
  intro l hl
  rcases List.mem_or_eq_of_mem_set hl with h | rfl
  · exact hls l h
  · simp [VLevel.WF]

theorem propElim_levels {ls ls' : List VLevel} {E : PropElim} (hE : data.propElim ls = some E)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∃ E', data.propElim ls' = some E' ∧ PropElim.Rel (EqUpToLevels U) E E' := by
  unfold propElim at hE ⊢
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hE
  obtain ⟨k, hk, i, hi, rfl⟩ := hE
  refine ⟨(data.nativeInstance.specialize 0 (ls'.set k .zero)).singletonElim
    data.owner data.schema.signature.constructors[i]
    (.const data.name (ls'.set k .zero)), by simp [hk, hi], ?_⟩
  have h0 := wf_set hls k
  have h0' := wf_set hls' k
  have hset := forall₂_set (R := (· ≈ ·)) (d := VLevel.zero) rfl heq k
  exact Instance.singletonElim_levels _ _ _ h0 h0' hset (.const h0 h0' hset)

theorem castSpec_levels {ls ls' : List VLevel} {S : CastSpec}
    (hS : data.castSpec env ls = some S)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∃ S', data.castSpec env ls' = some S' ∧
      CastSpec.Rel (EqUpToLevels U) (fun u v => u.WF U ∧ v.WF U ∧ u ≈ v) S S' := by
  unfold castSpec at hS ⊢
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hS
  exact ⟨_, by simp [hG], CastSpec.rel_levels G hls hls' heq⟩

theorem propParams_levels {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    List.Forall₂ (EqUpToLevels U) (data.propParams ls) (data.propParams ls') := by
  simp only [propParams]
  generalize data.nativeInstance.params = l
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (EqUpToLevels.instL_expr x hls hls' heq) ih

/-- The reconstruction at instantiated universes is the instantiated reconstruction. -/
theorem occ_instL {ls packed : List VLevel} {S : CastSpec} {E : PropElim}
    (hS : data.castSpec env ls = some S) (hE : data.propElim ls = some E) :
    data.castSpec env (ls.map (·.inst packed)) = some (S.instL packed) ∧
    data.propParams (ls.map (·.inst packed)) = (data.propParams ls).map (·.instL packed) ∧
    ∃ E', data.propElim (ls.map (·.inst packed)) = some E' ∧
      ∀ ps idx m i,
        PropElim.occ (S.instL packed) ((data.propParams ls).map (·.instL packed)) E'
            (ps.map (·.instL packed)) (idx.map (·.instL packed)) (m.instL packed) i =
          ((PropElim.occ S (data.propParams ls) E ps idx m i).1.map (·.instL packed),
            (PropElim.occ S (data.propParams ls) E ps idx m i).2.map (·.instL packed)) := by
  refine ⟨by rw [castSpec_instL, hS]; rfl, propParams_instL _ _, ?_⟩
  obtain ⟨E', hE', hrel⟩ := propElim_instL hE packed
  refine ⟨E', hE', fun ps idx m i => ?_⟩
  have := PropElim.occ_rel (SynRel.instL packed) (CastSpec.rel_instL S packed)
    forall₂_instL_of hrel (params := data.propParams ls) (ps := ps) (idx := idx) (m := m) (m' := m.instL packed)
    forall₂_instL_of forall₂_instL_of rfl i
  rw [← forall₂_instL this.1, ← forall₂_instL this.2]

/-- The reconstruction at equivalent universes, from arguments equal up to levels, is equal
up to levels. -/
theorem occ_levels {ls ls' : List VLevel} {S : CastSpec} {E : PropElim}
    (hS : data.castSpec env ls = some S) (hE : data.propElim ls = some E)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∃ S' E', data.castSpec env ls' = some S' ∧ data.propElim ls' = some E' ∧
      S'.fields.length = S.fields.length ∧
      ∀ {ps ps' idx idx' m m'}, List.Forall₂ (EqUpToLevels U) ps ps' →
        List.Forall₂ (EqUpToLevels U) idx idx' → EqUpToLevels U m m' → ∀ i,
        List.Forall₂ (EqUpToLevels U) (PropElim.occ S (data.propParams ls) E ps idx m i).1
            (PropElim.occ S' (data.propParams ls') E' ps' idx' m' i).1 ∧
          List.Forall₂ (EqUpToLevels U) (PropElim.occ S (data.propParams ls) E ps idx m i).2
            (PropElim.occ S' (data.propParams ls') E' ps' idx' m' i).2 := by
  obtain ⟨S', hS', hSrel⟩ := castSpec_levels hS hls hls' heq
  obtain ⟨E', hE', hErel⟩ := propElim_levels hE hls hls' heq
  refine ⟨S', E', hS', hE', hSrel.fields_length.symm, fun hps hidx hm i => ?_⟩
  exact PropElim.occ_rel (SynRel.levels U) hSrel (propParams_levels hls hls' heq) hErel
    hps hidx hm i

end InductiveSignature.NativeRecursorData

end Lean4Lean
