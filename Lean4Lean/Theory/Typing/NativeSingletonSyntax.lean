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
end Lean4Lean
