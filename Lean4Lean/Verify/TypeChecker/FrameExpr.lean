import Lean4Lean.Verify.TypeChecker.FrameBasic
import Lean4Lean.Verify.Inductive.Recursor.Structure
import Lean4Lean.Verify.TypeChecker.Basic

/-!
# Frame lemma: ghost-freeness of expression operations

`GF G` is preserved by every pure expression operation the checker applies to its inputs.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

/-- Every element of the array is ghost-free. -/
def GFArr (G : FVarId → Prop) (arr : Array Expr) : Prop := ∀ a ∈ arr, GF G a

theorem GF.default : GF G (default : Expr) := FVarsIn.default

theorem GF.panic : GF G (panicWithPosWithDecl m d l c msg : Expr) := by
  simp only [panicWithPosWithDecl]; exact GF.default

theorem GFArr.getElem! {arr : Array Expr} (h : GFArr G arr) (i : Nat) : GF G arr[i]! := by
  rw [Array.getElem!_eq_getD]; unfold Array.getD; split
  · exact h _ (Array.getElem_mem _)
  · exact GF.default

theorem GFArr.getElem? {arr : Array Expr} (h : GFArr G arr) {i : Nat} {a : Expr}
    (e : arr[i]? = some a) : GF G a :=
  h _ (Array.mem_of_getElem? e)

theorem GFArr.getElem {arr : Array Expr} (h : GFArr G arr) {i : Nat} (hi : i < arr.size) :
    GF G arr[i] := h _ (Array.getElem_mem _)

theorem GFArr.empty : GFArr G #[] := nofun

theorem GFArr.reverse {arr : Array Expr} (h : GFArr G arr) : GFArr G arr.reverse :=
  fun _ hx => h _ (Array.mem_reverse.1 hx)

theorem GFArr.extract {arr : Array Expr} (h : GFArr G arr) : GFArr G (arr.extract i j) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hx
  exact h _ (Array.getElem_mem _)

open private mkAppRangeAux from Lean.Expr in
theorem GF.mkAppRange {arr : Array Expr} (hf : GF G f) (h : GFArr G arr) :
    GF G (mkAppRange f i j arr) := by
  unfold Lean.mkAppRange
  generalize hk : j - i = k
  induction k generalizing i f with
  | zero => rw [mkAppRangeAux, if_neg (by omega)]; exact hf
  | succ k ih => rw [mkAppRangeAux, if_pos (by omega)]; exact ih ⟨hf, h.getElem! i⟩ (by omega)

open private mkAppRevRangeAux from Lean.Expr in
theorem GF.mkAppRevRange {arr : Array Expr} (hf : GF G f) (h : GFArr G arr) :
    GF G (f.mkAppRevRange i j arr) := by
  unfold Expr.mkAppRevRange
  induction j generalizing f with
  | zero => rw [mkAppRevRangeAux, if_pos (Nat.zero_le _)]; exact hf
  | succ j ih =>
    rw [mkAppRevRangeAux]; split
    · exact hf
    · exact ih ⟨hf, h.getElem! _⟩

theorem GF.getAppFn : ∀ {e : Expr}, GF G e → GF G e.getAppFn
  | .app f _, h => GF.getAppFn (e := f) h.1
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h
  | .lam .., h | .forallE .., h | .letE .., h | .lit .., h | .mdata .., h | .proj .., h => h

theorem GF.getAppArgsRevList {e : Expr} (h : GF G e) : ∀ a ∈ e.getAppArgsRevList, GF G a := by
  induction e <;> simp [Expr.getAppArgsRevList]
  rename_i ih _; exact ⟨h.2, ih h.1⟩

theorem GF.getAppArgs (h : GF G e) : GFArr G e.getAppArgs := by
  rw [Expr.getAppArgs_eq_rev]; intro a ha
  exact GF.getAppArgsRevList h a (by simpa using ha)

theorem GF.getAppRevArgs (h : GF G e) : GFArr G e.getAppRevArgs := by
  rw [Expr.getAppRevArgs_eq]; intro a ha
  exact GF.getAppArgsRevList h a (by simpa using ha)

theorem GF.appArg! : ∀ {e : Expr}, GF G e → GF G e.appArg!
  | .app .., h => h.2
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .lam .., _ | .forallE .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.appArg!] using GF.default

theorem GF.bindingBody! : ∀ {e : Expr}, GF G e → GF G e.bindingBody!
  | .lam .., h | .forallE .., h => h.2
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .app .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.bindingBody!] using GF.default

theorem GF.bindingDomain! : ∀ {e : Expr}, GF G e → GF G e.bindingDomain!
  | .lam .., h | .forallE .., h => h.1
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .sort .., _ | .const .., _
  | .app .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simpa [Expr.bindingDomain!] using GF.default

theorem GF.instantiate1 (h1 : GF G e) (h2 : GF G a) : GF G (e.instantiate1 a) := by
  rw [Expr.instantiate1_eq]; exact FVarsIn.instantiate1 h1 h2

theorem GF.instantiate {arr : Array Expr} (h1 : GF G e) (h2 : GFArr G arr) :
    GF G (e.instantiate arr) := by
  rw [Expr.instantiate_eq]; exact FVarsIn.instantiateList h1 fun a ha => h2 a (by simpa using ha)

theorem GF.instantiateRev {arr : Array Expr} (h1 : GF G e) (h2 : GFArr G arr) :
    GF G (e.instantiateRev arr) := by
  rw [Expr.instantiateRev_eq]; exact h1.instantiate h2.reverse

theorem GF.instantiateRange {arr : Array Expr} (h1 : GF G e) (h2 : GFArr G arr) :
    GF G (e.instantiateRange i j arr) := by
  rw [Expr.instantiateRange_eq]; exact h1.instantiate h2.extract

theorem GF.instantiateRevRange {arr : Array Expr} (h1 : GF G e) (h2 : GFArr G arr) :
    GF G (e.instantiateRevRange i j arr) := by
  rw [Expr.instantiateRevRange_eq]; exact h1.instantiateRev h2.extract

theorem GF.abstractN (h : GF G e) : GF G (e.abstractN xs k) := by
  induction e generalizing k <;> simp_all [Expr.abstractN, FVarsIn]
  split <;> simp_all [FVarsIn]

theorem GF.lowerLooseBVars' (h : GF G e) : GF G (e.lowerLooseBVars' s d) := by
  induction e generalizing s <;> rw [Expr.lowerLooseBVars'] <;> split <;> simp_all [FVarsIn]

theorem GF.instantiateLevelParams (h : GF G e) (hl : ∀ l ∈ ls, l.hasMVar' = false) :
    GF G (e.instantiateLevelParams ps ls) := FVarsIn.instantiateLevelParams h hl

theorem GF.sort_iff : GF G (.sort l) ↔ l.hasMVar' = false := Iff.rfl

theorem GF.sortLevel! : ∀ {e : Expr}, GF G e → e.sortLevel!.hasMVar' = false
  | .sort .., h => h
  | .bvar .., _ | .fvar .., _ | .mvar .., _ | .app .., _ | .const .., _
  | .lam .., _ | .forallE .., _ | .letE .., _ | .lit .., _ | .mdata .., _ | .proj .., _ => by
    simp [Expr.sortLevel!]; rfl

/-! ### `cheapBetaReduce` -/

theorem GF.cheapBetaReduce (h : GF G e) : GF G e.cheapBetaReduce := by
  simp only [Expr.cheapBetaReduce, Id.run]
  split; · exact h
  split; · exact h
  have hargs := h.getAppArgs
  have hcont : ∀ i fn, GF G fn → GF G (Expr.cheapBetaReduce.cont e e.getAppArgs i fn) := by
    intro i fn hfn
    unfold Expr.cheapBetaReduce.cont
    split
    · exact hfn.mkAppRange hargs
    split
    · split
      · exact (hargs.getElem! _).mkAppRange hargs
      · exact GF.panic
    · exact h
  have hloop : ∀ i fn, GF G fn → GF G (Expr.cheapBetaReduce.loop e e.getAppArgs i fn) := by
    intro i fn hfn
    induction fn generalizing i with
    | lam _ _ body _ _ ih =>
      unfold Expr.cheapBetaReduce.loop; split
      · exact ih _ hfn.2
      · exact hcont _ _ hfn
    | _ => unfold Expr.cheapBetaReduce.loop; split <;> exact hcont _ _ hfn
  exact hloop _ _ h.getAppFn

/-! ### Binding over the checker's own free variables -/

/-- Every element of the array is a free variable that is not a ghost. -/
def FVArr (G : FVarId → Prop) (arr : Array Expr) : Prop := ∀ x ∈ arr, ∃ id, x = .fvar id ∧ ¬ G id

theorem FVArr.empty : FVArr G #[] := nofun

theorem FVArr.push {arr : Array Expr} {id : FVarId} (h : FVArr G arr) (hid : ¬ G id) :
    FVArr G (arr.push (.fvar id)) := by
  intro x hx; rcases Array.mem_push.1 hx with hx | rfl
  · exact h _ hx
  · exact ⟨_, rfl, hid⟩

theorem FVArr.gfArr {arr : Array Expr} (h : FVArr G arr) : GFArr G arr := by
  intro x hx; obtain ⟨id, rfl, hid⟩ := h x hx; exact hid

theorem FVArr.eq_map {arr : Array Expr} (h : FVArr G arr) :
    ∃ xs : List FVarId, arr = ⟨xs.map .fvar⟩ ∧ ∀ x ∈ xs, ¬ G x := by
  obtain ⟨l⟩ := arr
  induction l with
  | nil => exact ⟨[], rfl, nofun⟩
  | cons a l ih =>
    obtain ⟨id, rfl, hid⟩ := h a (by simp)
    obtain ⟨xs, eq, hxs⟩ := ih fun x hx => h x (by simp at hx ⊢; exact .inr hx)
    cases eq
    exact ⟨id :: xs, rfl, by simp; exact ⟨hid, hxs⟩⟩

/-- The declarations of a local context at the given variables are ghost-free. -/
def DeclsGF (G : FVarId → Prop) (lctx : LocalContext) (xs : List FVarId) : Prop :=
  ∀ x ∈ xs, ∀ ⦃d⦄, lctx.find? x = some d → GF G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GF G v

theorem value?_ldecl : (LocalDecl.ldecl i f n t v nd k).value? true = some v := by
  cases nd <;> rfl

theorem GF.mkBindingList1N (hb : GF G b)
    (hd : ∀ ⦃d⦄, lctx.find? x = some d → GF G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GF G v) :
    GF G (LocalContext.mkBindingList1N isLambda lctx ys x b) := by
  unfold LocalContext.mkBindingList1N
  split
  · rename_i h; have := (hd h).1
    split
    · exact ⟨GF.abstractN this, hb⟩
    · exact ⟨GF.abstractN this, hb⟩
  · rename_i h; have := hd h
    split
    · exact ⟨GF.abstractN this.1, GF.abstractN (this.2 value?_ldecl), hb⟩
    · exact hb.lowerLooseBVars'
  · exact GF.panic

theorem GF.mkBindingListN (hb : GF G b) (hd : DeclsGF G lctx xs) :
    GF G (LocalContext.mkBindingListN isLambda lctx xs b) := by
  unfold LocalContext.mkBindingListN LocalContext.mkBindingListN.core
  have : ∀ ys : List FVarId, (∀ x ∈ ys, x ∈ xs) → ∀ b : Expr, GF G b →
      GF G (LocalContext.mkBindingListN.go isLambda lctx ys b) := by
    intro ys; induction ys with
    | nil => intro _ b hb; exact hb
    | cons y ys ih =>
      intro hys b hb
      simp only [LocalContext.mkBindingListN.go]
      exact ih (fun x hx => hys x (.tail _ hx)) _
        (GF.mkBindingList1N hb (hd y (hys y (.head _))))
  exact this _ (fun x hx => List.mem_reverse.1 hx) _ hb.abstractN

theorem GhostRel.mkBinding {c₁ c₂ : Context} (hr : GhostRel G c₁ c₂) {arr : Array Expr}
    (hfv : FVArr G arr) (hb : GF G b) :
    c₁.lctx.mkBinding isLambda arr b = c₂.lctx.mkBinding isLambda arr b ∧
    GF G (c₂.lctx.mkBinding isLambda arr b) := by
  obtain ⟨xs, rfl, hxs⟩ := hfv.eq_map
  rw [LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN]
  exact ⟨LocalContext.mkBindingListN_congr_setIndex fun x hx => hr.find? (hxs x hx),
    GF.mkBindingListN hb fun x _ _ hd => hr.decls hd⟩

theorem M.Framed.getLCtx_mkBinding {arr : Array Expr} (hfv : FVArr G arr) (hb : GF G b) :
    M.Framed G (getLCtx >>= fun l => Pure.pure (l.mkBinding isLambda arr b)) (GF G) := by
  intro c₁ c₂ s a s' hr hs e
  have := hr.mkBinding (isLambda := isLambda) hfv hb
  change Except.ok (c₁.lctx.mkBinding isLambda arr b, s) = _ at e
  rw [this.1] at e; cases e
  exact ⟨rfl, this.2, hs, .rfl⟩

theorem RecM.Framed.getLCtx_mkForall {arr : Array Expr} (hfv : FVArr G arr) (hb : GF G b) :
    RecM.Framed G (getLCtx >>= fun l => Pure.pure (l.mkForall arr b)) (GF G) :=
  fun _ _ => M.Framed.getLCtx_mkBinding (isLambda := false) hfv hb

end Lean4Lean.TypeChecker
