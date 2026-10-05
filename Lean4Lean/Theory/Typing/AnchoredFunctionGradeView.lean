import Lean4Lean.Theory.Typing.AnchoredVariableTransfer

/-! Temporary grade changes for source function observations. A variable trace
may use a higher internal grade than its leaves and result. Raising the whole
function, adapting its input there, and lowering again preserves the original
function grade and every source leaf. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def raiseAtom {n : Nat} : (N : Nat) → n ≤ N → Atom n → Atom N
  | 0, h, a => (show n = 0 by omega) ▸ a
  | N + 1, h, a =>
    if he : n = N + 1 then he ▸ a
    else .pad (raiseAtom N (by omega) a)

@[simp] theorem raiseAtom_self (a : Atom n) : raiseAtom n (Nat.le_refl n) a = a := by
  cases n <;> simp [raiseAtom]

theorem raiseAtom_step {n N : Nat} (h : n ≤ N) (a : Atom n) :
    raiseAtom (N + 1) (Nat.le_succ_of_le h) a = .pad (raiseAtom N h a) := by
  simp only [raiseAtom, dif_neg (show n ≠ N + 1 by omega)]

theorem raiseProfile_singleton {n N : Nat} (h : n ≤ N) (a : Atom n) :
    raiseProfile N h (.singleton a) = .singleton (raiseAtom N h a) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simp only [raiseProfile_self, raiseAtom_self]
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, raiseAtom_step hn, ih hn, Profile.pad_singleton]

def raiseKey {n : Nat} (N : Nat) (h : n ≤ N) (key : Key n) : Key N :=
  { domain := key.domain, anchor := key.anchor, input := raiseProfile N h key.input }

@[simp] theorem raiseKey_self (key : Key n) : raiseKey n (Nat.le_refl n) key = key := by
  cases key
  simp only [raiseKey, raiseProfile_self]

theorem raiseKey_step {n N : Nat} (h : n ≤ N) (key : Key n) :
    raiseKey (N + 1) (Nat.le_succ_of_le h) key = (raiseKey N h key).pad := by
  simp only [raiseKey, Key.pad, raiseProfile_step h]

/-- Only existing pad/function commutations occur in this view. -/
noncomputable def functionGradeView {n N : Nat} (h : n ≤ N)
    (key : Key n) (output : Atom n) :
    AtomView env U registry Γ
      (raiseAtom (N + 1) (Nat.succ_le_succ h) (.fn key output))
      (.fn (raiseKey N h key) (raiseAtom N h output)) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simpa only [raiseAtom_self, raiseKey_self] using
      (AtomView.refl (env := env) (U := U) (registry := registry) (Γ := Γ) (n := 1) (.fn key output))
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n
      simpa only [raiseAtom_self, raiseKey_self] using
        (AtomView.refl (env := env) (U := U) (registry := registry) (Γ := Γ) (n := N + 2) (.fn key output))
    · have hn : n ≤ N := by omega
      simpa only [raiseAtom_step hn, raiseAtom_step (Nat.succ_le_succ hn), raiseKey_step hn] using
        (AtomView.trans (AtomView.pad (ih hn))
          (AtomView.commutePadFn (raiseKey N hn key) (raiseAtom N hn output)))

noncomputable def Obs.raise {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : Obs env U registry Γ locals σ expression demand footprint) :
    Obs env U registry Γ locals σ expression (raiseProfile N h demand) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact observation
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using Obs.pad (ih hn)

noncomputable def Obs.lower {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : Obs env U registry Γ locals σ expression
      (raiseProfile N h demand) footprint) :
    Obs env U registry Γ locals σ expression demand footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact observation
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn] at observation
      exact ih hn (Obs.unpad observation)

/-- Adapt a function observation using the exact leaves of an observed
variable, even when that variable trace temporarily visits higher grades.
The resulting function keeps its original grade, domain, anchor, output and
footprint; only its input demand becomes the padded union of those leaves. -/
noncomputable def Obs.inputFromVariableTrace {key : Key n} {output : Atom n}
    (henv : env.Ordered)
    (function : Obs env U registry Γ locals σ expression (Profile.fn key output) functionFootprint)
    (trace : VariableTrace env U registry Γ i key.input variableFootprint)
    (bounded : ∀ j need, (j, need) ∈ variableFootprint → need.rank ≤ n) :
    Obs env U registry Γ locals σ expression
      (Profile.fn (inputKey key (variableFootprint.atGrade n)) output) functionFootprint := by
  let N := trace.height
  have hn : n ≤ N := trace.output_bound
  let key' := inputKey key (variableFootprint.atGrade n)
  have forward : ProfileView env U registry Γ
      (raiseKey N hn key').input (raiseKey N hn key).input := by
    simpa only [raiseKey, key', inputKey, Footprint.atGrade_raise hn bounded] using
      trace.normalize N (Nat.le_refl _)
  have lifted := function.raise (Nat.succ_le_succ hn)
  rw [Profile.fn, raiseProfile_singleton] at lifted
  have exposed := Obs.view lifted (functionGradeView hn key output)
  have changed := Obs.view exposed (AtomView.input forward (forward.inverse henv))
  have lowered := Obs.view changed ((functionGradeView hn key' output).inverse henv)
  apply Obs.lower (Nat.succ_le_succ hn)
  simpa only [Profile.fn, raiseProfile_singleton] using lowered

end Lean4Lean.AnchoredSource
