import Lean4Lean.Theory.Typing.AnchoredSourceObservation
import Lean4Lean.Theory.Typing.AnchoredProfileViews

/-! Normalize the actual leaves of a variable observation at one common
grade. Empty demands retain their grade bounds. No source demand is replaced by a larger available valuation. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private noncomputable def pairedRefl (p : Profile n) : ProfileView env U registry Γ p p := by
  induction p with
  | nil => exact .nil
  | cons a rest ih => exact .cons (.refl a) ih

private noncomputable def pairedAppend {p q p' q' : Profile n}
    (first : ProfileView env U registry Γ p q)
    (second : ProfileView env U registry Γ p' q') :
    ProfileView env U registry Γ (p.union p') (q.union q') := by
  match p, q, first with
  | _, _, .nil => exact second
  | _, _, .cons head tail => exact .cons head (pairedAppend tail second)
termination_by sizeOf first
decreasing_by all_goals simp_wf; omega

private noncomputable def pairedTrans {p q r : Profile n}
    (first : ProfileView env U registry Γ p q)
    (second : ProfileView env U registry Γ q r) : ProfileView env U registry Γ p r := by
  match p, q, first with
  | _, _, .nil => cases second; exact .nil
  | _, _, .cons head tail =>
    cases second with
    | cons head' tail' => exact .cons (.trans head head') (pairedTrans tail tail')
termination_by sizeOf first
decreasing_by all_goals simp_wf; omega

private noncomputable def pairedPad {p q : Profile n}
    (view : ProfileView env U registry Γ p q) :
    ProfileView env U registry Γ p.pad q.pad := by
  match p, q, view with
  | _, _, .nil => exact .nil
  | _, _, .cons head tail => exact .cons (.pad head) (pairedPad tail)
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

private noncomputable def pairedRaise {n N : Nat} {p q : Profile n} (h : n ≤ N)
    (view : ProfileView env U registry Γ p q) :
    ProfileView env U registry Γ (raiseProfile N h p) (raiseProfile N h q) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact view
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using view
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using pairedPad (ih hn)

/-- Exactly the constructors that can finish at one source variable. -/
inductive VariableTrace (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (i : Nat) : {n : Nat} → Profile n → Footprint → Type where
  | leaf (demand : Profile n) : VariableTrace env U registry Γ i demand [(i, ⟨n, demand⟩)]
  | empty : VariableTrace env U registry Γ i (n := n) .empty []
  | union {p q : Profile n} (left : VariableTrace env U registry Γ i p first)
      (right : VariableTrace env U registry Γ i q second) :
      VariableTrace env U registry Γ i (p.union q) (first ++ second)
  | view {a b : Atom n} (source : VariableTrace env U registry Γ i (.singleton a) footprint)
      (change : AtomView env U registry Γ a b) :
      VariableTrace env U registry Γ i (.singleton b) footprint
  | pad {p : Profile n} (source : VariableTrace env U registry Γ i p footprint) :
      VariableTrace env U registry Γ i p.pad footprint
  | unpad {p : Profile n} (source : VariableTrace env U registry Γ i p.pad footprint) :
      VariableTrace env U registry Γ i p footprint
  | rowShift {key : Key n} {output : Atom n} (source : VariableTrace env U registry Γ i (Profile.fn key output) footprint) :
      VariableTrace env U registry Γ i (Profile.fn key.pad (.pad output)) footprint

noncomputable def VariableTrace.ofObs
    (observation : Obs env U registry Γ locals σ (.bvar i) demand footprint) :
    VariableTrace env U registry Γ i demand footprint :=
  match observation with
  | .var _ _ _ demand => .leaf demand
  | .empty => .empty
  | .union left right => .union (ofObs left) (ofObs right)
  | .view source change => .view (ofObs source) change
  | .pad source => .pad (ofObs source)
  | .unpad source => .unpad (ofObs source)
  | .rowShift source => .rowShift (ofObs source)

def VariableTrace.height : {n : Nat} → {demand : Profile n} → {footprint : Footprint} →
    VariableTrace env U registry Γ i demand footprint → Nat
  | n, _, _, .leaf _ => n
  | n, _, _, .empty => n
  | _, _, _, .union left right => max left.height right.height
  | _, _, _, .view source _ => source.height
  | n + 1, _, _, .pad source => max (n + 1) source.height
  | _, _, _, .unpad source => source.height
  | n + 2, _, _, .rowShift source => max (n + 2) source.height

theorem VariableTrace.output_bound
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint) : n ≤ trace.height := by
  induction trace with
  | leaf | empty => exact Nat.le_refl _
  | union left right ihleft ihright => exact Nat.le_trans ihleft (Nat.le_max_left _ _)
  | view source change ih => exact ih
  | pad | rowShift => exact Nat.le_max_left _ _
  | unpad source ih => exact Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) ih

theorem VariableTrace.leaf_bound
    (trace : VariableTrace env U registry Γ i demand footprint)
    (hm : (j, need) ∈ footprint) : need.rank ≤ trace.height := by
  induction trace with
  | leaf demand => cases List.mem_singleton.mp hm; exact Nat.le_refl _
  | empty => cases hm
  | union left right ihleft ihright =>
    rcases List.mem_append.mp hm with h | h
    · exact Nat.le_trans (ihleft h) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihright h) (Nat.le_max_right _ _)
  | view source change ih => exact ih hm
  | pad source ih => exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)
  | unpad source ih => exact ih hm
  | rowShift source ih => exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

/-- Every actual leaf is retained, in its original order, after padding to
the chosen common grade. This is a paired transformation, not a projection. -/
noncomputable def VariableTrace.normalize
    (trace : VariableTrace env U registry Γ i (demand : Profile n) footprint)
    (N : Nat) (hN : trace.height ≤ N) :
    ProfileView env U registry Γ (footprint.atGrade N)
      (raiseProfile N (Nat.le_trans trace.output_bound hN) demand) := by
  induction trace with
  | leaf demand =>
    simp only [height] at hN
    simpa only [Footprint.atGrade, List.flatMap_cons, List.flatMap_nil,
      Need.atGrade, dif_pos hN, List.append_nil] using pairedRefl (env := env) (U := U) (registry := registry) (Γ := Γ) (raiseProfile N hN demand)
  | empty =>
    rw [raiseProfile_empty]
    exact .nil
  | union left right ihleft ihright =>
    have hl : left.height ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
    have hr : right.height ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
    simpa only [Footprint.atGrade_append, raiseProfile_union] using
      pairedAppend (ihleft hl) (ihright hr)
  | view source change ih =>
    exact pairedTrans (ih hN)
      (pairedRaise (Nat.le_trans source.output_bound hN) (.cons change .nil))
  | pad source ih =>
    have hs : source.height ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
    have hout : _ + 1 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
    simpa only [raiseProfile_pad hout] using ih hs
  | unpad source ih =>
    simpa only [raiseProfile_pad] using ih hN
  | @rowShift n footprint key output source ih =>
    have hs : source.height ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
    have hout : n + 2 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
    have bridge := pairedRaise hout
      (ProfileView.cons (AtomView.commutePadFn (env := env) (U := U)
        (registry := registry) (Γ := Γ) key output) ProfileView.nil)
    change ProfileView env U registry Γ
      (raiseProfile N hout (Profile.fn key output).pad)
      (raiseProfile N hout (Profile.fn key.pad (.pad output))) at bridge
    have bridge' : ProfileView env U registry Γ
        (raiseProfile N (Nat.le_trans source.output_bound hs) (Profile.fn key output))
        (raiseProfile N hout (Profile.fn key.pad (.pad output))) := by
      simpa only [raiseProfile_pad hout] using bridge
    exact pairedTrans (ih hs) bridge'

/-- A concrete factor of an existing variable observation, including an
explicit bound on every empty or nonempty source demand. -/
theorem Obs.variable_factor
    (observation : Obs env U registry Γ locals σ (.bvar i) (demand : Profile n) footprint) :
    ∃ N, ∃ hn : n ≤ N,
      (∀ j need, (j, need) ∈ footprint → need.rank ≤ N) ∧
      Nonempty (ProfileView env U registry Γ (footprint.atGrade N) (raiseProfile N hn demand)) := by
  let trace := VariableTrace.ofObs observation
  exact ⟨trace.height, trace.output_bound, fun _ _ h => trace.leaf_bound h,
    ⟨trace.normalize trace.height (Nat.le_refl _)⟩⟩

end Lean4Lean.AnchoredSource
