import Lean4Lean.Theory.Typing.AnchoredNativeSpineCertificate
import Lean4Lean.Theory.Typing.AnchoredNativeArgumentLedger

/-! A code-only path through the original argument spine. Unlike a value
demand path, the final requested Pi row may have empty output. Every prior
requirement retains an actual observer of the original argument expression. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive NativeCodePath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) :
    List VExpr → {n : Nat} → Profile n → {N : Nat} → Profile N → Type where
  | nil : NativeCodePath env U registry target locals σ available [] profile profile
  | snoc
      (frame : ApplicationCodeInput env U registry target locals σ available A B a result before)
      (prior : NativeCodePath env U registry target locals σ available arguments frame.profile root) :
      NativeCodePath env U registry target locals σ available (arguments ++ [a]) result root

structure NativeCodeRoot (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (profile : Profile n) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  rank : Nat
  support : Profile rank
  footprint : Footprint
  certificate : CodeCert env U registry target locals σ (info.type.instL levels) support footprint
  resources : footprint.Available available
  path : NativeCodePath env U registry target locals σ available arguments profile support

noncomputable def NativeSpineCertificate.codeRoot
    (spine : NativeSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) :
    NativeCodeRoot sourceEnv env U registry target locals σ available name levels
      expression.getAppFnArgs.2 profile := by
  induction spine with
  | constant lookup formation certificate resources =>
    exact ⟨_, lookup, _, _, _, certificate, resources, .nil⟩
  | application frame function ih =>
    exact ⟨ih.info, ih.lookup, ih.rank, ih.support, ih.footprint, ih.certificate,
      ih.resources, by simpa only [getAppFnArgs_app] using NativeCodePath.snoc frame ih.path⟩
  | conversion edge certificate transfer term ih => exact ih

/-- A finite prior valuation is backed by actual source observers of its
arguments. This invariant is constructed when advancing each original frame,
rather than assumed from target typing of its realized anchor. -/
def NativeObservedValuation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) (prior : Valuation) : Prop :=
  ∀ index need, need ∈ prior index → ∃ bound : index < arguments.length,
    ∃ footprint, Nonempty (Obs env U registry target locals σ
      arguments[arguments.length - 1 - index] need.profile footprint) ∧
      footprint.Available available

theorem NativeObservedValuation.empty :
    NativeObservedValuation env U registry target locals σ available [] (fun _ => []) := by
  intro _ _ h
  cases h

theorem NativeObservedValuation.ledger
    (observed : NativeObservedValuation env U registry target locals σ available arguments prior)
    (resources : required.Available prior) :
    Nonempty (NativeArgumentLedger env U registry target locals σ available arguments required) := by
  induction required with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    obtain ⟨bound, footprint, ⟨observation⟩, leaves⟩ := observed index need
      (resources index need List.mem_cons_self)
    obtain ⟨tail⟩ := ih (fun i n h => resources i n (List.mem_cons_of_mem _ h))
    exact ⟨.cons bound observation leaves tail⟩

theorem NativeObservedValuation.push
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available prior : Valuation}
    {arguments : List VExpr} {argument : VExpr} {needs : List Need}
    (observed : NativeObservedValuation env U registry target locals σ available arguments prior)
    (closed : available.AtomClosed)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ argument input footprint)
    (resources : footprint.Available available)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    NativeObservedValuation env U registry target locals σ available (arguments ++ [argument])
      (Valuation.push needs prior) := by
  intro index need member
  cases index with
  | zero =>
    have included := covered need member
    have bound := bounded need member
    simp only [Need.atGrade, dif_pos bound] at included
    obtain ⟨required, ⟨selected⟩, selection⟩ := observation.subprofile included
    refine ⟨by simp, required, ⟨?_⟩, selection.available_closed resources closed⟩
    simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
      Nat.sub_zero, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero] using selected.lower bound
  | succ index =>
    obtain ⟨bound, required, ⟨old⟩, leaves⟩ := observed index need member
    have position : (arguments ++ [argument]).length - 1 - (index + 1) =
        arguments.length - 1 - index := by simp only [List.length_append, List.length_singleton]; omega
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega,
      required, ⟨?_⟩, leaves⟩
    have same : (arguments ++ [argument])[(arguments ++ [argument]).length - 1 - (index + 1)] =
        arguments[arguments.length - 1 - index] := by
      simp only [position]
      exact List.getElem_append_left (by omega)
    exact same.symm ▸ old

end Lean4Lean.AnchoredSource.Adapted
