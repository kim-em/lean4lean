import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureResources
import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades

/-! Terminal family captures use the original declaration variables, their
literal lookup types, and the retained row domain chains. Grade padding
changes no source leaf and never recomputes a frozen family key. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem captureVariables_succ (count : Nat) :
    constantCaptureVariables (count + 1) = .bvar count :: constantCaptureVariables count := by
  simp only [constantCaptureVariables, List.range_succ, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.map_cons]

private theorem lookup_suffix (suffix source : List VExpr) (A : VExpr) :
    Lookup (suffix ++ A :: source) suffix.length (A.liftN (suffix.length + 1)) := by
  induction suffix with
  | nil => exact .zero
  | cons B suffix ih =>
    simpa only [List.length_cons, List.cons_append, ← liftN_succ] using Lookup.succ (A := B) ih

theorem familySubst_drop (initial : Subst) (values : List VExpr) (index : Nat) :
    familySubst initial values (values.length + index) = initial index := by
  induction values generalizing initial index with
  | nil => simp only [familySubst, List.foldl_nil, List.length_nil, Nat.zero_add]
  | cons value values ih =>
    change familySubst (initial.cons value) values (values.length + 1 + index) = initial index
    simpa only [Nat.add_assoc, Nat.add_comm 1 index, Subst.cons] using
      ih (initial.cons value) (index + 1)

theorem familySubst_liftN (initial : Subst) (values : List VExpr) (expression : VExpr) :
    (expression.liftN values.length).subst (familySubst initial values) = expression.subst initial := by
  rw [liftN_subst]
  congr 1
  funext index
  simpa only [Subst.lift_l, Lift.consN, Lift.liftVar_skipN, Lift.liftVar,
    Nat.add_comm] using familySubst_drop initial values index

theorem familySubst_native (arguments values : List VExpr) :
    familySubst (nativeCaptureSubst arguments) values = nativeCaptureSubst (arguments ++ values) := by
  induction values generalizing arguments with
  | nil => simp only [familySubst, List.foldl_nil, List.append_nil]
  | cons value values ih =>
    change familySubst ((nativeCaptureSubst arguments).cons value) values = _
    rw [← nativeCaptureSubst_append, ih]
    simp only [List.append_assoc, List.singleton_append]

noncomputable def _root_.Lean4Lean.AnchoredSemantics.DomainChain.raise
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    (henv : env.Ordered) {n N : Nat} {input : Profile n} {left right : VExpr} (bound : n ≤ N)
    (chain : DomainChain env U registry target input left right) :
    DomainChain env U registry target (raiseProfile N bound input) left right := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseProfile_self] using chain
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using chain
    · have low : n ≤ N := by omega
      rw [raiseProfile_step low]
      exact (ih low).pad henv

/-- Every retained declared row corresponds to precisely one frozen key. -/
theorem FamilySeededCodeRows.length
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys) : keys.length = domains.length := by
  induction rows with
  | nil => rfl
  | cons original row admission extra bounded covered inputPresent tail ih => exact congrArg Nat.succ ih

/-- Construct the complete terminal capture tree from actual row origins.
The domain chain is moved along source binders syntactically, so variable
interpretation can return to its exact original frozen key domain. -/
theorem FamilySeededCodeRows.captures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target domains : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {required : Footprint} {expression : VExpr} {keys : List FamilyKey}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    Nonempty (FamilyCaptures env U registry target (domains.reverse ++ source) rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor))) (constantCaptureVariables keys.length)
      (FamilyKey.uniform N keys bounded) (FamilyKey.captureFootprint keys)) := by
  induction rows with
  | nil => exact ⟨.nil⟩
  | @cons source A level locals seed available B n key result domains keys
      original row support admission extra bounds covered inputPresent tail ih =>
    have bound := bounded ⟨n, key, support⟩ List.mem_cons_self
    obtain ⟨previous⟩ := ih (fun key member => bounded key (List.mem_cons_of_mem _ member))
    let finalSeed := familySubst (seed.cons key.anchor) (keys.map (·.key.anchor))
    have lookup : Lookup (domains.reverse ++ A :: source) keys.length (A.liftN (keys.length + 1)) := by
      simpa only [List.length_reverse, ← tail.length] using lookup_suffix domains.reverse source A
    have domainEq : (A.liftN (keys.length + 1)).subst finalSeed = A.subst seed := by
      rw [show keys.length + 1 = (keys.map (·.key.anchor)).length + 1 by simp]
      rw [show A.liftN ((keys.map (·.key.anchor)).length + 1) =
        A.lift.liftN (keys.map (·.key.anchor)).length by
          rw [liftN_liftN]; congr 1; omega]
      rw [familySubst_liftN, lift_subst_cons]
    have valueEq : finalSeed keys.length = key.anchor := by
      simpa only [List.length_map, Nat.add_zero, Subst.cons] using
        familySubst_drop (seed.cons key.anchor) (keys.map (·.key.anchor)) 0
    have alignment : DomainChain env U registry target (raiseKey N bound key).input
        (raiseKey N bound key).domain ((A.liftN (keys.length + 1)).subst finalSeed) := by
      rw [domainEq]
      exact row.alignment.raise henv bound
    have observation := (Obs.var (env := env) (U := U) (registry := registry) (target := target)
      tail.terminalLocals finalSeed keys.length key.input).raise bound
    have anchor : RankedData.RequestAdmission env U (relations env U registry N) target
        (raiseDataRequest N bound (⟨key, support⟩ : DataRequest (Profile n)))
        (finalSeed keys.length) (finalSeed keys.length) := by
      rw [valueEq]
      exact RankedData.RequestAdmission.raiseFamily henv bound admission
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      captureVariables_succ, List.map_cons, familySubst, List.foldl_cons,
      FamilyKey.uniform, FamilyKey.request, FamilyKey.captureFootprint, FamilySeededCodeRows.terminalLocals,
      finalSeed] using
      (show Nonempty _ from ⟨FamilyCaptures.cons lookup observation (.refl _) alignment anchor previous⟩)

end Lean4Lean.AnchoredSource.Adapted
