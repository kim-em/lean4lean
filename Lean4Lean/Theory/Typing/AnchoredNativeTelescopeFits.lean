import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree
import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
import Lean4Lean.Theory.Typing.AnchoredSourceSubstitution

/-! Build the actual native argument invariant along the concrete observer's
registered telescope. The stored anchor guards and domain certificates supply
every fitting entry; no argument-typing inversion or semantic callback occurs. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem onCtx_tail (h : OnCtx (later ++ source) P) : OnCtx source P := by
  induction later with
  | nil => exact h
  | cons _ _ ih => exact ih h.1

private theorem domain_formation {env : VEnv} {U : Nat}
    {domains : List VExpr} {index : Nat} {domain : VExpr}
    (formed : OnCtx domains.reverse (env.IsType U))
    (origin : domains[index]? = some domain) :
    env.IsType U (domains.take index).reverse domain := by
  have h : OnCtx ((domains.drop (index + 1)).reverse ++ (domains.take (index + 1)).reverse)
      (env.IsType U) := by
    rw [← List.reverse_append, List.take_append_drop]
    exact formed
  have formedPrefix :=  onCtx_tail h
  rw [List.take_add_one, origin] at formedPrefix
  simp only [Option.toList_some, List.reverse_append, List.reverse_singleton,
    List.singleton_append, OnCtx] at formedPrefix
  exact formedPrefix.2

private theorem capture_append (values : List VExpr) (value : VExpr) :
    nativeCaptureSubst (values ++ [value]) = (nativeCaptureSubst values).cons value := by
  funext i
  cases i with
  | zero => simp [nativeCaptureSubst, Subst.cons]
  | succ i =>
    simp only [nativeCaptureSubst, List.length_append, List.length_singleton, Subst.cons]
    by_cases hi : i < values.length
    · rw [dif_pos (by omega), dif_pos hi, List.getElem_append_left (by omega)]
      congr 1 <;> omega
    · rw [dif_neg (by omega), dif_neg hi]
      congr 1 <;> omega

/-- A terminal descendant together with its finite native-argument valuation.
Intermediate domain-certificate demands remain in the valuation. -/
structure NativeTerminalFits (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) where
  arguments : List VExpr
  rank : Nat
  demand : Profile rank
  footprint : Footprint
  terminal : NativeConstantTerminal env U registry target signature arguments demand footprint
  available : Valuation
  closed : available.AtomClosed
  raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst arguments)
    (signature.domains.take arguments.length).reverse
  fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
    (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst arguments) available
  resources : footprint.Available available

theorem NativeTelescopeTree.terminalFits
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (formed : OnCtx signature.domains.reverse (env.IsType U))
    {arguments : List VExpr} {demand : Profile n} {footprint : Footprint}
    (tree : NativeTelescopeTree env U registry target signature arguments demand footprint)
    {available : Valuation} (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst arguments)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst arguments) available)
    (resources : footprint.Available available) :
    Nonempty (NativeTerminalFits env U registry target signature) := by
  match tree with
  | .terminal leaf => exact ⟨⟨arguments, _, demand, footprint, leaf, available, closed, raw, fits, resources⟩⟩
  | .binder (domain := domain) (key := key) (bodyFootprint := bodyFoot) origin domainCode guard body pack covered =>
    have domainResources : _ := fun i need hm => resources i need (List.mem_append_left _ hm)
    have externalResources : _ := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨level, domainTyped⟩ := domain_formation formed origin
    have anchorTyped := guard.path.cast guard.anchor.2.1
    obtain ⟨_, _, _, _, _, anchorRelated⟩ := guard.anchor.2.2
    have anchor := Related.convert henv guard.inputTyped guard.domains anchorRelated
    have pushedRaw : Ctx.SubstEq env U target
        ((nativeCaptureSubst arguments).cons key.anchor)
        ((nativeCaptureSubst arguments).cons key.anchor)
        (domain :: (signature.domains.take arguments.length).reverse) :=
      .cons raw domainTyped anchorTyped
    have bounds := pack.atomized_localNeeds
    have pushedFits := fits.pushDiagonal henv hTarget domainCode domainResources guard.inputTyped anchor
      (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) (fun need hm => (bounds need hm).1)
      (fun need hm atom ha => covered atom ((bounds need hm).2 atom ha))
    have sourceEq : (signature.domains.take (arguments ++ [key.anchor]).length).reverse =
        domain :: (signature.domains.take arguments.length).reverse := by
      simp only [List.length_append, List.length_singleton, List.take_add_one, origin,
        Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append]
    have localsEq : List.range (arguments ++ [key.anchor]).length = Locals.push (List.range arguments.length) := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    apply body.terminalFits henv hTarget formed (Valuation.push_atomized_closed closed _)
    · simpa only [sourceEq, capture_append] using pushedRaw
    · simpa only [sourceEq, localsEq, capture_append] using pushedFits
    · exact pack.available_atomized_localNeeds externalResources
termination_by sizeOf tree

/-- At the bare head the source valuation is literally empty; all terminal
argument capabilities are produced by the finite registered binder tree. -/
theorem NativeConstantObservation.terminalFits
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {demand : Profile n}
    (observation : NativeConstantObservation env U registry target name levels demand)
    (formed : OnCtx observation.signature.domains.reverse (env.IsType U)) :
    Nonempty (NativeTerminalFits env U registry target observation.signature) := by
  apply observation.tree.terminalFits henv hTarget formed
    (available := fun _ => []) (by intro _ _ h; cases h) (.nil) (.nil)
  intro _ _ h
  cases h

end Lean4Lean.AnchoredSource.Adapted
