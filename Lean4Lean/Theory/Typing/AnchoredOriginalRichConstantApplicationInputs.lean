import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstValuePruning
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstApplicationShared

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem inputNeed {profile : Profile n} (member : need ∈ recipeDependencyInputs profile) :
    need.rank ≤ n ∧ (need.atGrade n).atoms ⊆ profile.atoms := by
  simp only [recipeDependencyInputs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    refine ⟨Nat.le_refl _, ?_⟩
    intro chosen member
    simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self] using member
  · obtain ⟨atom, belongs, equal⟩ := List.mem_map.mp member
    cases equal
    refine ⟨Nat.le_refl _, ?_⟩
    intro chosen member
    have equal := List.mem_singleton.mp (show chosen ∈ [atom] from by
      simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self, Profile.singleton, Profile.atoms, Profile.mk] using member)
    simpa only [equal] using belongs

/-- Evaluate the actual rich variable argument under its original BinderPack.
Nested charged programs are traversed, rather than treated as already legacy. -/
theorem RichObs.recipeVariableArgumentDemand
    {node : EndpointState sourceEnv U source (.bvar 0) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (argument : RichObs sourceEnv env U registry target node locals σ (rawInput : Profile n) argumentFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput requested)
    (pack : BinderPack n packed (functionFootprint ++ argumentFootprint) outside)
    (covered : packed.atoms ⊆ keyInput.atoms)
    (closed : available.AtomClosed) (resources : outside.Available available) :
    Nonempty (RecipeVariableDemand env U registry target keyInput requested) := by
  have supplied := BinderPack.dependencySupply pack (env := env) (U := U) (registry := registry)
    (target := target) covered (fun index need member =>
      RecipeVariableDependency.leaf (resources index need member))
  have evaluated := argument.dependencyModel (recipeDependencyInputs.closed closed)
    (fun index need member => supplied index need (List.mem_append_right _ member))
  simp only [RecipeDependencyProfile] at evaluated
  obtain ⟨fp, ⟨trace⟩, available⟩ := evaluated
  have info : ∀ index need, (index, need) ∈ fp →
      need.rank ≤ n ∧ (need.atGrade n).atoms ⊆ keyInput.atoms := by
    intro index need member
    have indexEq := trace.indices member
    subst index
    exact inputNeed (available 0 need member)
  have included : (fp.atGrade n).atoms ⊆ keyInput.atoms := by
    intro atom member
    obtain ⟨⟨index, need⟩, selected, belongs⟩ := List.mem_flatMap.mp member
    exact (info index need selected).2 belongs
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  refine ⟨⟨fp.atGrade n, included, N, hn, ?_⟩⟩
  rw [← Footprint.atGrade_raise hn (fun index need member => (info index need member).1)]
  exact (trace.normalize henv hscoped formed N ht).comp
    (GeneralNormalProfileAdapter.raise henv hscoped formed hn adapter)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel

/-- Both inputs are computed from the actual rich native application program.
The function is closed by value pruning; the argument's full nested recipe
program is evaluated through the original enclosing BinderPack. -/
theorem nativeRichConstantApplicationInputs {key : Key n} {output : Atom n}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (function : EndpointState owner.selected.origin.source U source (.const name levels) (.forallE A B))
    (argument : EndpointState owner.selected.origin.source U source (.bvar 0) A)
    (fn : RichObs owner.selected.origin.source env U registry target function locals σ
      (Profile.fn key output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument locals σ rawInput argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (covered : packed.atoms ⊆ outerInput.atoms)
    (closed : available.AtomClosed) (resources : outside.Available available) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output),
      ∃ demand : RecipeVariableDemand env U registry target outerInput key.input,
        packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
        ∀ policy, packet.query.headDepth policy ≤ fn.headDepth policy := by
  obtain ⟨packet, nameEq, ownerEq, depth⟩ := canonicalConstSiteOfFunction owner function fn
  obtain ⟨demand⟩ := arg.recipeVariableArgumentDemand henv hscoped formed adapter pack covered closed resources
  exact ⟨packet, demand, nameEq, ownerEq, depth⟩

end Lean4Lean.AnchoredSource.Adapted
