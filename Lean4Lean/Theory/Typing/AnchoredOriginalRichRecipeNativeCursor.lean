import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeInterpretation

/-! A native cursor descends into the retained input program. Unlike deferred
recipe row resolution, this selects an actual stored body certificate and
proves it strictly smaller than the row syntax being opened. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Strengthen `RichRows.rowCertificate` on the very same selected constructor
record. The domain query is unchanged, and the selected body is an actual child
of `rows`. The bound holds simultaneously for arbitrary, even nonmonotone,
head policies. -/
theorem RichRows.nativeCursor
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨{ domainSupport := ambient
                domainFootprint := domainFootprint
                domain := domain
                domainAvailable := domainAvailable
                inputTyped := guard.inputTyped
                alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
                anchor := guard.anchor
                bodyFootprint := _
                body := body
                packed := _
                outside := _
                pack := pack
                covered := covered
                outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) },
        HEq.rfl, ?_, ?_⟩
      · simp_wf
        omega
      · intro policy
        simp only [RichRows.headDepth]
        omega
    · obtain ⟨row, same, smaller, bounded⟩ := tail.nativeCursor domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, same, ?_, ?_⟩
      · simp_wf
        omega
      · intro policy
        have lower := bounded policy
        simp only [RichRows.headDepth]
        omega
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

/-- Opening a native canonical input keeps its actual original body and
binder pack. The cursor enters a strict syntactic child of the retained
certificate, rather than manufacturing another elimination of the parent. -/
theorem RichCodeRecipe.rootNativeCursor
    {strata : EquationStratification env}
    (owner : CanonicalCodeOwner env registry strata name)
    {domainNode : EndpointState owner.selected.origin.source U [] A (.sort u)}
    {bodyNode : EndpointState owner.selected.origin.source U [A] B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert owner.selected.origin.source env U registry target domainNode
      [] realization true ambient domainFootprint)
    (guard : PiGuard env U target realization A B prototypeDomain prototypeBody)
    (rows : RichRows owner.selected.origin.source env U registry target domainNode bodyNode
      [] realization relevant ambient table rowFootprint)
    (resources : (domainFootprint ++ rowFootprint).Available (fun _ => []))
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target [] realization (fun _ => [])
      relevant domainNode bodyNode key result,
      HEq row.domain domain ∧
      sizeOf row.body < sizeOf (RichCert.pi hu hv domain guard rows) ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        (RichCert.pi hu hv domain guard rows).headDepth policy := by
  obtain ⟨row, domainEq, smaller, depth⟩ := rows.nativeCursor domain
    (fun index need member => resources index need (List.mem_append_left _ member))
    (fun index need member => resources index need (List.mem_append_right _ member)) member
  refine ⟨row, domainEq, ?_, ?_⟩
  · simp_wf
    omega
  · intro policy
    simpa only [RichCert.headDepth] using depth policy

/-- The native cursor's next original world is the canonical input world,
not an uncharged body in the caller source. Its exact call key decreases
before any subsequent body compilation is attempted. -/
theorem RichCodeRecipe.rootNativeCursor_opening
    {strata : EquationStratification env}
    (owner : CanonicalCodeOwner env registry strata name)
    {domainNode : EndpointState owner.selected.origin.source U [] A (.sort u)}
    {bodyNode : EndpointState owner.selected.origin.source U [A] B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert owner.selected.origin.source env U registry target domainNode
      [] realization true ambient domainFootprint)
    (guard : PiGuard env U target realization A B prototypeDomain prototypeBody)
    (rows : RichRows owner.selected.origin.source env U registry target domainNode bodyNode
      [] realization relevant ambient table rowFootprint)
    (resources : (domainFootprint ++ rowFootprint).Available (fun _ => []))
    (member : (key, result) ∈ table)
    (cutoffBound : cutoff ≤ strata.rules.length)
    (bounded : EquationStratifiedFuel.WithinAbove cutoff fuel
      (EquationStratifiedFuel.headDepth owner.selected.ordinal
        (fun control => (RichCert.pi hu hv domain guard rows).stratifiedDepth
          (strata.headOrdinal registry) control)))
    (constants schedule : Nat) :
    (∃ row : RichPiRowCertificate env U registry target [] realization (fun _ => [])
      relevant domainNode bodyNode key result,
      HEq row.domain domain ∧
      sizeOf row.body < sizeOf (RichCert.pi hu hv domain guard rows) ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        (RichCert.pi hu hv domain guard rows).headDepth policy) ∧
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (owner.selected.ordinal - 1)
        (fun control => (RichCert.pi hu hv domain guard rows).stratifiedDepth
          (strata.headOrdinal registry) control)
        owner.selected.origin.ordered.constantCount
        (recipeRootSchedule owner (.pi hu hv domainNode bodyNode)))
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule) := by
  exact ⟨RichCodeRecipe.rootNativeCursor owner hu hv domain guard rows resources member,
    EquationStratifiedFuel.openingDecrease owner.selected.ordinal_pos
      owner.selected.ordinal_le cutoffBound bounded constants schedule
      owner.selected.origin.ordered.constantCount
      (recipeRootSchedule owner (.pi hu hv domainNode bodyNode))⟩

/-- Conversion/reference prefixes retain the same selected native body;
the charged original remains the actual prefix start. -/
theorem RichCodeRecipe.rootRoutedNativeCursor_opening
    {strata : EquationStratification env}
    (owner : CanonicalCodeOwner env registry strata name)
    {domainNode : EndpointState owner.selected.origin.source U [] A (.sort u)}
    {bodyNode : EndpointState owner.selected.origin.source U [A] B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert owner.selected.origin.source env U registry target domainNode
      [] realization true ambient domainFootprint)
    (guard : PiGuard env U target realization A B prototypeDomain prototypeBody)
    {first : EndpointState owner.selected.origin.source U [] (.forallE A B) (.sort level)}
    (path : PrefixRoute owner.selected.origin.source U [] (.forallE A B)
      first (.pi hu hv domainNode bodyNode))
    (rows : RichRows owner.selected.origin.source env U registry target domainNode bodyNode
      [] realization relevant ambient table rowFootprint)
    (resources : (domainFootprint ++ rowFootprint).Available (fun _ => []))
    (member : (key, result) ∈ table)
    (cutoffBound : cutoff ≤ strata.rules.length)
    (bounded : EquationStratifiedFuel.WithinAbove cutoff fuel
      (EquationStratifiedFuel.headDepth owner.selected.ordinal
        (fun control => (RichCert.route path (RichCert.pi hu hv domain guard rows)).stratifiedDepth
          (strata.headOrdinal registry) control)))
    (constants schedule : Nat) :
    (∃ row : RichPiRowCertificate env U registry target [] realization (fun _ => [])
      relevant domainNode bodyNode key result,
      HEq row.domain domain ∧
      sizeOf row.body < sizeOf (RichCert.route path (RichCert.pi hu hv domain guard rows)) ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        (RichCert.route path (RichCert.pi hu hv domain guard rows)).headDepth policy) ∧
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (owner.selected.ordinal - 1)
        (fun control => (RichCert.route path (RichCert.pi hu hv domain guard rows)).stratifiedDepth
          (strata.headOrdinal registry) control)
        owner.selected.origin.ordered.constantCount
        (recipeRootSchedule owner first))
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule) := by
  obtain ⟨row, exactDomain, smaller, depth⟩ :=
    RichCodeRecipe.rootNativeCursor owner hu hv domain guard rows resources member
  refine ⟨⟨row, exactDomain, ?_, ?_⟩, ?_⟩
  · apply Nat.lt_trans smaller
    simp_wf
    omega
  · intro policy
    simpa only [RichCert.headDepth] using depth policy
  · exact EquationStratifiedFuel.openingDecrease owner.selected.ordinal_pos
      owner.selected.ordinal_le cutoffBound bounded constants schedule
      owner.selected.origin.ordered.constantCount (recipeRootSchedule owner first)

/-- Root level alignment is retained as syntax correspondence. In particular,
this does not assert the raw expression equality required by ordinary R. -/
theorem RichCodeRecipe.rootNativeCursor_aligned
    {strata : EquationStratification env}
    (owner : CanonicalCodeOwner env registry strata name)
    {domainNode : EndpointState owner.selected.origin.source U [] A (.sort u)}
    {bodyNode : EndpointState owner.selected.origin.source U [A] B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert owner.selected.origin.source env U registry target domainNode
      [] realization true ambient domainFootprint)
    (guard : PiGuard env U target realization A B prototypeDomain prototypeBody)
    (rows : RichRows owner.selected.origin.source env U registry target domainNode bodyNode
      [] realization relevant ambient table rowFootprint)
    (resources : (domainFootprint ++ rowFootprint).Available (fun _ => []))
    (member : (key, result) ∈ table)
    (expressionEq : EqUpToLevels U (.forallE A B) expression) :
    ∃ destinationDomain destinationBody,
      expression = VExpr.forallE destinationDomain destinationBody ∧
      EqUpToLevels U A destinationDomain ∧ EqUpToLevels U B destinationBody ∧
      ∃ row : RichPiRowCertificate env U registry target [] realization (fun _ => [])
        relevant domainNode bodyNode key result,
        HEq row.domain domain ∧
        sizeOf row.body < sizeOf (RichCert.pi hu hv domain guard rows) ∧
        ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
          (RichCert.pi hu hv domain guard rows).headDepth policy := by
  cases expressionEq with
  | forallE domainEq bodyEq =>
    exact ⟨_, _, rfl, domainEq, bodyEq,
      RichCodeRecipe.rootNativeCursor owner hu hv domain guard rows resources member⟩

/-- Pending eliminations retain the actual root's named mask. Resource
transfers may add demands, but do not make the original opening disappear. -/
theorem RichRecipeContext.rootDepth
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe) (policy : Name → Nat → Nat) :
    input.recipe.headDepth policy ≤ recipe.headDepth policy := by
  induction pending with
  | root => exact Nat.le_refl _
  | domain _ ih | body _ _ _ ih | fixedBody _ _ _ ih | action _ _ ih => simpa only [RichCodeRecipe.headDepth] using ih
  | resources _ _ ih => simpa only [RichCodeRecipe.headDepth] using Nat.le_trans ih (Nat.le_max_left _ _)

/-- Every focused recipe constructor supplies the real canonical key guard.
This spends the retained named charge, independently of the pending selectors
or their later semantic execution. -/
theorem RichRecipeContext.openingDecrease
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (cutoffBound : cutoff ≤ input.strata.rules.length)
    (bounded : EquationStratifiedFuel.WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (input.strata.headOrdinal registry) control))
    (constants schedule : Nat) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key input.strata.rules.length (input.owner.selected.ordinal - 1)
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)
        input.owner.selected.origin.ordered.constantCount
        (recipeRootSchedule input.owner input.node))
      (EquationControlMeasure.key input.strata.rules.length cutoff fuel constants schedule) := by
  have rootBound : EquationStratifiedFuel.WithinAbove cutoff fuel
      (EquationStratifiedFuel.headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have selected := pending.rootDepth (stratifiedHeadPolicy
      (input.strata.headOrdinal registry) control)
    have available := bounded control active
    have smaller : input.recipe.stratifiedDepth (input.strata.headOrdinal registry) control ≤ fuel control :=
      Nat.le_trans selected available
    simpa only [RichRecipeRootInput.recipe, RichCodeRecipe.stratifiedDepth,
      RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, RichCert.stratifiedDepth, EquationStratifiedFuel.headDepth]
      using smaller
  exact EquationStratifiedFuel.openingDecrease input.owner.selected.ordinal_pos
    input.owner.selected.ordinal_le cutoffBound rootBound constants schedule
    input.owner.selected.origin.ordered.constantCount (recipeRootSchedule input.owner input.node)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
