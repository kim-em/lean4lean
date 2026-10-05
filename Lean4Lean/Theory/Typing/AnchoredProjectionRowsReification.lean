import Lean4Lean.Theory.Typing.AnchoredProjectionRows
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupply
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization

/-! Reify a declaration field template using the finite original parameter
and preceding-field observations. The declaration rows themselves account
for all template requirements, including domain-certificate dependencies. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private def GradedResult.lowerProjectionRequested
    (bound : n ≤ N)
    (result : GradedResult env U registry target locals σ available expression
      (raiseProfile N bound (input : Profile n))) :
    GradedResult env U registry target locals σ available expression input :=
  { result with
    bound := Nat.le_trans bound result.bound
    adapter := by simpa only [raiseProfile_trans] using result.adapter }

/-- Every terminal need selects an actual finite source argument observer.
The row's retained binder coverage accounts for both body and domain needs;
no additional observation premise is introduced for a transferred template. -/
theorem ProjectionRows.sourceValues
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {rowLocals callerLocals : List Nat}
    {seed σ : Subst} {rowAvailable callerAvailable : Valuation}
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    {required : Footprint}
    (rows : ProjectionRows env U registry target required
      rowLocals seed rowAvailable expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {priorValues values : List VExpr}
    (previous : NativeGradedValuation env U registry target callerLocals σ callerAvailable
      priorValues rowAvailable)
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      values (FamilyKey.uniform N keys bounded)) :
    NativeGradedValuation env U registry target callerLocals σ callerAvailable
      (priorValues ++ values) rows.terminalValuation := by
  induction rows generalizing priorValues values with
  | nil resources =>
    cases observations
    simpa only [List.append_nil, ProjectionRows.terminalValuation] using previous
  | cons row admission needs low covered inputPresent singletons tail ih =>
    cases observations with
    | @cons value request values requests observed rest =>
      obtain ⟨observed⟩ := observed
      have originalInput : GradedResult env U registry target callerLocals σ callerAvailable
          value _ := observed.lowerProjectionRequested (bounded _ List.mem_cons_self)
      have advanced := previous.push originalInput low covered
      have final := ih (fun key member => bounded key (List.mem_cons_of_mem _ member)) advanced rest
      simpa only [List.append_assoc, List.singleton_append,
        ProjectionRows.terminalValuation] using final

/-- Finite original source observations supply every requested terminal
leaf, at the caller's unchanged valuation. This includes empty input rows. -/
theorem ProjectionRows.sourceSupply
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {callerLocals : List Nat} {σ : Subst}
    {callerAvailable : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : ProjectionRows env U registry target required []
      (nativeCaptureSubst []) (fun _ => []) expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {values : List VExpr}
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      values (FamilyKey.uniform N keys bounded))
    {footprint : Footprint} (resources : footprint.Available rows.terminalValuation) :
    Nonempty (GradedSupply env U registry target callerLocals σ
      (nativeCaptureSubst values) callerAvailable footprint) := by
  have observed := rows.sourceValues N bounded NativeGradedValuation.empty observations
  simp only [List.nil_append] at observed
  exact observed.substitution.supply resources

/-- Restore the actual source field expression after declaration replay.
The replacement tuple is the original parameters and earlier projections,
with every observer supplied by the finite exact request list. -/
theorem ProjectionRows.reifyTemplate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (formed : OnCtx target (env.IsType U))
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (closed : callerAvailable.AtomClosed)
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    {required : Footprint}
    (rows : ProjectionRows env U registry target required []
      (nativeCaptureSubst []) (fun _ => []) expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {values : List VExpr}
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      values (FamilyKey.uniform N keys bounded))
    {template : VExpr} {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target rows.terminalLocals
      (nativeCaptureSubst (values.map (·.subst σ))) template support footprint)
    (scope : template.ClosedN values.length)
    (resources : footprint.Available rows.terminalValuation) :
    Nonempty (CertificateResult env U registry target callerLocals σ callerAvailable
      (template.instOuter values) support) := by
  have atCaller := certificate.realizePrefix scope ((nativeCaptureSubst values).comp σ) (by
    intro i hi
    simp only [nativeCaptureSubst, List.length_map, Subst.comp]
    rw [dif_pos hi, dif_pos hi]
    simp only [List.getElem_map])
  obtain ⟨supply⟩ := rows.sourceSupply N bounded observations resources
  obtain ⟨result⟩ := atCaller.substitute henv hscoped formed
    (nativeCaptureSubst values) σ rfl callerLocals callerAvailable closed supply
  have literal : template.subst (nativeCaptureSubst values) = template.instOuter values := by
    rw [instOuter_eq_subst]
    apply subst_congr_closedN scope
    intro i hi
    simp only [nativeCaptureSubst, Subst.ofList, dif_pos hi]
  exact ⟨literal ▸ result⟩

end Lean4Lean.AnchoredSource.Adapted
