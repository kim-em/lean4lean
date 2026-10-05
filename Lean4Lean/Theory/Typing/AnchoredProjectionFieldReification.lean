import Lean4Lean.Theory.Typing.AnchoredProjectionFieldFactor
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupply
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization

/-! Reify a declaration field template using the finite original parameter
and preceding-field observations. The declaration rows themselves account
for all template requirements, including domain-certificate dependencies. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private def GradedResult.lowerRequested
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
theorem FamilySeededCodeRows.sourceValues
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target source : List VExpr} {rowLocals callerLocals : List Nat}
    {seed σ : Subst} {rowAvailable callerAvailable : Valuation}
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source rowLocals seed rowAvailable expression domains keys)
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
    simpa only [List.append_nil, FamilySeededCodeRows.terminalValuation] using previous
  | @cons source A level locals seed available B n key result domains keys
      original row support admission extra low covered inputPresent tail ih =>
    cases observations with
    | @cons value request values requests observed rest =>
      obtain ⟨observed⟩ := observed
      have originalInput : GradedResult env U registry target callerLocals σ callerAvailable
          value key.input := observed.lowerRequested (bounded _ List.mem_cons_self)
      have coverage := row.seedCoverage extra low covered
      have advanced := previous.push originalInput
        (fun need member => (coverage need member).1)
        (fun need member => (coverage need member).2)
      have final := ih (fun key member => bounded key (List.mem_cons_of_mem _ member)) advanced rest
      simpa only [List.append_assoc, List.singleton_append,
        FamilySeededCodeRows.terminalValuation] using final

/-- Finite original source observations supply every requested terminal
leaf, at the caller's unchanged valuation. This includes empty input rows. -/
theorem FamilySeededCodeRows.sourceSupply
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {callerLocals : List Nat} {σ : Subst}
    {callerAvailable : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
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
theorem CodeCert.reifyFamilyTemplate
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (formed : OnCtx target (env.IsType U))
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (closed : callerAvailable.AtomClosed)
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
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

/-- The reified expression is the literal field selected by the original
projection rule, not another field type inferred from raw equality. -/
theorem CodeCert.reifyProjectionType
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (formed : OnCtx target (env.IsType U))
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (callerClosed : callerAvailable.AtomClosed)
    {expression : VExpr} {rowDomains : List VExpr} {keys : List FamilyKey}
    {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) expression rowDomains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {info : VProjectionInfo} {name : Name} {domains : List VExpr} {result : VExpr}
    (shape : info.ctorType = wrapForalls domains result)
    (closed : info.ctorType.Closed)
    {levels : List VLevel} {parameters : List VExpr} {index : Nat} {major fieldType : VExpr}
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (fieldBound : info.nparams + index < domains.length)
    (selected : info.fieldType name levels parameters index major = some fieldType)
    (observations : List.Forall₂ (fun value request => Nonempty
      (GradedResult env U registry target callerLocals σ callerAvailable value request.input))
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major))
      (FamilyKey.uniform N keys bounded))
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target rows.terminalLocals
      (nativeCaptureSubst ((parameters ++ (List.range index).map
        (fun field => VExpr.proj name field major)).map (·.subst σ)))
      (domains[info.nparams + index].instL levels) support footprint)
    (resources : footprint.Available rows.terminalValuation) :
    Nonempty (CertificateResult env U registry target callerLocals σ callerAvailable
      fieldType support) := by
  let signature : ConstantTelescope info.ctorType := ⟨domains, result, shape⟩
  have scope := signature.domain_scope closed (List.getElem?_eq_getElem fieldBound)
  have instantiated : (domains[info.nparams + index].instL levels).ClosedN
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)).length := by
    simpa only [List.length_append, List.length_map, List.length_range, parameterCount] using scope.instL
  have literal := info.fieldType_eq_instOuter shape levelCount parameterCount fieldBound
    (typeName := name) (major := major)
  have equal := Option.some.inj (selected.symm.trans literal)
  rw [equal]
  exact certificate.reifyFamilyTemplate henv hscoped formed callerClosed rows N bounded
    observations instantiated resources

end Lean4Lean.AnchoredSource.Adapted
