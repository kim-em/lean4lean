import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetLambdaData

/-! The native hereditary lambda transfer uses only the original domain, body,
and codomain clauses. Its finite returned observation and assigned Pi
certificate retain both requested and raw output support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem SortableCert.transferBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (transfer : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available left right assigned)
    (certificate : SortableCert env U registry target locals σ left relevant profile footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      left right assigned relevant profile) := by
  exact HereditaryBudgeted.Transfer.sortable henv hscoped hTarget closed transfer certificate bounded resources

private def OriginalTail.SortableTailPairedFits.pushDiagonalOriginal
    {n : Nat} {input support : Profile n}
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (_hTarget : OnCtx target (env.IsType U))
    (frame : SortableTailPairedFits env registry target context locals σ σ available)
    (domainRef : EndpointRef sourceEnv U source A (.sort level))
    (domain : SortableCert env U registry target locals σ A true support footprint)
    (resources : footprint.Available available) (typed : (input : Profile n).HasType support)
    (arguments : Related env U registry target anchor anchor (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    SortableTailPairedFits env registry target (.cons context domainRef) (Locals.push locals)
      (σ.cons anchor) (σ.cons anchor) (Valuation.push needs available) :=
  frame.pushCertificates domainRef domain domain resources resources typed typed arguments
    (arguments.symm henv) needs bounded covered

theorem SortableObs.graded_lambda_typeBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : SortableTailPairedFits env registry target context locals realization realization available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals realization A true support domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : SortableObs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (BudgetLambdaTypeResult budgets env U registry target locals realization available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output support) := by
  obtain ⟨raw, _, oldSupport, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons key.anchor) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  let localFits := fits.pushDiagonalOriginal henv hTarget domainRef domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have localBound : HereditaryBudgeted.Within budgets localFits.nativeDepth := by
    intro current fuel member
    simp only [localFits, SortableTailPairedFits.pushDiagonalOriginal,
      SortableTailPairedFits.pushCertificates, SortableTailPairedFits.nativeDepth, SortableTailFits.nativeDepth]
    have original := Nat.max_le.mp (frameBound current fuel member)
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨domainBound current fuel member, original.1⟩,
      Nat.max_le.mpr ⟨domainBound current fuel member, original.2⟩⟩
  obtain ⟨fullResult⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons key.anchor) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound).1
      observation bodyBound (pack.available_atomized_localNeeds outsideAvailable)
  let result := fullResult
  obtain ⟨packed, externalFootprint, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available result.typeAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  let rows := SortableRows.cons guard result.requestedCertificate bodyPack coverage SortableRows.nil
  let certificate := domain.piLiteral rows
  refine ⟨⟨⟨(lowerProfile n result.bound result.support), result.typeFootprint, result.requestedCertificate,
    result.typeAvailable, result.requestedTyped, _, certificate, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hd | hb
    · exact domainAvailable i need hd
    · exact externalAvailable i need (by simpa using hb)
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) result.requestedTyped
  · intro current fuel member
    simpa only [result, SortableComputationalTransferResult.requestedCertificate,
      SortableCert.nativeDepth_lower] using fullResult.certificateBound current fuel member
  · intro current fuel member
    simp only [certificate, rows, SortableCert.piLiteral, SortableCert.nativeDepth,
      SortableRows.nativeDepth, SortableComputationalTransferResult.requestedCertificate,
      SortableCert.nativeDepth_lower, Nat.max_zero]
    exact Nat.max_le.mpr ⟨domainBound current fuel member, fullResult.certificateBound current fuel member⟩


theorem BudgetLambdaTypeResult.gradedAtArgumentBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : SortableObs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    LambdaArgumentResult env U registry target (left.cons key.anchor) (right.cons argument)
      body other B output fixed.resultSupport := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons argument) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits frameBound).1
  obtain ⟨localFits, localBound⟩ := HereditaryBudgeted.pushOriginal henv hscoped hTarget domainRef closed domainChild fits frameBound domain domainBound domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodies := originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound
  obtain ⟨code⟩ := fixed.bodyCertificate.transferBudgeted henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1
    fixed.bodyBound fixed.bodyAvailable
  obtain ⟨forward⟩ := bodies.1 observation bodyBound (pack.available_atomized_localNeeds outsideAvailable)
  have selfBodies := HereditaryBudgeted.TailJointAt.left henv hscoped originalBody
  obtain ⟨self⟩ := (selfBodies target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument)
    (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound).1
    observation bodyBound (pack.available_atomized_localNeeds outsideAvailable)
  exact ⟨code.related,
    Related.retag henv fixed.outputTyped code.related.left_diagonal (self.requestedRelated henv hTarget),
    Related.retag henv fixed.outputTyped code.related.left_diagonal (forward.requestedRelated henv hTarget)⟩



private theorem admitted_right (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩

theorem BudgetLambdaTypeResult.gradedFutureOutputsBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : SortableObs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    {future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (admitted : Admitted env U registry future (key.rename ρ) x y) :
    TypeRelated env U registry future
      (B.subst ((left.lift_r ρ).cons x)) (B.subst ((left.lift_r ρ).cons y))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A body).subst left).lift' ρ) x)
      (.app (((VExpr.lam A body).subst left).lift' ρ) y)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A' other).subst right).lift' ρ) x)
      (.app (((VExpr.lam A' other).subst right).lift' ρ) y)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A body).subst left).lift' ρ) x)
      (.app (((VExpr.lam A' other).subst right).lift' ρ) x)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) := by
  let fixed' := fixed.future henv insertion
  obtain ⟨fits', fitsDepth⟩ := fits.future_allDepth henv insertion
  have fitsBound' : HereditaryBudgeted.Within budgets fits'.nativeDepth := by
    intro current fuel member
    change fits'.nativeDepth current ≤ fuel
    rw [fitsDepth]
    exact frameBound current fuel member
  have substitutions' := substitutions.future henv insertion
  let domain' := domain.future henv insertion
  have domainBound' : HereditaryBudgeted.Within budgets domain'.nativeDepth := by
    intro current fuel member
    simpa only [domain', SortableCert.nativeDepth_future] using domainBound current fuel member
  have guard' := guard.future henv insertion
  have observationPacket : ∃ observation' : SortableObs env U registry future (Locals.push locals)
      ((left.cons key.anchor).lift_r ρ) body ((Profile.singleton output).rename ρ)
      (Footprint.rename ρ bodyFootprint), HereditaryBudgeted.Within budgets observation'.nativeDepth := by
    refine ⟨observation.future henv insertion, ?_⟩
    intro current fuel member
    simpa only [SortableObs.nativeDepth_future] using bodyBound current fuel member
  rw [subst_cons_future] at observationPacket
  simp only [Profile.rename_singleton] at observationPacket
  obtain ⟨observation', bodyBound'⟩ := observationPacket
  have pack' := pack.rename ρ
  have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
      atom ∈ (key.input.rename ρ).atoms := by
    intro atom hm
    obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hm
    subst atom
    exact List.mem_map_of_mem (covered original horiginal)
  have domainAvailable' := domainAvailable.rename ρ
  have outsideAvailable' := outsideAvailable.rename ρ
  have hFuture := insertion.targetWF henv
  have hx := admitted.left_diagonal
  have hy := admitted_right henv hscoped admitted
  have lx := fixed'.gradedAtArgumentBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left (HereditaryBudgeted.frame_left fitsBound') domain' domainBound' guard' observation' bodyBound' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ly := fixed'.gradedAtArgumentBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left (HereditaryBudgeted.frame_left fitsBound') domain' domainBound' guard' observation' bodyBound' pack' covered'
    domainAvailable' outsideAvailable' hy
  have rx := fixed'.gradedAtArgumentBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' fitsBound' domain' domainBound' guard' observation' bodyBound' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ry := fixed'.gradedAtArgumentBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' fitsBound' domain' domainBound' guard' observation' bodyBound' pack' covered'
    domainAvailable' outsideAvailable' hy
  obtain ⟨code, leftOutput, rightOutput, crossOutput⟩ :=
    LambdaArgumentResult.outputs henv hscoped fixed'.outputTyped lx ly rx ry
  have argumentPair := guard'.path.cast admitted.2.1
  have expanded := lambda_beta_outputs henv hFuture substitutions' domains codomain
    leftBody rightBody argumentPair leftOutput rightOutput crossOutput
  have support_eq : fixed'.resultSupport = fixed.resultSupport.rename ρ := rfl
  rw [support_eq] at expanded
  exact ⟨code, by simpa only [lift'_subst] using expanded⟩


theorem BudgetLambdaTypeResult.gradedRelatedBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : SortableObs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Related env U registry target ((VExpr.lam A body).subst left)
      ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
      (Profile.fn key output)
      (Profile.pi (A.subst left) (B.subst left.lift) domainSupport
        [(key, fixed.resultSupport)]) := by
  have rawA := domains.hasType.1.subst henv substitutions.left hTarget
  have formedA : env.IsType U target (A.subst left) := ⟨_, rawA⟩
  have contextA : OnCtx (A.subst left :: target) (env.IsType U) := ⟨hTarget, formedA⟩
  have rawB := codomain.subst henv
    (substitutions.left.lift henv domains.hasType.1) contextA
  have formedB : env.IsType U (A.subst left :: target) (B.subst left.lift) := ⟨_, rawB⟩
  have row : ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ (((B.subst left.lift).lift' ρ.cons).inst x)
        (((B.subst left.lift).lift' ρ.cons).inst y) (fixed.resultSupport.rename ρ) := by
    intro Δ ρ future x y admitted
    have result := fixed.gradedFutureOutputsBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits frameBound domain domainBound guard observation bodyBound pack covered
      domainAvailable outsideAvailable future admitted
    simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using result.1
  let display := PiWitness.literal henv hTarget formedA formedB guard.inputTyped guard.formed
    guard.path guard.domains row
  have code := TypeRelated.literalPi henv formedA formedB guard.inputTyped guard.formed
    guard.path guard.domains row
  have behavior : FunctionBehavior env U registry (relations env U registry n) target
      ((VExpr.lam A body).subst left) ((VExpr.lam A' other).subst right)
      (.forallE (A.subst left) (B.subst left.lift)) key output
      (.pi (A.subst left) (B.subst left.lift) domainSupport [(key, fixed.resultSupport)]) := by
    refine ⟨guard.anchor, _, _, domainSupport, [(key, fixed.resultSupport)],
      fixed.resultSupport, List.mem_singleton_self _, List.mem_singleton_self _,
      fixed.outputTyped, display, ?_⟩
    intro Δ ρ future x y admitted
    simp only [display, PiWitness.literal, Lift.refl_comp] at admitted
    have result := fixed.gradedFutureOutputsBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits frameBound domain domainBound guard observation bodyBound pack covered
      domainAvailable outsideAvailable future admitted
    simpa only [display, PiWitness.literal, Lift.refl_comp, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons, Related] using result.2
  exact Related.function henv hscoped fixed.typed code behavior

/-- The actual source certificate and semantic term result are produced
together from the original lambda children. There is no assumed producer for
a newly synthesized typing proof. -/
theorem SortableObs.graded_lambda_interpretBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : SortableObs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    ∃ support footprint,
      ∃ certificate : SortableCert env U registry target locals left (.forallE A B) true support footprint,
      HereditaryBudgeted.Within budgets certificate.nativeDepth ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  obtain ⟨fixed⟩ := SortableObs.graded_lambda_typeBudgetedOriginal henv context domainRef originalBody closed domains.hasType.1 hTarget
    substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound) domain domainBound guard observation bodyBound pack covered domainAvailable outsideAvailable
  exact ⟨_, _, fixed.certificate, fixed.certificateBound, fixed.available, fixed.typed,
    fixed.gradedRelatedBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain closed domains codomain leftBody rightBody
      hTarget substitutions fits frameBound domain domainBound guard observation bodyBound pack covered domainAvailable outsideAvailable⟩

theorem SortableCoveredLambda.gradedInterpretBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : SortableCoveredLambda env U registry target locals left A body key output)
    (domainBound : HereditaryBudgeted.Within budgets node.domain.nativeDepth)
    (bodyBound : HereditaryBudgeted.Within budgets node.bodyObservation.nativeDepth)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    ∃ support footprint,
      ∃ certificate : SortableCert env U registry target locals left (.forallE A B) true support footprint,
      HereditaryBudgeted.Within budgets certificate.nativeDepth ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  exact SortableObs.graded_lambda_interpretBudgetedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain closed
    domains codomain leftBody rightBody hTarget substitutions fits frameBound node.domain domainBound node.guard
    node.bodyObservation bodyBound node.pack node.covered domainAvailable outsideAvailable



theorem BudgetLambdaTypeResult.gradedCodomainTransferBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target (Locals.push locals)
      (left.cons key.anchor) (right.cons argument)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      B B (.sort bodyLevel) true fixed.resultSupport) := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons argument) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits frameBound).1
  obtain ⟨localFits, localBound⟩ := HereditaryBudgeted.pushOriginal henv hscoped hTarget domainRef closed domainChild fits frameBound domain domainBound domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound
  exact fixed.bodyCertificate.transferBudgeted henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1 fixed.bodyBound fixed.bodyAvailable


/-- Move only the fixed actual codomain certificate to the other realization.
The original codomain child supplies the transfer; the literal Pi certificate
is rebuilt from its returned leaves and the already available domain. -/
theorem BudgetLambdaTypeResult.gradedChangeBaseBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint newDomainFootprint bodyFootprint outside : Footprint}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (newDomain : SortableCert env U registry target locals right A true domainSupport newDomainFootprint)
    (newDomainBound : HereditaryBudgeted.Within budgets newDomain.nativeDepth)
    (newGuard : LambdaGuard env U registry target right A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (newDomainAvailable : newDomainFootprint.Available available) :
    ∃ changed : BudgetLambdaTypeResult budgets env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport,
      changed.resultSupport = fixed.resultSupport := by
  obtain ⟨code⟩ := fixed.gradedCodomainTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalCodomain
    closed formedA hTarget substitutions fits frameBound domain domainBound guard pack covered domainAvailable guard.anchor
  obtain ⟨packed, external, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available code.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  let certificate := newDomain.piLiteral
    (SortableRows.cons newGuard code.certificate bodyPack coverage SortableRows.nil)
  refine ⟨⟨⟨fixed.resultSupport, code.footprint, code.certificate, code.available,
    fixed.outputTyped, _, certificate, ?_, ?_⟩, code.valueBound, ?_⟩, rfl⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (newDomainAvailable i need)
      (fun h => externalAvailable i need (by simpa using h))
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) fixed.outputTyped


  · intro current fuel member
    simp only [certificate, SortableCert.piLiteral, SortableCert.nativeDepth, SortableRows.nativeDepth, Nat.max_zero]
    exact Nat.max_le.mpr ⟨newDomainBound current fuel member, code.valueBound current fuel member⟩


theorem BudgetLambdaTypeResult.gradedRawRightRelatedBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {leftDomainFootprint rightDomainFootprint bodyFootprint outside : Footprint}
    (leftFixed : BudgetLambdaTypeResult budgets env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (rightFixed : BudgetLambdaTypeResult budgets env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (support_eq : leftFixed.resultSupport = rightFixed.resultSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) other other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (leftDomain : SortableCert env U registry target locals left A true domainSupport leftDomainFootprint)
    (leftDomainBound : HereditaryBudgeted.Within budgets leftDomain.nativeDepth)
    (leftGuard : LambdaGuard env U registry target left A key domainSupport)
    (rightDomain : SortableCert env U registry target locals right A true domainSupport rightDomainFootprint)
    (rightDomainBound : HereditaryBudgeted.Within budgets rightDomain.nativeDepth)
    (rightGuard : LambdaGuard env U registry target right A key domainSupport)
    (observation : SortableObs env U registry target (Locals.push locals)
      (right.cons key.anchor) other (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (leftAvailable : leftDomainFootprint.Available available)
    (rightAvailable : rightDomainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Related env U registry target ((VExpr.lam A' other).subst right)
      ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
      (Profile.fn key output)
      (Profile.pi (A.subst left) (B.subst left.lift) domainSupport
        [(key, leftFixed.resultSupport)]) := by
  have rawA := domains.hasType.1.subst henv substitutions.left hTarget
  have formedA : env.IsType U target (A.subst left) := ⟨_, rawA⟩
  have contextA : OnCtx (A.subst left :: target) (env.IsType U) := ⟨hTarget, formedA⟩
  have formedB : env.IsType U (A.subst left :: target) (B.subst left.lift) :=
    ⟨_, codomain.subst henv (substitutions.left.lift henv domains.hasType.1) contextA⟩
  have row : ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ (((B.subst left.lift).lift' ρ.cons).inst x)
        (((B.subst left.lift).lift' ρ.cons).inst y) (leftFixed.resultSupport.rename ρ) := by
    intro Δ ρ future x y admitted
    let fixed := leftFixed.future henv future
    have pack' := pack.rename ρ
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
        atom ∈ (key.input.rename ρ).atoms := by
      intro atom hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (covered a ha)
    have sub := substitutions.future henv future
    obtain ⟨val, valDepth⟩ := fits.future_allDepth henv future
    have valBound : HereditaryBudgeted.Within budgets val.nativeDepth := by
      intro current fuel member
      change val.nativeDepth current ≤ fuel
      rw [valDepth]
      exact frameBound current fuel member
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left (HereditaryBudgeted.frame_left valBound)
      (leftDomain.future henv future)
      (by intro current fuel member; simpa only [SortableCert.nativeDepth_future] using leftDomainBound current fuel member) (leftGuard.future henv future) pack' covered'
      (leftAvailable.rename ρ) (Admitted.left_diagonal admitted)
    have ay : Admitted env U registry Δ (key.rename ρ) y y := by
      obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := admitted
      exact ⟨raw.trans pair, pair.hasType.2, support, typed, formed, code,
        Related.trans henv hscoped first second, Related.left_diagonal (Related.symm henv second)⟩
    obtain ⟨cy⟩ := fixed.gradedCodomainTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left (HereditaryBudgeted.frame_left valBound)
      (leftDomain.future henv future)
      (by intro current fuel member; simpa only [SortableCert.nativeDepth_future] using leftDomainBound current fuel member) (leftGuard.future henv future) pack' covered'
      (leftAvailable.rename ρ) ay
    have result := (cx.related.symm henv fixed.outputTyped.wf_type).trans henv cy.related
    simpa only [fixed, BudgetLambdaTypeResult.future, SortableLambdaTypeResult.future, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons] using result
  let display := PiWitness.literal henv hTarget formedA formedB leftGuard.inputTyped
    leftGuard.formed leftGuard.path leftGuard.domains row
  have code := TypeRelated.literalPi henv formedA formedB leftGuard.inputTyped
    leftGuard.formed leftGuard.path leftGuard.domains row
  have behavior : FunctionBehavior env U registry (relations env U registry n) target
      ((VExpr.lam A' other).subst right) ((VExpr.lam A' other).subst right)
      (.forallE (A.subst left) (B.subst left.lift)) key output
      (.pi (A.subst left) (B.subst left.lift) domainSupport [(key, leftFixed.resultSupport)]) := by
    refine ⟨leftGuard.anchor, _, _, domainSupport, [(key, leftFixed.resultSupport)],
      leftFixed.resultSupport, List.mem_singleton_self _, List.mem_singleton_self _,
      leftFixed.outputTyped, display, ?_⟩
    intro Δ ρ future x y admitted
    simp only [display, PiWitness.literal, Lift.refl_comp] at admitted
    have result := rightFixed.gradedFutureOutputsBudgetedOriginal henv hscoped context domainRef originalDomain originalBody
      originalCodomain closed domains codomain leftBody rightBody
      (substitutions.right henv hTarget) fits.right (HereditaryBudgeted.frame_right frameBound) rightDomain rightDomainBound rightGuard observation bodyBound
      pack covered rightAvailable outsideAvailable future admitted
    let fixed := rightFixed.future henv future
    have pack' := pack.rename ρ
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
        atom ∈ (key.input.rename ρ).atoms := by
      intro atom hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (covered a ha)
    have sub := substitutions.future henv future
    obtain ⟨val, valDepth⟩ := fits.future_allDepth henv future
    have valBound : HereditaryBudgeted.Within budgets val.nativeDepth := by
      intro current fuel member
      change val.nativeDepth current ≤ fuel
      rw [valDepth]
      exact frameBound current fuel member
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.right henv targetWF) val.right (HereditaryBudgeted.frame_right valBound)
      (rightDomain.future henv future)
      (by intro current fuel member; simpa only [SortableCert.nativeDepth_future] using rightDomainBound current fuel member) (rightGuard.future henv future) pack' covered'
      (rightAvailable.rename ρ) (Admitted.left_diagonal admitted)
    obtain ⟨cross⟩ := fixed.gradedCodomainTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.symm henv targetWF) val.symm (by intro current fuel member; simpa only [SortableTailPairedFits.nativeDepth, SortableTailPairedFits.symm, Nat.max_comm] using valBound current fuel member)
      (rightDomain.future henv future)
      (by intro current fuel member; simpa only [SortableCert.nativeDepth_future] using rightDomainBound current fuel member) (rightGuard.future henv future) pack' covered'
      (rightAvailable.rename ρ) (Admitted.left_diagonal admitted)
    have bridge := (cx.related.symm henv fixed.outputTyped.wf_type).trans henv cross.related
    have rightOutput := Related.convert henv fixed.outputTyped bridge result.2.2.1
    have support_eq' : fixed.resultSupport = leftFixed.resultSupport.rename ρ :=
      congrArg (Profile.rename ρ) support_eq.symm
    rw [support_eq'] at rightOutput
    have converted := rightOutput
    simp only [display, PiWitness.literal, Lift.refl_comp, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons, Related] at converted ⊢
    exact ⟨converted, converted, Related.left_diagonal converted⟩
  exact Related.function henv hscoped leftFixed.typed code behavior



private theorem union_code
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem SortableCoveredLambda.gradedTransferBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : SortableCoveredLambda env U registry target locals left A body key output)
    (domainBound : HereditaryBudgeted.Within budgets node.domain.nativeDepth)
    (bodyBound : HereditaryBudgeted.Within budgets node.bodyObservation.nativeDepth)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  have originalA := HereditaryBudgeted.TailJointAt.left henv hscoped originalDomain
  have originalOther := HereditaryBudgeted.TailJointAt.right henv hscoped originalBody
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals left right available A A' (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits frameBound).1
  have actualDomainChild : HereditaryBudgeted.Transfer budgets env U registry target locals left right available A A (.sort domainLevel) := (originalA target locals left right available closed
    hTarget substitutions fits frameBound).1
  obtain ⟨annotation⟩ := node.domain.transferBudgeted henv hscoped hTarget closed
    domainChild domainBound domainAvailable
  obtain ⟨actualDomain⟩ := node.domain.transferBudgeted henv hscoped hTarget closed
    actualDomainChild domainBound domainAvailable
  have annotationGuard : LambdaGuard env U registry target right A' key node.domainSupport := {
    inputTyped := node.guard.inputTyped
    formed := node.guard.formed
    path := node.guard.path.trans (.single (domains.substDF henv substitutions.wf hTarget substitutions))
    domains := node.guard.domains.trans henv annotation.related
    anchor := node.guard.anchor }
  have actualGuard : LambdaGuard env U registry target right A key node.domainSupport := {
    inputTyped := node.guard.inputTyped
    formed := node.guard.formed
    path := node.guard.path.trans (.single (domains.hasType.1.substDF henv substitutions.wf hTarget substitutions))
    domains := node.guard.domains.trans henv actualDomain.related
    anchor := node.guard.anchor }
  obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := node.guard.anchor
  have arguments := Related.convert henv node.guard.inputTyped node.guard.domains anchor
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons key.anchor) (A :: source) :=
    .cons substitutions domains.hasType.1 (node.guard.path.cast raw)
  obtain ⟨localFits, localBound⟩ := HereditaryBudgeted.pushOriginal henv hscoped hTarget domainRef closed actualDomainChild fits frameBound node.domain domainBound
    domainAvailable node.guard.inputTyped arguments
    (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (node.pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  have localClosed := Valuation.push_atomized_closed closed node.bodyFootprint.localNeeds
  obtain ⟨returned⟩ := (originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons key.anchor)
    (Valuation.push (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons) available)
    localClosed hTarget paired localFits localBound).1 node.bodyObservation bodyBound
      (node.pack.available_atomized_localNeeds outsideAvailable)
  obtain ⟨normalAtom, member, ⟨outputAdapter⟩⟩ := returned.adapter.origin
    (by
      rw [raiseProfile_singleton]
      exact List.mem_map.mpr ⟨_, List.mem_singleton_self _, rfl⟩)
  obtain ⟨rawOutput, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨selected, selectedDepth⟩ := returned.observation.atom_allDepth rawMember
  have selectedAvailable := selected.atomizes.available_closed returned.resources localClosed
  obtain ⟨packed, external, pack, covered, externalAvailable⟩ :=
    Footprint.pack_available selectedAvailable
      (fun need hm => (node.pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  let highKey := raiseKey returned.rank returned.bound key
  have highPack := pack.raise returned.bound
  have highCovered := raiseProfile_subset returned.bound covered
  let highAnnotation := annotation.certificate.raise returned.bound
  let highActualDomain := actualDomain.certificate.raise returned.bound
  let highDomain := node.domain.raise returned.bound
  have highAnnotationGuard := annotationGuard.raise henv returned.bound
  have highActualGuard := actualGuard.raise henv returned.bound
  have highGuard := node.guard.raise henv returned.bound
  have selectedBound : HereditaryBudgeted.Within budgets selected.observation.nativeDepth :=
    fun current fuel member => Nat.le_trans (selectedDepth current) (returned.observationBound current fuel member)
  have highAnnotationBound : HereditaryBudgeted.Within budgets highAnnotation.nativeDepth := by
    intro current fuel member
    simpa only [highAnnotation, SortableCert.nativeDepth_raise] using annotation.valueBound current fuel member
  have highActualDomainBound : HereditaryBudgeted.Within budgets highActualDomain.nativeDepth := by
    intro current fuel member
    simpa only [highActualDomain, SortableCert.nativeDepth_raise] using actualDomain.valueBound current fuel member
  have highDomainBound : HereditaryBudgeted.Within budgets highDomain.nativeDepth := by
    intro current fuel member
    simpa only [highDomain, SortableCert.nativeDepth_raise] using domainBound current fuel member
  let rawNode : SortableCoveredLambda env U registry target locals right A' other highKey rawOutput := {
    domainSupport := raiseProfile returned.rank returned.bound node.domainSupport
    domainFootprint := annotation.footprint
    domain := highAnnotation
    guard := highAnnotationGuard
    bodyFootprint := selected.footprint
    bodyObservation := selected.observation
    outside := external
    packed := raiseProfile returned.rank returned.bound packed
    pack := highPack
    covered := highCovered }
  obtain ⟨rightFixed⟩ := SortableObs.graded_lambda_typeBudgetedOriginal henv context domainRef originalOther closed domains.hasType.1
    hTarget (substitutions.right henv hTarget) fits.right (HereditaryBudgeted.frame_right frameBound) highActualDomain highActualDomainBound highActualGuard
    selected.observation selectedBound highPack highCovered actualDomain.available externalAvailable
  obtain ⟨leftFixed, support_eq⟩ := rightFixed.gradedChangeBaseBudgetedOriginal henv hscoped context domainRef originalA originalCodomain
    closed domains.hasType.1 hTarget (substitutions.symm henv hTarget) fits.symm
    (by intro current fuel member; simpa only [SortableTailPairedFits.nativeDepth, SortableTailPairedFits.symm, Nat.max_comm] using frameBound current fuel member)
    highActualDomain highActualDomainBound highActualGuard highDomain highDomainBound highGuard highPack highCovered
    actualDomain.available domainAvailable
  have rawRelated := leftFixed.gradedRawRightRelatedBudgetedOriginal henv hscoped rightFixed support_eq context domainRef originalA
    originalOther originalCodomain closed domains codomain bodies.hasType.2 rightBody hTarget
    substitutions fits frameBound highDomain highDomainBound highGuard highActualDomain highActualDomainBound highActualGuard
    selected.observation selectedBound highPack highCovered domainAvailable actualDomain.available externalAvailable
  obtain ⟨requestedSupport, requestedFootprint, requestedCertificate, requestedBound, requestedAvailable,
      requestedTyped, requestedRelated⟩ := node.gradedInterpretBudgetedOriginal henv hscoped domainBound bodyBound context domainRef originalA originalBody
    originalCodomain closed domains codomain bodies.hasType.1 rightBody hTarget substitutions fits frameBound
    domainAvailable outsideAvailable
  have bound := Nat.succ_le_succ returned.bound
  let highRequestedCertificate := requestedCertificate.raise bound
  have highRequestedRelated := Related.raise henv bound requestedRelated
  have highRequestedTyped := Profile.HasType.raise bound requestedTyped
  have requestedCode := TypeRelated.raise henv bound
    (requestedRelated.typeCode henv hscoped hTarget
      (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms]))
  have rawCode := rawRelated.typeCode henv hscoped hTarget
    (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms])
  have code := union_code requestedCode rawCode
  have wf := highRequestedTyped.wf_type.union leftFixed.typed.wf_type
  have typed := highRequestedTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := leftFixed.typed.enlarge (Profile.le_union_right _ _) wf
  have outputStep : GeneralNormalAtomAdapter (n := returned.rank + 1) env U registry target
      (AtomData.fn highKey rawOutput) (AtomData.fn highKey (raiseAtom returned.rank returned.bound output)) :=
    .fn (.refl _) outputAdapter
  have gradeStep := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) returned.bound key output).inverse henv
  have step := GeneralNormalAtomAdapter.comp outputStep (gradeStep.toGeneralAdapter henv hscoped hTarget)
  have adapter : GeneralNormalProfileAdapter env U registry target
      (Profile.fn highKey rawOutput) (raiseProfile (returned.rank + 1) bound (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) step (.nil _)
  exact ⟨{
    rank := returned.rank + 1
    bound := bound
    raw := Profile.fn highKey rawOutput
    footprint := rawNode.domainFootprint ++ rawNode.outside
    observation := rawNode.observation
    adapter := adapter
    resources := fun i need hm => (List.mem_append.mp hm).elim
      (annotation.available i need) (externalAvailable i need)
    support := _
    typeFootprint := _
    typeCertificate := .union highRequestedCertificate leftFixed.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (requestedAvailable i need) (leftFixed.available i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRequestedRelated
    rawRelated := Related.retag henv rawTyped code rawRelated
    live := rawRelated.live henv hscoped hTarget
    observationBound := by
      intro current fuel member
      simp only [SortableCoveredLambda.observation, SortableObs.nativeDepth]
      change max (highAnnotation.nativeDepth current) (selected.observation.nativeDepth current) ≤ fuel
      exact Nat.max_le.mpr ⟨highAnnotationBound current fuel member, selectedBound current fuel member⟩
    certificateBound := by
      intro current fuel member
      simp only [SortableCert.nativeDepth, highRequestedCertificate, SortableCert.nativeDepth_raise]
      exact Nat.max_le.mpr ⟨requestedBound current fuel member, leftFixed.certificateBound current fuel member⟩ }⟩

theorem SortableObs.graded_lam_transferBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : SortableCert env U registry target locals left A true domainSupport domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (bodyObservation : SortableObs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : HereditaryBudgeted.Within budgets bodyObservation.nativeDepth)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : SortableTailPairedFits env registry target context locals left right available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  let node : SortableCoveredLambda env U registry target locals left A body key output :=
    ⟨domainSupport, domainFootprint, domain, guard, bodyFootprint, bodyObservation,
      outside, packed, pack, covered⟩
  exact node.gradedTransferBudgetedOriginal henv hscoped domainBound bodyBound context domainRef originalDomain originalBody originalCodomain
    closed domains codomain bodies rightBody hTarget substitutions fits frameBound domainAvailable outsideAvailable



end Lean4Lean.AnchoredSource.Adapted
