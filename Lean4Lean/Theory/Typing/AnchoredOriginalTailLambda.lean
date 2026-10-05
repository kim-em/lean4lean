import Lean4Lean.Theory.Typing.AnchoredOriginalTailPi
import Lean4Lean.Theory.Typing.AnchoredOriginalTailApplication
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaJoint

/-! Lambda transfer retains original domain captures in every finite row
and future world; both source annotations keep their own original frames. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private def OriginalTail.TailPairedFits.pushDiagonalOriginal
    {n : Nat} {input support : Profile n}
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (_hTarget : OnCtx target (env.IsType U))
    (frame : TailPairedFits env registry target context locals σ σ available)
    (domainRef : EndpointRef sourceEnv U source A (.sort level))
    (domain : CodeCert env U registry target locals σ A support footprint)
    (resources : footprint.Available available) (typed : (input : Profile n).HasType support)
    (arguments : Related env U registry target anchor anchor (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    TailPairedFits env registry target (.cons context domainRef) (Locals.push locals)
      (σ.cons anchor) (σ.cons anchor) (Valuation.push needs available) :=
  frame.pushCertificates domainRef domain domain resources resources typed typed arguments
    (arguments.symm henv) needs bounded covered

theorem Obs.graded_lambda_typeOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : TailPairedFits env registry target context locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTypeResult env U registry target locals realization available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output support) := by
  obtain ⟨raw, _, oldSupport, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons key.anchor) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have localFits := fits.pushDiagonalOriginal henv hTarget domainRef domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  obtain ⟨fullResult⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons key.anchor) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
      observation (pack.available_atomized_localNeeds outsideAvailable)
  let result := fullResult.requested henv hTarget
  obtain ⟨packed, externalFootprint, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available result.typeAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have rows := PiRows.cons guard result.certificate bodyPack coverage PiRows.nil
  have certificate := domain.piLiteral rows
  refine ⟨⟨result.support, result.typeFootprint, result.certificate,
    result.typeAvailable, result.typed, _, certificate, ?_, ?_⟩⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hd | hb
    · exact domainAvailable i need hd
    · exact externalAvailable i need (by simpa using hb)
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) result.typed


theorem LambdaTypeResult.gradedAtArgumentOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
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
  have domainChild : GradedTransfer env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  obtain ⟨localFits⟩ := fits.pushGradedOriginal henv hscoped hTarget domainRef closed domainChild domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodies := originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  obtain ⟨code⟩ := fixed.bodyCertificate.transfer_graded henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1
    fixed.bodyAvailable
  obtain ⟨forward⟩ := bodies.1 observation (pack.available_atomized_localNeeds outsideAvailable)
  have selfBodies := TailJoint.left henv hscoped originalBody
  obtain ⟨self⟩ := (selfBodies target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument)
    (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
    observation (pack.available_atomized_localNeeds outsideAvailable)
  exact ⟨code.related,
    Related.retag henv fixed.outputTyped code.related.left_diagonal (self.requestedRelated henv hTarget),
    Related.retag henv fixed.outputTyped code.related.left_diagonal (forward.requestedRelated henv hTarget)⟩


private theorem admitted_right (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩

theorem LambdaTypeResult.gradedFutureOutputsOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
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
  have fits' := fits.future henv insertion
  have substitutions' := substitutions.future henv insertion
  have domain' := domain.future henv insertion
  have guard' := guard.future henv insertion
  have observation' := observation.future henv insertion
  simp only [subst_cons_future, Profile.rename_singleton] at observation'
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
  have lx := fixed'.gradedAtArgumentOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ly := fixed'.gradedAtArgumentOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hy
  have rx := fixed'.gradedAtArgumentOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ry := fixed'.gradedAtArgumentOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hy
  obtain ⟨code, leftOutput, rightOutput, crossOutput⟩ :=
    LambdaArgumentResult.outputs henv hscoped fixed'.outputTyped lx ly rx ry
  have argumentPair := guard'.path.cast admitted.2.1
  have expanded := lambda_beta_outputs henv hFuture substitutions' domains codomain
    leftBody rightBody argumentPair leftOutput rightOutput crossOutput
  have support_eq : fixed'.resultSupport = fixed.resultSupport.rename ρ := rfl
  rw [support_eq] at expanded
  exact ⟨code, by simpa only [lift'_subst] using expanded⟩


theorem LambdaTypeResult.gradedRelatedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
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
    have result := fixed.gradedFutureOutputsOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits domain guard observation pack covered
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
    have result := fixed.gradedFutureOutputsOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits domain guard observation pack covered
      domainAvailable outsideAvailable future admitted
    simpa only [display, PiWitness.literal, Lift.refl_comp, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons, Related] using result.2
  exact Related.function henv hscoped fixed.typed code behavior

/-- The actual source certificate and semantic term result are produced
together from the original lambda children. There is no assumed producer for
a newly synthesized typing proof. -/
theorem Obs.graded_lambda_interpretOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals left (.forallE A B) support footprint) ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  obtain ⟨fixed⟩ := Obs.graded_lambda_typeOriginal henv context domainRef originalBody closed domains.hasType.1 hTarget
    substitutions.left fits.left domain guard observation pack covered domainAvailable outsideAvailable
  exact ⟨_, _, ⟨fixed.certificate⟩, fixed.available, fixed.typed,
    fixed.gradedRelatedOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain closed domains codomain leftBody rightBody
      hTarget substitutions fits domain guard observation pack covered domainAvailable outsideAvailable⟩

theorem CoveredLambda.gradedInterpretOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : CoveredLambda env U registry target locals left A body key output)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals left (.forallE A B) support footprint) ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  exact Obs.graded_lambda_interpretOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain closed
    domains codomain leftBody rightBody hTarget substitutions fits node.domain node.guard
    node.bodyObservation node.pack node.covered domainAvailable outsideAvailable


theorem LambdaTypeResult.gradedCodomainTransferOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    Nonempty (CodeTransferResult env U registry target (Locals.push locals)
      (left.cons key.anchor) (right.cons argument)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      B B fixed.resultSupport) := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons argument) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have domainChild : GradedTransfer env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  obtain ⟨localFits⟩ := fits.pushGradedOriginal henv hscoped hTarget domainRef closed domainChild domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  exact fixed.bodyCertificate.transfer_graded henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1 fixed.bodyAvailable


/-- Move only the fixed actual codomain certificate to the other realization.
The original codomain child supplies the transfer; the literal Pi certificate
is rebuilt from its returned leaves and the already available domain. -/
theorem LambdaTypeResult.gradedChangeBaseOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint newDomainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (newDomain : CodeCert env U registry target locals right A domainSupport newDomainFootprint)
    (newGuard : LambdaGuard env U registry target right A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (newDomainAvailable : newDomainFootprint.Available available) :
    ∃ changed : LambdaTypeResult env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport,
      changed.resultSupport = fixed.resultSupport := by
  obtain ⟨code⟩ := fixed.gradedCodomainTransferOriginal henv hscoped context domainRef originalDomain originalCodomain
    closed formedA hTarget substitutions fits domain guard pack covered domainAvailable guard.anchor
  obtain ⟨packed, external, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available code.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have certificate := newDomain.piLiteral
    (PiRows.cons newGuard code.certificate bodyPack coverage PiRows.nil)
  refine ⟨⟨fixed.resultSupport, code.footprint, code.certificate, code.available,
    fixed.outputTyped, _, certificate, ?_, ?_⟩, rfl⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (newDomainAvailable i need)
      (fun h => externalAvailable i need (by simpa using h))
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) fixed.outputTyped


/-- Interpret the actual raw right lambda at the left-realized assigned Pi.
Only the original domain/body/codomain clauses are invoked. -/
theorem LambdaTypeResult.gradedRawRightRelatedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {leftDomainFootprint rightDomainFootprint bodyFootprint outside : Footprint}
    (leftFixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (rightFixed : LambdaTypeResult env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (support_eq : leftFixed.resultSupport = rightFixed.resultSupport)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) other other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (leftDomain : CodeCert env U registry target locals left A domainSupport leftDomainFootprint)
    (leftGuard : LambdaGuard env U registry target left A key domainSupport)
    (rightDomain : CodeCert env U registry target locals right A domainSupport rightDomainFootprint)
    (rightGuard : LambdaGuard env U registry target right A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (right.cons key.anchor) other (.singleton output) bodyFootprint)
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
    have val := fits.future henv future
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransferOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left
      (leftDomain.future henv future) (leftGuard.future henv future) pack' covered'
      (leftAvailable.rename ρ) (Admitted.left_diagonal admitted)
    have ay : Admitted env U registry Δ (key.rename ρ) y y := by
      obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := admitted
      exact ⟨raw.trans pair, pair.hasType.2, support, typed, formed, code,
        Related.trans henv hscoped first second, Related.left_diagonal (Related.symm henv second)⟩
    obtain ⟨cy⟩ := fixed.gradedCodomainTransferOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left
      (leftDomain.future henv future) (leftGuard.future henv future) pack' covered'
      (leftAvailable.rename ρ) ay
    have result := (cx.related.symm henv fixed.outputTyped.wf_type).trans henv cy.related
    simpa only [fixed, LambdaTypeResult.future, lift'_subst,
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
    have result := rightFixed.gradedFutureOutputsOriginal henv hscoped context domainRef originalDomain originalBody
      originalCodomain closed domains codomain leftBody rightBody
      (substitutions.right henv hTarget) fits.right rightDomain rightGuard observation
      pack covered rightAvailable outsideAvailable future admitted
    let fixed := rightFixed.future henv future
    have pack' := pack.rename ρ
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
        atom ∈ (key.input.rename ρ).atoms := by
      intro atom hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (covered a ha)
    have sub := substitutions.future henv future
    have val := fits.future henv future
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransferOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.right henv targetWF) val.right
      (rightDomain.future henv future) (rightGuard.future henv future) pack' covered'
      (rightAvailable.rename ρ) (Admitted.left_diagonal admitted)
    obtain ⟨cross⟩ := fixed.gradedCodomainTransferOriginal henv hscoped context domainRef originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.symm henv targetWF) val.symm
      (rightDomain.future henv future) (rightGuard.future henv future) pack' covered'
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

theorem CoveredLambda.gradedTransferOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : CoveredLambda env U registry target locals left A body key output)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    Nonempty (GradedTransferResult env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  have originalA := TailJoint.left henv hscoped originalDomain
  have originalOther := TailJoint.right henv hscoped originalBody
  have domainChild : GradedTransfer env U registry target locals left right available A A' (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  have actualDomainChild : GradedTransfer env U registry target locals left right available A A (.sort domainLevel) := (originalA target locals left right available closed
    hTarget substitutions fits).1
  obtain ⟨annotation⟩ := node.domain.transfer_graded henv hscoped hTarget closed
    domainChild domainAvailable
  obtain ⟨actualDomain⟩ := node.domain.transfer_graded henv hscoped hTarget closed
    actualDomainChild domainAvailable
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
  obtain ⟨localFits⟩ := fits.pushGradedOriginal henv hscoped hTarget domainRef closed actualDomainChild node.domain
    domainAvailable node.guard.inputTyped arguments
    (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (node.pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  have localClosed := Valuation.push_atomized_closed closed node.bodyFootprint.localNeeds
  obtain ⟨returned⟩ := (originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons key.anchor)
    (Valuation.push (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons) available)
    localClosed hTarget paired localFits).1 node.bodyObservation
      (node.pack.available_atomized_localNeeds outsideAvailable)
  obtain ⟨normalAtom, member, ⟨outputAdapter⟩⟩ := returned.adapter.origin
    (by
      rw [raiseProfile_singleton]
      exact List.mem_map.mpr ⟨_, List.mem_singleton_self _, rfl⟩)
  obtain ⟨rawOutput, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨selected⟩ := returned.observation.atom rawMember
  have selectedAvailable := selected.atomizes.available_closed returned.resultAvailable localClosed
  obtain ⟨packed, external, pack, covered, externalAvailable⟩ :=
    Footprint.pack_available selectedAvailable
      (fun need hm => (node.pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  let highKey := raiseKey returned.rank returned.bound key
  have highPack := pack.raise returned.bound
  have highCovered := raiseProfile_subset returned.bound covered
  have highAnnotation := annotation.certificate.raise returned.bound
  have highActualDomain := actualDomain.certificate.raise returned.bound
  have highDomain := node.domain.raise returned.bound
  have highAnnotationGuard := annotationGuard.raise henv returned.bound
  have highActualGuard := actualGuard.raise henv returned.bound
  have highGuard := node.guard.raise henv returned.bound
  let rawNode : CoveredLambda env U registry target locals right A' other highKey rawOutput := {
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
  obtain ⟨rightFixed⟩ := Obs.graded_lambda_typeOriginal henv context domainRef originalOther closed domains.hasType.1
    hTarget (substitutions.right henv hTarget) fits.right highActualDomain highActualGuard
    selected.observation highPack highCovered actualDomain.available externalAvailable
  obtain ⟨leftFixed, support_eq⟩ := rightFixed.gradedChangeBaseOriginal henv hscoped context domainRef originalA originalCodomain
    closed domains.hasType.1 hTarget (substitutions.symm henv hTarget) fits.symm
    highActualDomain highActualGuard highDomain highGuard highPack highCovered
    actualDomain.available domainAvailable
  have rawRelated := leftFixed.gradedRawRightRelatedOriginal henv hscoped rightFixed support_eq context domainRef originalA
    originalOther originalCodomain closed domains codomain bodies.hasType.2 rightBody hTarget
    substitutions fits highDomain highGuard highActualDomain highActualGuard
    selected.observation highPack highCovered domainAvailable actualDomain.available externalAvailable
  obtain ⟨requestedSupport, requestedFootprint, ⟨requestedCertificate⟩, requestedAvailable,
      requestedTyped, requestedRelated⟩ := node.gradedInterpretOriginal henv hscoped context domainRef originalA originalBody
    originalCodomain closed domains codomain bodies.hasType.1 rightBody hTarget substitutions fits
    domainAvailable outsideAvailable
  have bound := Nat.succ_le_succ returned.bound
  have highRequestedCertificate := requestedCertificate.raise bound
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
  have outputStep : NormalAtomAdapter (n := returned.rank + 1) env U registry target
      (AtomData.fn highKey rawOutput) (AtomData.fn highKey (raiseAtom returned.rank returned.bound output)) :=
    .fn (.refl _) outputAdapter
  have gradeStep := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) returned.bound key output).inverse henv
  have step := NormalAtomAdapter.comp outputStep (gradeStep.toAdapter henv hscoped hTarget)
  have adapter : NormalProfileAdapter env U registry target
      (Profile.fn highKey rawOutput) (raiseProfile (returned.rank + 1) bound (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) step (.nil _)
  exact ⟨{
    rank := returned.rank + 1
    bound := bound
    rawDemand := Profile.fn highKey rawOutput
    resultFootprint := rawNode.domainFootprint ++ rawNode.outside
    observation := rawNode.observation
    adapter := adapter
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (annotation.available i need) (externalAvailable i need)
    support := _
    typeFootprint := _
    certificate := .union highRequestedCertificate leftFixed.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (requestedAvailable i need) (leftFixed.available i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRequestedRelated
    rawRelated := Related.retag henv rawTyped code rawRelated }⟩

theorem Obs.graded_lam_transferOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : TailPairedFits env registry target context locals left right available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (GradedTransferResult env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  let node : CoveredLambda env U registry target locals left A body key output :=
    ⟨domainSupport, domainFootprint, domain, guard, bodyFootprint, bodyObservation,
      outside, packed, pack, covered⟩
  exact node.gradedTransferOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
    closed domains codomain bodies rightBody hTarget substitutions fits domainAvailable outsideAvailable


private theorem lambda_observerOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A body) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    exact Obs.graded_lam_transferOriginal henv hscoped domain guard body pack covered
      context domainRef originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransfer.lamDFOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : TailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available) :
    GradedTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
  lambda_observerOriginal henv hscoped context domainRef originalDomain originalBody originalCodomain
    domains codomain bodies rightBody closed hTarget substitutions fits

/-- The two lambda annotations use their own actual formation references.
The reverse Pi conversion is constructed from the original formation
children, not supplied as a recursive call on a synthesized derivation. -/
theorem OriginalTail.DerivationFundamental.lamDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B)
    (domainIH : DerivationFundamental env registry context domain)
    (codomainIH : DerivationFundamental env registry (.cons context (.left domain)) codomain)
    (codomainIH' : DerivationFundamental env registry (.cons context (.right domain)) codomain')
    (bodyIH : DerivationFundamental env registry (.cons context (.left domain)) bodies)
    (bodyIH' : DerivationFundamental env registry (.cons context (.right domain)) bodies') :
    DerivationFundamental env registry context
      (.lamDF domainWF bodyWF domain codomain codomain' bodies bodies') := by
  intro target locals σ τ available closed hTarget substitutions fits
  have domainJoint : TailJoint env registry context A A' (.sort domainLevel) := domainIH
  have bodyJoint : TailJoint env registry (.cons context (.left domain)) body other B := bodyIH
  have otherJoint : TailJoint env registry (.cons context (.right domain)) body other B := bodyIH'
  have forward : GradedTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
    GradedTransfer.lamDFOriginal henv hscoped context (.left domain) domainJoint bodyJoint codomainIH
      (domain.forget.defeq.mono hle) (codomain.forget.defeq.mono hle)
      (bodies.forget.defeq.mono hle) (bodies'.forget.defeq.mono hle).hasType.2
      closed hTarget substitutions fits
  have backwardNatural : GradedTransfer env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A' B) :=
    GradedTransfer.lamDFOriginal henv hscoped context (.right domain) domainJoint.symm otherJoint.symm codomainIH'
      (domain.forget.defeq.mono hle).symm (codomain'.forget.defeq.mono hle)
      (bodies'.forget.defeq.mono hle).symm (bodies.forget.defeq.mono hle).hasType.1
      closed hTarget substitutions fits
  have pi := OriginalTail.DerivationFundamental.forallEDF henv hscoped hle context domainWF bodyWF
    domain codomain codomain' domainIH codomainIH codomainIH'
  have code : GradedTransfer env U registry target locals σ σ available
      (.forallE A' B) (.forallE A B) (.sort (.imax domainLevel bodyLevel)) :=
    (pi target locals σ σ available closed hTarget substitutions.left fits.left).2.1
  have backward : GradedTransfer env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A B) :=
    GradedTransfer.convertAnswer henv hscoped closed hTarget code backwardNatural
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

/-- Both binder contexts are measured with their own original annotation
endpoint, even though the lambda equality shares a raw codomain expression. -/
theorem OriginalTail.lamDF_schedule
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B) :
    let parent := schedule .fundamental (Closure.close
      (Derivation.lamDF domainWF bodyWF domain codomain codomain' bodies bodies').origin context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close codomain.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close codomain'.origin
      (ContextDerivation.cons context (.right domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close bodies.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close bodies'.origin
      (ContextDerivation.cons context (.right domain)).closures).cost < parent := by
  have leftBound : (Closure.close (lambdaOrigin domain.origin codomain.origin bodies.origin) context.closures).cost <
      (Closure.close (Derivation.lamDF domainWF bodyWF domain codomain codomain' bodies bodies').origin context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have rightBound : (Closure.close (lambdaOrigin domain.origin codomain'.origin bodies'.origin) context.closures).cost <
      (Closure.close (Derivation.lamDF domainWF bodyWF domain codomain codomain' bodies bodies').origin context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have domainBound := binder_domain_cost domain.origin [codomain.origin, bodies.origin] [] context.closures
  have leftBody := binder_body_cost (domain := domain.origin) (bodies := [codomain.origin, bodies.origin])
    (children := []) (body := bodies.origin) (by simp) context.closures
  have leftType := binder_body_cost (domain := domain.origin) (bodies := [codomain.origin, bodies.origin])
    (children := []) (body := codomain.origin) (by simp) context.closures
  have rightBody := binder_body_cost (domain := domain.origin) (bodies := [codomain'.origin, bodies'.origin])
    (children := []) (body := bodies'.origin) (by simp) context.closures
  have rightType := binder_body_cost (domain := domain.origin) (bodies := [codomain'.origin, bodies'.origin])
    (children := []) (body := codomain'.origin) (by simp) context.closures
  exact ⟨schedule_strict (Nat.lt_trans domainBound leftBound) _ _,
    schedule_strict (Nat.lt_trans leftType leftBound) _ _,
    schedule_strict (Nat.lt_trans rightType rightBound) _ _,
    schedule_strict (Nat.lt_trans leftBody leftBound) _ _,
    schedule_strict (Nat.lt_trans rightBody rightBound) _ _⟩

end Lean4Lean.AnchoredSource.Adapted
