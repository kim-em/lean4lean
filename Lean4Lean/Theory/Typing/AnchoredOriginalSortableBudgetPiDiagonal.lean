import Lean4Lean.Theory.Typing.AnchoredSortableBudgetComposition
import Lean4Lean.Theory.Typing.AnchoredSortableTailDepthFuture

/-! A diagonal Pi code from its two fixed original formation children.
The body is queried only at retained rows and actual admitted arguments. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem renameCoverage {p q : Profile n}
    (covered : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (ρ : Lift) :
    ∀ atom ∈ (p.rename ρ).atoms, atom ∈ (q.rename ρ).atoms := by
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map_of_mem (covered old ho)

private theorem SortableCert.piBodyBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {key : Key n} {ambient result packed : Profile n}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (bodyRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (certificate : SortableCert env U registry target (Locals.push locals) (σ.cons key.anchor)
      B relevant result footprint)
    (bodyBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key z z) :
    TypeRelated env U registry target (B.subst (σ.cons key.anchor))
      (B.subst (σ.cons z)) result := by
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available A A (.sort domainLevel) :=
    domainIH target locals σ σ available closed hTarget substitutions fits frameBound
  obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons z) (A :: source) :=
    .cons substitutions (domainRef.sound.defeq.mono hle) (guard.path.cast raw)
  let head := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  obtain ⟨domainAnswer⟩ := domainChild.sortable henv hscoped hTarget closed
    domain domainBound domainAvailable
  let localFits := fits.pushCertificates domainRef domain domainAnswer.certificate domainAvailable
    domainAnswer.available guard.inputTyped guard.inputTyped arguments
    (Related.convert henv guard.inputTyped domainAnswer.related (arguments.symm henv)) head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have localBound : HereditaryBudgeted.Within budgets localFits.nativeDepth := by
    intro current fuel member
    simp only [localFits, SortableTailPairedFits.nativeDepth, SortableTailPairedFits.pushCertificates,
      SortableTailFits.nativeDepth]
    have original := Nat.max_le.mp (frameBound current fuel member)
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨domainBound current fuel member, original.1⟩,
      Nat.max_le.mpr ⟨domainAnswer.valueBound current fuel member, original.2⟩⟩
  have bodyChild : HereditaryBudgeted.Transfer budgets env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons z) (Valuation.push head available) B B (.sort bodyLevel) := bodyIH target (Locals.push locals) (σ.cons key.anchor) (σ.cons z)
    (Valuation.push head available) (Valuation.push_atomized_closed closed _) hTarget paired localFits localBound
  obtain ⟨answer⟩ := bodyChild.sortable henv hscoped hTarget (Valuation.push_atomized_closed closed _)
    certificate bodyBound (pack.available_atomized_localNeeds resources)
  exact answer.related

private theorem SortableRows.piCapabilitiesBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {ambient : Profile n} {rows : List (Key n × Profile n)}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (bodyRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (body : SortableRows env U registry target locals σ A B relevant ambient rows footprint)
    (bodyBound : HereditaryBudgeted.Within budgets body.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) :
    ∀ key result, (key, result) ∈ rows →
      key.input.HasType ambient ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient ∧
      ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
        Admitted env U registry Δ (key.rename ρ) x y →
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B.subst σ.lift).lift' ρ.cons).inst y) (result.rename ρ) := by
  intro key result member
  match body with
  | .nil => cases member
  | .cons guard certificate pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      have resources' := fun i need hm => resources i need (List.mem_append_left _ hm)
      refine ⟨guard.inputTyped, guard.path, guard.domains, ?_⟩
      intro Δ ρ future x y admitted
      obtain ⟨shiftedFrame, shiftedDepth⟩ := fits.future_allDepth henv future
      have shiftedBound : HereditaryBudgeted.Within budgets shiftedFrame.nativeDepth := by
        intro current fuel member
        change shiftedFrame.nativeDepth current ≤ fuel
        rw [shiftedDepth]
        exact frameBound current fuel member
      let domain' := domain.future henv future
      have shiftedDomainBound : HereditaryBudgeted.Within budgets domain'.nativeDepth := by
        intro current fuel member
        simpa only [domain', SortableCert.nativeDepth_future] using domainBound current fuel member
      have guard' := guard.future henv future
      let certificate' : SortableCert env U registry Δ (Locals.push locals)
          ((σ.lift_r ρ).cons (key.anchor.lift' ρ)) B relevant (result.rename ρ)
          (Footprint.rename ρ _) := by
        simpa only [subst_cons_future] using certificate.future henv future
      have shiftedCertificateBound : HereditaryBudgeted.Within budgets certificate'.nativeDepth := by
        intro current fuel member
        have h : certificate.nativeDepth current ≤ fuel := by
          have hb := bodyBound current fuel member
          simp only [SortableRows.nativeDepth] at hb
          exact (Nat.max_le.mp hb).1
        simpa only [certificate', SortableCert.nativeDepth_mp, subst_cons_future,
          SortableCert.nativeDepth_future] using h
      have pack' := pack.rename ρ
      have covered' := renameCoverage covered ρ
      have atArgument : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B.subst ((σ.lift_r ρ).cons z)) (result.rename ρ) := by
        intro z hz
        exact SortableCert.piBodyBudgetedOriginal henv hscoped hle context domainRef bodyRef domainIH bodyIH
          (closed.rename ρ) (future.targetWF henv) (substitutions.future henv future)
          shiftedFrame shiftedBound domain' shiftedDomainBound guard' certificate' shiftedCertificateBound pack' covered'
          (domainAvailable.rename ρ) (Footprint.Available.rename resources' ρ) hz
      have rightAdmission : Admitted env U registry Δ (key.rename ρ) y y := by
        obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
        exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
          Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩
      have left := atArgument x admitted.left_diagonal
      have right := atArgument y rightAdmission
      simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using
        (left.symm henv certificate'.formed.wf_value).trans henv right
    · exact tail.piCapabilitiesBudgetedOriginal henv hscoped hle context domainRef bodyRef domainIH bodyIH
        closed hTarget substitutions fits frameBound domain domainBound
        (by
          intro current fuel member
          have hb := bodyBound current fuel member
          simp only [SortableRows.nativeDepth] at hb
          exact (Nat.max_le.mp hb).2) domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) key result member
termination_by sizeOf body

theorem SortableCert.piDiagonalBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B protoA protoB : VExpr} {ambient : Profile n} {rows : List (Key n × Profile n)}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (bodyRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (guard : PiGuard env U target σ A B protoA protoB)
    (body : SortableRows env U registry target locals σ A B relevant ambient rows footprint)
    (bodyBound : HereditaryBudgeted.Within budgets body.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) :
    TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) (Profile.pi protoA protoB ambient rows) := by
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available A A (.sort domainLevel) :=
    domainIH target locals σ σ available closed hTarget substitutions fits frameBound
  obtain ⟨domainCode⟩ := domainChild.sortable henv hscoped hTarget closed domain domainBound domainAvailable
  have caps := body.piCapabilitiesBudgetedOriginal henv hscoped hle context domainRef bodyRef domainIH bodyIH
    closed hTarget substitutions fits frameBound domain domainBound bodyBound domainAvailable resources
  have formedA := domainRef.sound.defeq.mono hle
  have formedB := bodyRef.sound.defeq.mono hle
  have hA := formedA.subst henv substitutions hTarget
  have hB := formedB.subst henv (substitutions.lift henv formedA) ⟨hTarget, _, hA⟩
  apply TypeRelated.literalPiPair henv hTarget ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
    .refl .refl guard.domainPath guard.bodyPath domainCode.related
  · intro key result member
    have cap := caps key result member
    exact ⟨ambient, cap.1, domain.formed, Profile.le_refl _, cap.2.1, cap.2.2.1⟩
  · intro key result member Δ ρ future x y admitted
    have cap := (caps key result member).2.2.2 Δ ρ future
    exact ⟨cap x y admitted, cap x y admitted, cap x x admitted.left_diagonal⟩

end Lean4Lean.AnchoredSource.Adapted
