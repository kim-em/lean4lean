import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFuture
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedPiRule

/-! The literal Pi rule uses the three fixed original formation children.
Every row extension retains the original domain endpoint in both source
contexts, including future target worlds used by row capabilities. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private def certificateFootprint {footprint : Footprint}
    (_ : CodeCert env U registry target locals σ expression demand footprint) : Footprint := footprint

/-- A finite source codomain certificate is transported at an actual admitted
argument through the original body child. Its original sort is retained too. -/
private theorem CodeCert.piBodyAtTail
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {B B' : VExpr} {key : Key n} {ambient result packed : Profile n}
    (originalDomain : TailJoint env registry context A A (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (certificate : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
      B result footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key z z) :
    Nonempty (CodeTransferResult env U registry target (Locals.push locals)
      (σ.cons key.anchor) (τ.cons z)
      (Valuation.push (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons) available)
      B B' result) ∧
      ∀ relevant, Relevant bodyLevel relevant → result.HasType (.sort relevant) := by
  have domainChild : GradedTransfer env U registry target locals σ τ available A A (.sort domainLevel) :=
    (originalDomain target locals σ τ available closed hTarget substitutions fits).1
  obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons z) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  let head := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  obtain ⟨localFits⟩ := fits.pushGradedOriginal henv hscoped hTarget domainRef closed domainChild domain domainAvailable
    guard.inputTyped arguments head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have children := originalBody target (Locals.push locals) (σ.cons key.anchor) (τ.cons z)
    (Valuation.push head available) (Valuation.push_atomized_closed closed _) hTarget paired localFits
  exact ⟨certificate.transfer_graded henv hscoped hTarget (Valuation.push_atomized_closed closed _)
      children.1 (pack.available_atomized_localNeeds resources),
    fun relevant flag => certificate.sortCorrect children.2.2.1 flag
      (pack.available_atomized_localNeeds resources)⟩

private theorem renameCoverage {p q : Profile n}
    (covered : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (ρ : Lift) :
    ∀ atom ∈ (p.rename ρ).atoms, atom ∈ (q.rename ρ).atoms := by
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map_of_mem (covered old ho)

section
variable {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  (henv : env.Ordered) (hscoped : registry.Scoped)
  {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
  {available : Valuation} {A' B B' : VExpr} {bodyLevel : VLevel}
  (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
  (originalBody : TailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
  (domains : env.IsDefEq U source A A' (.sort domainLevel))
  (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (fits : TailPairedFits env registry target context locals σ τ available)

include henv hscoped context domainRef originalDomain originalBody domains closed hTarget substitutions fits in
private theorem PiRows.transferTail
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (body : PiRows env U registry target locals σ A B ambient rows footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) :
    Nonempty (RowsResult env U registry target locals τ available A' B' ambient rows) := by
  match body with
  | .nil => exact ⟨⟨[], .nil, fun _ _ h => nomatch h⟩⟩
  | .cons guard certificate pack covered tail =>
    have actualDomain : TailJoint env registry context A A (.sort domainLevel) :=
      originalDomain.left henv hscoped
    have domainChild : GradedTransfer env U registry target locals σ τ available A A' (.sort domainLevel) :=
      (originalDomain target locals σ τ available closed hTarget substitutions fits).1
    have actualChild : GradedTransfer env U registry target locals σ τ available A A (.sort domainLevel) :=
      (actualDomain target locals σ τ available closed hTarget substitutions fits).1
    obtain ⟨domainCode⟩ := domain.transfer_graded henv hscoped hTarget closed domainChild domainAvailable
    have guard' : LambdaGuard env U registry target τ A' _ ambient := {
      inputTyped := guard.inputTyped
      formed := guard.formed
      path := guard.path.trans (.single (domains.substDF henv substitutions.wf hTarget substitutions))
      domains := guard.domains.trans henv domainCode.related
      anchor := guard.anchor }
    obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := guard.anchor
    have arguments := Related.convert henv guard.inputTyped guard.domains anchor
    have paired : Ctx.SubstEq env U target (σ.cons _) (τ.cons _) (A :: source) :=
      .cons substitutions domains.hasType.1 (guard.path.cast raw)
    let needs := certificateFootprint certificate |>.localNeeds
    let head := needs ++ needs.flatMap Need.singletons
    obtain ⟨localFits⟩ := fits.pushGradedOriginal henv hscoped hTarget domainRef closed actualChild domain domainAvailable
      guard.inputTyped arguments head
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    have child : GradedTransfer env U registry target (Locals.push locals)
        (σ.cons _) (τ.cons _) (Valuation.push head available) B B' (.sort bodyLevel) :=
      (originalBody target (Locals.push locals) _ _ _
        (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
    obtain ⟨returned⟩ := certificate.transfer_graded henv hscoped hTarget
      (Valuation.push_atomized_closed closed _) child
      (pack.available_atomized_localNeeds (fun i need hm => resources i need (List.mem_append_left _ hm)))
    obtain ⟨packed, outside, newPack, newCovered, outsideAvailable⟩ :=
      Footprint.pack_available returned.available
        (fun need hm => (pack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    obtain ⟨rest⟩ := tail.transferTail domain domainAvailable
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨⟨outside ++ rest.footprint,
      .cons guard' returned.certificate newPack newCovered rest.bodies,
      fun i need hm => (List.mem_append.mp hm).elim (outsideAvailable i need) (rest.resources i need)⟩⟩
termination_by sizeOf body

include henv hscoped context domainRef originalDomain originalBody domains closed hTarget substitutions fits in
private theorem PiRows.capabilitiesTail
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (body : PiRows env U registry target locals σ A B ambient rows footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) :
    ∀ key result, (key, result) ∈ rows →
      key.input.HasType ambient ∧ result.HasType (.sort true) ∧
      (∀ relevant, Relevant bodyLevel relevant → result.HasType (.sort relevant)) ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient ∧
      ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
        Admitted env U registry Δ (key.rename ρ) x y →
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B.subst σ.lift).lift' ρ.cons).inst y) (result.rename ρ) ∧
        TypeRelated env U registry Δ (((B'.subst τ.lift).lift' ρ.cons).inst x)
          (((B'.subst τ.lift).lift' ρ.cons).inst y) (result.rename ρ) ∧
        TypeRelated env U registry Δ (((B.subst σ.lift).lift' ρ.cons).inst x)
          (((B'.subst τ.lift).lift' ρ.cons).inst x) (result.rename ρ) := by
  intro key result member
  match body with
  | .nil => cases member
  | .cons guard certificate pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      have originalA := originalDomain.left henv hscoped
      have originalB := originalBody.left henv hscoped
      have resources' := fun i need hm => resources i need (List.mem_append_left _ hm)
      have sorted := (CodeCert.piBodyAtTail henv hscoped context domainRef originalA originalBody domains.hasType.1
        closed hTarget substitutions fits domain guard certificate pack covered domainAvailable resources' guard.anchor).2
      refine ⟨guard.inputTyped, certificate.formed, sorted, guard.path, guard.domains, ?_⟩
      intro Δ ρ future x y admitted
      have domain' := domain.future henv future
      have guard' := guard.future henv future
      have certificate' := certificate.future henv future
      simp only [subst_cons_future] at certificate'
      have pack' := pack.rename ρ
      have covered' := renameCoverage covered ρ
      have subs := substitutions.future henv future
      have fs := fits.future henv future
      have hΔ := future.targetWF henv
      have atLeft : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B.subst ((σ.lift_r ρ).cons z)) (result.rename ρ) := by
        intro z hz
        obtain ⟨⟨returned⟩, _⟩ := CodeCert.piBodyAtTail henv hscoped context domainRef originalA originalB domains.hasType.1
          (closed.rename ρ) hΔ subs.left fs.left domain' guard' certificate' pack' covered'
          (domainAvailable.rename ρ) (Footprint.Available.rename resources' ρ) hz
        exact returned.related
      have atRight : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B'.subst ((τ.lift_r ρ).cons z)) (result.rename ρ) := by
        intro z hz
        obtain ⟨⟨returned⟩, _⟩ := CodeCert.piBodyAtTail henv hscoped context domainRef originalA originalBody domains.hasType.1
          (closed.rename ρ) hΔ subs fs domain' guard' certificate' pack' covered'
          (domainAvailable.rename ρ) (Footprint.Available.rename resources' ρ) hz
        exact returned.related
      have rightAdmission : Admitted env U registry Δ (key.rename ρ) y y := by
        obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
        exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
          Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩
      have lx := atLeft x admitted.left_diagonal
      have ly := atLeft y rightAdmission
      have rx := atRight x admitted.left_diagonal
      have ry := atRight y rightAdmission
      have wf := certificate'.formed.wf_value
      have triples := And.intro ((lx.symm henv wf).trans henv ly)
        (And.intro ((rx.symm henv wf).trans henv ry) ((lx.symm henv wf).trans henv rx))
      simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using triples
    · exact tail.capabilitiesTail domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) key result member
termination_by sizeOf body

end

/-- The primitive Pi observation case, before its outer observation closures. -/
private theorem Obs.graded_pi_transferTail
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' protoA protoB : VExpr} {bodyLevel : VLevel}
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    {domainFootprint rowFootprint : Footprint}
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : PiGuard env U target σ A B protoA protoB)
    (body : PiRows env U registry target locals σ A B ambient rows rowFootprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : rowFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel))
      (Profile.pi protoA protoB ambient rows)) := by
  have domainChild : GradedTransfer env U registry target locals σ τ available A A' (.sort domainLevel) :=
    (originalDomain target locals σ τ available closed hTarget substitutions fits).1
  obtain ⟨newDomain⟩ := domain.transfer_graded henv hscoped hTarget closed domainChild domainAvailable
  obtain ⟨newRows⟩ := body.transferTail henv hscoped context domainRef originalDomain originalBody domains closed hTarget
    substitutions fits domain domainAvailable resources
  have caps := body.capabilitiesTail henv hscoped context domainRef originalDomain originalBody domains closed hTarget
    substitutions fits domain domainAvailable resources
  have hA := domains.hasType.1.subst henv substitutions.left hTarget
  have hA' := domains.hasType.2.subst henv (substitutions.right henv hTarget) hTarget
  have contextA : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨hTarget, _, hA⟩
  have contextA' : OnCtx (A'.subst τ :: target) (env.IsType U) := ⟨hTarget, _, hA'⟩
  have sourceA : OnCtx (A :: source) (env.IsType U) := ⟨substitutions.wf, _, domains.hasType.1⟩
  have rawDomains := domains.substDF henv substitutions.wf hTarget substitutions
  have rawBodies := bodies.substDF henv sourceA contextA (substitutions.lift henv domains.hasType.1)
  have rawRight := rightBody.subst henv
    ((substitutions.right henv hTarget).lift henv domains.hasType.2) contextA'
  have guard' : PiGuard env U target τ A' B' protoA protoB := {
    domainPath := (TypeConversion.single rawDomains.symm).trans guard.domainPath
    bodyPath := TypeConversion.changeDomain henv hTarget hA' hA (.single rawDomains.symm)
      ((TypeConversion.single rawBodies.symm).trans guard.bodyPath) }
  have valueCode : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A' B').subst τ) (Profile.pi protoA protoB ambient rows) := by
    apply TypeRelated.literalPiPair henv hTarget ⟨_, hA⟩ ⟨_, hA'⟩
      ⟨_, rawBodies.hasType.1⟩ ⟨_, rawRight⟩ (.single rawDomains) (.single rawBodies)
      guard.domainPath guard.bodyPath newDomain.related
    · intro key result member
      have cap := caps key result member
      exact ⟨ambient, cap.1, domain.formed, Profile.le_refl _, cap.2.2.2.1, cap.2.2.2.2.1⟩
    · intro key result member
      exact (caps key result member).2.2.2.2.2
  have wf : (Profile.pi protoA protoB ambient rows).WF := Profile.WF.pi_iff.mpr
    ⟨domain.formed, fun key result member => ⟨(caps key result member).1, (caps key result member).2.1.wf_value⟩⟩
  have sortable : (Profile.pi protoA protoB ambient rows).HasType (.sort true) :=
    Profile.HasType.pi_iff.mpr ⟨wf, fun key result member => (caps key result member).2.1⟩
  obtain ⟨relevant, flag⟩ : ∃ relevant, Relevant bodyLevel relevant := by
    by_cases h : bodyLevel ≈ .zero
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have typed : (Profile.pi protoA protoB ambient rows).HasType (.sort relevant) :=
    Profile.HasType.pi_iff.mpr ⟨wf, fun key result member => (caps key result member).2.2.1 relevant flag⟩
  have imaxFlag : Relevant (.imax domainLevel bodyLevel) relevant := by
    cases relevant <;> simpa only [Relevant, Bool.false_eq_true, if_false, if_true,
      VLevel.imax_eq_zero] using flag
  have levelWF : (VLevel.imax domainLevel bodyLevel).WF U :=
    ⟨domains.sort_r henv substitutions.wf, bodies.sort_r henv sourceA⟩
  have typeCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n + 1) henv levelWF levelWF rfl imaxFlag
  have related := Related.of_code henv sortable typed valueCode typeCode
  exact ⟨{
    rank := n + 1, bound := Nat.le_refl _, rawDemand := Profile.pi protoA protoB ambient rows,
    resultFootprint := newDomain.footprint ++ newRows.footprint,
    observation := .pi newDomain.certificate guard' newRows.bodies,
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (newDomain.available i need) (newRows.resources i need),
    support := .sort relevant, typeFootprint := [],
    certificate := .seed (.sort imaxFlag) (Profile.HasType.sort relevant),
    typeAvailable := fun _ _ hm => (nomatch hm),
    typed := by simpa only [raiseProfile_self] using typed,
    rawTyped := typed, typeCode := typeCode,
    related := by simpa only [raiseProfile_self, subst_sort] using related,
    rawRelated := (Related.symm henv related).left_diagonal }⟩


theorem Obs.piOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : TailJoint env registry context A A' (.sort domainLevel))
    (originalBody : TailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.forallE A B) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .pi domain guard body =>
    exact Obs.graded_pi_transferTail henv hscoped context domainRef originalDomain originalBody domains bodies rightBody
      closed hTarget substitutions fits domain guard body
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.piOriginal henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega


/-- The actual original Pi equality, with each body interpreted in its
own retained original domain context. -/
theorem OriginalTail.DerivationFundamental.forallEDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort u))
    (body : Derivation sourceEnv U (A :: source) B B' (.sort v))
    (body' : Derivation sourceEnv U (A' :: source) B B' (.sort v))
    (domainIH : DerivationFundamental env registry context domain)
    (bodyIH : DerivationFundamental env registry (.cons context (.left domain)) body)
    (bodyIH' : DerivationFundamental env registry (.cons context (.right domain)) body') :
    DerivationFundamental env registry context (.forallEDF hu hv domain body body') := by
  intro target locals σ τ available closed hTarget substitutions fits
  have domains := domain.forget.defeq.mono below
  have bodies := body.forget.defeq.mono below
  have bodies' := body'.forget.defeq.mono below
  have domainJoint : TailJoint env registry context A A' (.sort u) := domainIH
  have bodyJoint : TailJoint env registry (.cons context (.left domain)) B B' (.sort v) := bodyIH
  have bodyJoint' : TailJoint env registry (.cons context (.right domain)) B B' (.sort v) := bodyIH'
  have forward : GradedTransfer env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax u v)) :=
    Obs.piOriginal henv hscoped context (.left domain) domainJoint bodyJoint
      domains bodies bodies'.hasType.2 closed hTarget substitutions fits
  have backward : GradedTransfer env U registry target locals σ τ available
      (.forallE A' B') (.forallE A B) (.sort (.imax u v)) :=
    Obs.piOriginal henv hscoped context (.right domain) domainJoint.symm bodyJoint'.symm
      domains.symm bodies'.symm bodies.hasType.1 closed hTarget substitutions fits
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

end Lean4Lean.AnchoredSource.Adapted
