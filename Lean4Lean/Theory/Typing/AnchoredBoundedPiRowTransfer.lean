import Lean4Lean.Theory.Typing.AnchoredBoundedPiCode
import Lean4Lean.Theory.Typing.AnchoredBoundedProofIrrel
/-! Exact finite Pi row transfer, using the original domain and codomain
children. Code demands keep their grade and keys under paired substitutions. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private def certificateFootprint {footprint : Footprint}
    (_ : CodeCert env U registry target locals σ expression demand footprint) : Footprint := footprint

/-- A finite source codomain certificate is transported at an actual admitted
argument through the original body child. Its original sort is retained too. -/
theorem CodeCert.piBodyAtBounded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B B' : VExpr} {key : Key n} {ambient result packed : Profile n}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (certificate : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
      B result footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key z z) :
    Nonempty (CodeResult current fuel env U registry target (Locals.push locals)
      (σ.cons key.anchor) (τ.cons z)
      (Valuation.push (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons) available)
      B B' result) ∧
      ∀ relevant, Relevant bodyLevel relevant → result.HasType (.sort relevant) := by
  have domainChild : Transfer current fuel env U registry target locals σ τ available A A (.sort domainLevel) :=
    (originalDomain target locals σ τ available closed hTarget substitutions fits).1
  obtain ⟨raw, _, _, _, _, _, anchor, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons z) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  let head := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  have localFits := fits.pushGraded henv hscoped hTarget closed domainChild domain domainBound domainAvailable
    guard.inputTyped arguments head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have children := originalBody target (Locals.push locals) (σ.cons key.anchor) (τ.cons z)
    (Valuation.push head available) (Valuation.push_atomized_closed closed _) hTarget paired localFits
  exact ⟨Transfer.codeCertificate henv hscoped hTarget (Valuation.push_atomized_closed closed _)
      children.1 certificate certificateBound (pack.available_atomized_localNeeds resources),
    fun relevant flag => CodeCert.sortCorrect children.2.2.1 flag certificate certificateBound
      (pack.available_atomized_localNeeds resources)⟩

private theorem renameCoverage {p q : Profile n}
    (covered : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (ρ : Lift) :
    ∀ atom ∈ (p.rename ρ).atoms, atom ∈ (q.rename ρ).atoms := by
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map_of_mem (covered old ho)

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  (henv : env.Ordered) (hscoped : registry.Scoped)
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation} {A A' B B' : VExpr} {domainLevel bodyLevel : VLevel}
  (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
  (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
  (domains : env.IsDefEq U source A A' (.sort domainLevel))
  (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (fits : PairedFits current fuel env U registry source target locals σ τ available)

include henv hscoped originalDomain originalBody domains closed hTarget substitutions fits in
theorem PiRows.transferBounded
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (body : PiRows env U registry target locals σ A B ambient rows footprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Substitution.RowsResult current fuel env U registry target locals τ available A' B' ambient rows) := by
  match body with
  | .nil => exact ⟨⟨[], .nil, (fun _ _ h => nomatch h), by simp only [PiRows.nativeDepth]; omega⟩⟩
  | .cons guard certificate pack covered tail =>
    have bounds := Nat.max_le.mp (show max (certificate.nativeDepth current) (tail.nativeDepth current) ≤ fuel by simpa only [PiRows.nativeDepth] using bodyBound)
    have actualDomain : Joint current fuel env U registry source A A (.sort domainLevel) :=
      originalDomain.left henv hscoped
    have domainChild : Transfer current fuel env U registry target locals σ τ available A A' (.sort domainLevel) :=
      (originalDomain target locals σ τ available closed hTarget substitutions fits).1
    have actualChild : Transfer current fuel env U registry target locals σ τ available A A (.sort domainLevel) :=
      (actualDomain target locals σ τ available closed hTarget substitutions fits).1
    obtain ⟨domainCode⟩ := domainChild.codeCertificate henv hscoped hTarget closed domain domainBound domainAvailable
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
    have localFits := fits.pushGraded henv hscoped hTarget closed actualChild domain domainBound domainAvailable
      guard.inputTyped arguments head
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    have child : Transfer current fuel env U registry target (Locals.push locals)
        (σ.cons _) (τ.cons _) (Valuation.push head available) B B' (.sort bodyLevel) :=
      (originalBody target (Locals.push locals) _ _ _
        (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
    obtain ⟨returned⟩ := child.codeCertificate henv hscoped hTarget
      (Valuation.push_atomized_closed closed _) certificate bounds.1
      (pack.available_atomized_localNeeds (fun i need hm => resources i need (List.mem_append_left _ hm)))
    obtain ⟨packed, outside, newPack, newCovered, outsideAvailable⟩ :=
      Footprint.pack_available returned.available
        (fun need hm => (pack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    obtain ⟨rest⟩ := PiRows.transferBounded domain tail domainBound domainAvailable bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨⟨outside ++ rest.footprint,
      .cons guard' returned.certificate newPack newCovered rest.bodies,
      fun i need hm => (List.mem_append.mp hm).elim (outsideAvailable i need) (rest.resources i need), by
        simpa only [PiRows.nativeDepth] using Nat.max_le.mpr ⟨returned.certificateBound, rest.bodiesBound⟩⟩⟩
termination_by sizeOf body

include henv hscoped originalDomain originalBody domains closed hTarget substitutions fits in
theorem PiRows.capabilitiesBounded
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (body : PiRows env U registry target locals σ A B ambient rows footprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (bodyBound : body.nativeDepth current ≤ fuel)
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
    have bounds := Nat.max_le.mp (show max (certificate.nativeDepth current) (tail.nativeDepth current) ≤ fuel by simpa only [PiRows.nativeDepth] using bodyBound)
    rcases List.mem_cons.mp member with same | member
    · cases same
      have originalA := originalDomain.left henv hscoped
      have originalB := originalBody.left henv hscoped
      have resources' := fun i need hm => resources i need (List.mem_append_left _ hm)
      have sorted := (CodeCert.piBodyAtBounded henv hscoped originalA originalBody domains.hasType.1
        closed hTarget substitutions fits domain guard certificate pack covered domainBound domainAvailable bounds.1 resources' guard.anchor).2
      refine ⟨guard.inputTyped, certificate.formed, sorted, guard.path, guard.domains, ?_⟩
      intro Δ ρ future x y admitted
      let domain' := domain.future henv future
      have guard' := guard.future henv future
      have certificatePair : ∃ c : CodeCert env U registry Δ (Locals.push locals)
          ((σ.cons key.anchor).lift_r ρ) B (result.rename ρ) (Footprint.rename ρ (certificateFootprint certificate)),
          c.nativeDepth current ≤ fuel :=
        ⟨certificate.future henv future, by simpa only [CodeCert.nativeDepth_future] using bounds.1⟩
      rw [subst_cons_future] at certificatePair
      obtain ⟨certificate', certificateBound'⟩ := certificatePair
      have pack' := pack.rename ρ
      have covered' := renameCoverage covered ρ
      have subs := substitutions.future henv future
      have fs := fits.future henv future
      have hΔ := future.targetWF henv
      have atLeft : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B.subst ((σ.lift_r ρ).cons z)) (result.rename ρ) := by
        intro z hz
        obtain ⟨⟨returned⟩, _⟩ := CodeCert.piBodyAtBounded henv hscoped originalA originalB domains.hasType.1
          (closed.rename ρ) hΔ subs.left fs.left domain' guard' certificate' pack' covered'
          (by simpa only [domain', CodeCert.nativeDepth_future] using domainBound)
          (domainAvailable.rename ρ) certificateBound' (Footprint.Available.rename resources' ρ) hz
        exact returned.related
      have atRight : ∀ z, Admitted env U registry Δ (key.rename ρ) z z →
          TypeRelated env U registry Δ (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
            (B'.subst ((τ.lift_r ρ).cons z)) (result.rename ρ) := by
        intro z hz
        obtain ⟨⟨returned⟩, _⟩ := CodeCert.piBodyAtBounded henv hscoped originalA originalBody domains.hasType.1
          (closed.rename ρ) hΔ subs fs domain' guard' certificate' pack' covered'
          (by simpa only [domain', CodeCert.nativeDepth_future] using domainBound)
          (domainAvailable.rename ρ) certificateBound' (Footprint.Available.rename resources' ρ) hz
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
    · exact PiRows.capabilitiesBounded domain tail domainBound domainAvailable bounds.2
        (fun i need hm => resources i need (List.mem_append_right _ hm)) key result member
termination_by sizeOf body

end
end Lean4Lean.AnchoredSource.Adapted.Staged
