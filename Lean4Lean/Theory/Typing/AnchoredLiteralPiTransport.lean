import Lean4Lean.Theory.Typing.AnchoredLiteralFunctionDisplay
import Lean4Lean.Theory.Typing.AnchoredExposureTransport

/-! Concrete proof-frame transport of a literal self Pi display. Both legs
remain actual proof insertions, so replaying a finite application path needs
only proof-versus-future pushouts. -/
namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

private theorem proofSkip_inv
    (H : ProofInsertion env U Γ (P :: Δ) ρ.skip) :
    ∃ q, ProofInsertion env U Γ Δ ρ ∧
      env.HasType U Δ P (.sort .zero) ∧ env.HasType U Δ q P := by
  cases H with
  | skip previous hP hq => exact ⟨_, previous, hP, hq⟩

theorem ProofInsertion.renameFrontProof
    (added : List VExpr)
    (H : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length))
    (K : ProofInsertion env U Γ Δ ρ) (henv : env.Ordered) :
    ProofInsertion env U Δ (renameAdded ρ added ++ Δ) (.skipN .refl added.length) ∧
    ProofInsertion env U (added ++ Γ) (renameAdded ρ added ++ Δ)
      (ρ.consN added.length) := by
  induction added with
  | nil => exact ⟨.refl (K.targetWF henv), K⟩
  | cons P rest ih =>
    change ProofInsertion env U Γ (P :: (rest ++ Γ))
      (.skip (.skipN .refl rest.length)) at H
    obtain ⟨q, previous, hP, hq⟩ := proofSkip_inv H
    obtain ⟨hi, hj⟩ := ih previous
    exact ⟨hi.skip (hP.weak' henv hj.weakening) (hq.weak' henv hj.weakening), hj.cons hP⟩

end Lean4Lean.VEnv
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem Exposure.proofFutureLiteral
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {expression head : VExpr} {map τ : Lift}
    (E : Exposure env U registry Γ expression Ω map head)
    (literal : E.postContext = Ω)
    (K : ProofInsertion env U Γ Δ τ)
    (henv : env.Ordered) (hscoped : registry.Scoped) :
    ∃ Ω' map' j, ProofInsertion env U Ω Ω' j ∧ map.comp j = τ.comp map' ∧
      ∃ shifted : Exposure env U registry Δ (expression.lift' τ) Ω' map' (head.lift' j),
        shifted.postContext = Ω' := by
  obtain ⟨hg, hk⟩ := E.generated.renameFrontProof E.added K henv
  have post : ProofInsertion env U (E.added ++ Γ) Ω E.postMap := by
    simpa only [literal] using E.post
  obtain ⟨Ω', i, j, hi, hj, he⟩ := post.pushoutProof hk henv
  let map' := (Lift.skipN .refl E.added.length).comp i
  have hmap : map.comp j = τ.comp map' := by
    rw [← E.map_eq, Lift.comp_assoc, he, ← Lift.comp_assoc,
      Lift.skipN_comp_consN, Lift.refl_comp]
    dsimp only [map']
    rw [← Lift.comp_assoc, Lift.comp_skipN]
    rfl
  refine ⟨Ω', map', j, hj, hmap, {
    added := renameAdded τ E.added
    result := E.result.lift' (τ.consN E.added.length)
    postMap := i
    trace := E.trace.rename hscoped τ
    generated := ?_
    postContext := Ω'
    post := hi
    terminal := .refl
    map_eq := ?_
    result_eq := ?_
    sound := ?_
    headType := ?_ }, rfl⟩
  · simpa only [renameAdded_length] using hg
  · simp only [renameAdded_length]
    rfl
  · rw [← lift'_comp, ← he, lift'_comp, E.result_eq]
  · simpa only [← lift'_comp, hmap] using E.sound.weak' henv hj.weakening
  · obtain ⟨u, hs⟩ := E.headType
    exact ⟨u, by simpa only [lift'] using hs.weak' henv hj.weakening⟩

/-- Transport the private components literally; all three displayed
codomain capabilities come from the original left self row. -/
theorem PiWitness.proofFutureLiteral
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    {Γ Δ : List VExpr} {ρ : Lift} {type A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (display : PiWitness env U registry (relations env U registry n)
      Γ type type A B domain rows)
    (literal : display.leftExposure.postContext = display.context)
    (future : ProofInsertion env U Γ Δ ρ) :
    ∃ shifted : PiWitness env U registry (relations env U registry n)
      Δ (type.lift' ρ) (type.lift' ρ) (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) (Rows.rename ρ rows),
      ∃ j, ProofInsertion env U display.context shifted.context j ∧
        display.map.comp j = ρ.comp shifted.map ∧
        shifted.leftBody = display.leftBody.lift' j.cons ∧
        shifted.leftExposure.postContext = shifted.context := by
  obtain ⟨Ω, μ, j, extension, hmap, exposure, literal'⟩ :=
    display.leftExposure.proofFutureLiteral literal future henv hscoped
  have hbodyMap : display.map.cons.comp j.cons = ρ.cons.comp μ.cons := congrArg Lift.cons hmap
  have hlater (τ : Lift) : display.map.comp (j.comp τ) = ρ.comp (μ.comp τ) := by
    rw [← Lift.comp_assoc, hmap, Lift.comp_assoc]
  let shifted : PiWitness env U registry (relations env U registry n)
      Δ (type.lift' ρ) (type.lift' ρ) (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) (Rows.rename ρ rows) := {
    context := Ω
    map := μ
    leftDomain := display.leftDomain.lift' j
    leftBody := display.leftBody.lift' j.cons
    rightDomain := display.leftDomain.lift' j
    rightBody := display.leftBody.lift' j.cons
    leftExposure := exposure
    rightExposure := exposure
    leftDomainType := display.leftDomainType.weak' henv extension.weakening
    rightDomainType := display.leftDomainType.weak' henv extension.weakening
    leftBodyType := display.leftBodyType.weak' henv extension.weakening.cons
    rightBodyType := display.leftBodyType.weak' henv extension.weakening.cons
    domains := .refl
    bodies := .refl
    prototypeDomainPath := by
      have hp := display.prototypeDomainPath.weak' henv extension.weakening
      rw [← lift'_comp, hmap, lift'_comp] at hp
      exact hp
    prototypeBodyPath := by
      have hp := display.prototypeBodyPath.weak' henv extension.weakening.cons
      rw [← lift'_comp, hbodyMap, lift'_comp] at hp
      exact hp
    domainRelated := by
      simpa only [TypeRelated, ← Profile.rename_comp, hmap] using
        TypeRelated.future henv extension.toFuture (TypeRelated.left_diagonal display.domainRelated)
    rowDomains := by
      intro newKey newOutput hmem
      obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      obtain ⟨support, hi, hs, hle, hp, hc⟩ := display.rowDomains oldKey oldOutput hsource
      refine ⟨support.rename j, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [Key.rename, ← Profile.rename_comp, hmap] using
          (Profile.rename_hasType_iff (ρ := j)).mpr hi
      · simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := j)).mpr hs
      · change Profile.LE _ _
        simpa only [← Profile.rename_comp, hmap] using (Profile.rename_le_iff (ρ := j)).mpr hle
      · simpa only [Key.rename, ← lift'_comp, hmap] using hp.weak' henv extension.weakening
      · simpa only [TypeRelated, Key.rename, ← lift'_comp, hmap] using
          TypeRelated.future henv extension.toFuture hc
    rowBodies := by
      intro newKey newOutput hmem Ξ τ later x y admitted
      obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
      cases heq
      have harg : Admitted env U registry Ξ (oldKey.rename (display.map.comp (j.comp τ))) x y := by
        simpa only [Admitted, ← Key.rename_comp, hlater] using admitted
      have h := (display.rowBodies oldKey oldOutput hsource Ξ (j.comp τ)
        (extension.toFuture.comp later henv) x y harg).1
      have hd := TypeRelated.left_diagonal h
      simpa only [TypeRelated, ← lift'_comp, show j.cons.comp τ.cons = (j.comp τ).cons from rfl,
        ← Profile.rename_comp, hlater] using And.intro h (And.intro h hd) }
  exact ⟨shifted, j, extension, hmap, rfl, literal'⟩

end Lean4Lean.AnchoredSemantics
