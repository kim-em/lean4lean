import Lean4Lean.Theory.Typing.AnchoredSourceObservation
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction

/-! Source type-support provenance keeps its actual computational leaves.
Code transformations retain those leaves and their footprints; they do not
claim a newly normalized computational observation of a source variable.
The interpretation below is an internal original-child induction device.
Its seed premise ranges only over actual leaves of the given certificate.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem CodeCert.formed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression profile footprint) :
    profile.HasType (.sort true) := by
  match cert with
  | .seed observation formed => exact formed
  | .union left right => exact left.formed.union right.formed
  | .pad source => exact source.formed.pad_sort
  | .unpad source => simpa only [Profile.down_sort] using source.formed.pad_inv
  | .down source => simpa only [Profile.down_sort] using source.formed.down
  | .map view source => exact view.mapType_sort source.formed
  | .select source member => exact source.formed.singleton_of_mem member
termination_by sizeOf cert
decreasing_by all_goals simp_wf; omega

/-- Every retained row is intrinsically admitted at the shared domain,
and its output is a formed code demand. -/
theorem PiRows.typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    {key : Key n} {output : Profile n} (hm : (key, output) ∈ rows) :
    key.input.HasType ambient ∧ output.HasType (.sort true) := by
  match bodies with
  | .nil => cases hm
  | .cons guard body normal covered tail =>
    rcases List.mem_cons.mp hm with he | ht
    · cases he; exact ⟨guard.inputTyped, body.formed⟩
    · exact tail.typed ht
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega

/-- Form a nonempty source Pi certificate directly from its finite domain
and anchored codomain observations. No semantic interpretation is assumed. -/
noncomputable def CodeCert.pi
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {A B prototypeDomain prototypeBody : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    {domainFootprint rowFootprint : Footprint}
    (domain : CodeCert env U registry Γ locals σ A ambient domainFootprint)
    (guard : PiGuard env U Γ σ A B prototypeDomain prototypeBody)
    (bodies : PiRows env U registry Γ locals σ A B ambient rows rowFootprint) :
    CodeCert env U registry Γ locals σ (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody ambient rows)
      (domainFootprint ++ rowFootprint) := by
  refine .seed (.pi domain guard bodies) (Profile.HasType.pi_iff.mpr ⟨?_, ?_⟩)
  · apply Profile.WF.pi_iff.mpr
    exact ⟨domain.formed, fun key output hm =>
      ⟨(bodies.typed hm).1, (bodies.typed hm).2.wf_value⟩⟩
  · exact fun key output hm => (bodies.typed hm).2

/-- The initial lambda type certificate uses the literal realized source
prototype; subsequent equality transport can retain it using PiGuard. -/
noncomputable def CodeCert.piLiteral
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    {domainFootprint rowFootprint : Footprint}
    (domain : CodeCert env U registry Γ locals σ A ambient domainFootprint)
    (bodies : PiRows env U registry Γ locals σ A B ambient rows rowFootprint) :
    CodeCert env U registry Γ locals σ (.forallE A B)
      (Profile.pi (A.subst σ) (B.subst σ.lift) ambient rows)
      (domainFootprint ++ rowFootprint) := domain.pi PiGuard.literal bodies

/-- An occurrence of a computational observation in this certificate.
This relation never manufactures a source observation or a typing proof. -/
inductive CodeCert.Leaf
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr} :
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
      CodeCert env U registry Γ locals σ expression profile footprint →
    {m : Nat} → {demand : Profile m} → {required : Footprint} →
      Obs env U registry Γ locals σ expression demand required → Prop where
  | seed {observation : Obs env U registry Γ locals σ expression demand required}
      {hsort : demand.HasType (.sort true)} : Leaf (.seed observation hsort) observation
  | left (leaf : Leaf left observation) : Leaf (.union left right) observation
  | right (leaf : Leaf right observation) : Leaf (.union left right) observation
  | pad (leaf : Leaf source observation) : Leaf (.pad source) observation
  | unpad (leaf : Leaf source observation) : Leaf (.unpad source) observation
  | down (leaf : Leaf source observation) : Leaf (.down source) observation
  | map (leaf : Leaf source observation) : Leaf (.map view source) observation
  | select (leaf : Leaf source observation) : Leaf (.select source member) observation

/-- Every requested leaf retains its original intrinsic formation evidence. -/
theorem CodeCert.Leaf.formed
    {cert : CodeCert env U registry Γ locals σ expression profile footprint}
    {observation : Obs env U registry Γ locals σ expression demand required}
    (leaf : cert.Leaf observation) : demand.HasType (.sort true) := by
  induction leaf with
  | seed => assumption
  | left _ ih | right _ ih | pad _ ih | unpad _ ih | down _ ih | map _ ih | select _ ih => exact ih

/-- Apply an ORIGINAL type-child induction hypothesis only to the stored
computational leaves. Every proof extension is retained in the conclusion. -/
theorem CodeCert.interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression left right : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression profile footprint)
    (seeds : ∀ {m : Nat} {demand : Profile m} {required : Footprint}
      (observation : Obs env U registry Γ locals σ expression demand required),
      cert.Leaf observation → FramedCode env U registry Γ left right demand) :
    FramedCode env U registry Γ left right profile := by
  match cert with
  | .seed observation formed => exact seeds observation .seed
  | .union left right =>
    exact (left.interpret henv hscoped fun observation leaf =>
      seeds observation (.left leaf)).union henv
      (right.interpret henv hscoped fun observation leaf => seeds observation (.right leaf))
  | .pad source =>
    obtain ⟨Δ, ρ, insertion, code⟩ := source.interpret henv hscoped
      fun observation leaf => seeds observation (.pad leaf)
    refine ⟨Δ, ρ, insertion, ?_⟩
    simpa only [Profile.rename_pad] using code.pad henv
  | .unpad source =>
    obtain ⟨Δ, ρ, insertion, code⟩ := source.interpret henv hscoped
      fun observation leaf => seeds observation (.unpad leaf)
    refine ⟨Δ, ρ, insertion, ?_⟩
    rw [Profile.rename_pad] at code
    exact (TypeRelated.pad_iff henv).mp code
  | .down source =>
    obtain ⟨Δ, ρ, insertion, code⟩ := source.interpret henv hscoped
      fun observation leaf => seeds observation (.down leaf)
    refine ⟨Δ, ρ, insertion, ?_⟩
    simpa only [Profile.down_rename] using code.down henv
  | .map view source =>
    obtain ⟨Δ, ρ, insertion, code⟩ := source.interpret henv hscoped
      fun observation leaf => seeds observation (.map leaf)
    refine ⟨Δ, ρ, insertion, ?_⟩
    have mapped := (view.future henv insertion.toFuture).codeMap henv hscoped code
    simpa only [← AtomView.mapType_future] using mapped
  | .select source member =>
    obtain ⟨Δ, ρ, insertion, code⟩ := source.interpret henv hscoped
      fun observation leaf => seeds observation (.select leaf)
    refine ⟨Δ, ρ, insertion, ?_⟩
    simpa only [Profile.rename_singleton] using
      code.singleton (List.mem_map_of_mem (f := Atom.rename ρ) member)
termination_by sizeOf cert
decreasing_by all_goals simp_wf; omega

/-- Convenient seed boundary for a joint theorem's original type child.
The assigned type and its support may vary by actual leaf; neither is
reinterpreted as a new induction hypothesis. -/
theorem CodeCert.interpretRelated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {σ : Subst} {expression left right : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression profile footprint)
    (seeds : ∀ {m : Nat} {demand : Profile m} {required : Footprint}
      (observation : Obs env U registry Γ locals σ expression demand required),
      cert.Leaf observation → ∃ type support,
        Related env U registry Γ left right type demand support) :
    FramedCode env U registry Γ left right profile := by
  apply cert.interpret henv hscoped
  intro m demand required observation leaf
  obtain ⟨type, support, related⟩ := seeds observation leaf
  exact related.codeInFrame henv hΓ leaf.formed

end Lean4Lean.AnchoredSource
