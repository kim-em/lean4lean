import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePiRule
import Lean4Lean.Theory.Typing.AnchoredOriginalTailLambda
import Lean4Lean.Theory.Typing.AnchoredSortableTransferClosures

/-! Rich lambda queries retain their actual domain certificates, body queries,
and captured source-tail frames across future target contexts. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
structure SortableCoveredLambda (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (A body : VExpr) (key : Key n) (output : Atom n) where
  domainSupport : Profile n
  domainFootprint : Footprint
  domain : SortableCert env U registry target locals realization A true domainSupport domainFootprint
  guard : LambdaGuard env U registry target realization A key domainSupport
  bodyFootprint : Footprint
  bodyObservation : SortableObs env U registry target (Locals.push locals)
    (realization.cons key.anchor) body (.singleton output) bodyFootprint
  outside : Footprint
  packed : Profile n
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms

structure SortableLambdaTypeResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (localNeeds : List Need)
    (A B body other : VExpr) (key : Key n) (output : Atom n) (domain : Profile n) where
  resultSupport : Profile n
  bodyFootprint : Footprint
  bodyCertificate : SortableCert env U registry target (Locals.push locals)
    (realization.cons key.anchor) B true resultSupport bodyFootprint
  bodyAvailable : bodyFootprint.Available (Valuation.push localNeeds available)
  outputTyped : (Profile.singleton output).HasType resultSupport
  footprint : Footprint
  certificate : SortableCert env U registry target locals realization (.forallE A B) true
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])
    footprint
  available : footprint.Available available
  typed : (Profile.fn key output).HasType
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])

noncomputable def SortableLambdaTypeResult.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {inputFootprint : Footprint} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domain : Profile n}
    (fixed : SortableLambdaTypeResult env U registry target locals realization available
      (inputFootprint.localNeeds ++ inputFootprint.localNeeds.flatMap Need.singletons) A B body other key output domain) :
    SortableLambdaTypeResult env U registry future locals (realization.lift_r ρ)
      (Valuation.rename ρ available) ((Footprint.rename ρ inputFootprint).localNeeds ++
        (Footprint.rename ρ inputFootprint).localNeeds.flatMap Need.singletons)
      A B body other (key.rename ρ) (output.rename ρ) (domain.rename ρ) where
  resultSupport := fixed.resultSupport.rename ρ
  bodyFootprint := Footprint.rename ρ fixed.bodyFootprint
  bodyCertificate := by
    simpa only [subst_cons_future, Key.rename] using fixed.bodyCertificate.future henv insertion
  bodyAvailable := by
    simpa only [Valuation.rename_push, Footprint.atomized_localNeeds_rename] using
      fixed.bodyAvailable.rename ρ
  outputTyped := by
    simpa only [Profile.rename_singleton] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.outputTyped
  footprint := Footprint.rename ρ fixed.footprint
  certificate := by
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename,
      List.map_cons, List.map_nil, lift'_subst, ← Subst.lift_r_lift] using
      fixed.certificate.future henv insertion
  available := fixed.available.rename ρ
  typed := by
    simpa only [Profile.fn, Profile.pi, Profile.rename_singleton, Atom.rename_fn,
      Atom.rename_pi, Rows.rename, List.map_cons, List.map_nil, lift'_subst,
      ← Subst.lift_r_lift] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.typed

noncomputable def SortableCoveredLambda.observation
    (node : SortableCoveredLambda env U registry target locals realization A body key output) :
    SortableObs env U registry target locals realization (.lam A body) (Profile.fn key output)
      (node.domainFootprint ++ node.outside) :=
  .lam node.domain node.guard node.bodyObservation node.pack node.covered

namespace OriginalTail
theorem SortableTailPairedFits.pushGradedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (closed : available.AtomClosed)
    (domainChild : SortableComputationalTransfer env U registry target locals σ τ available A A (.sort level))
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (domain : SortableCert env U registry target locals σ A true support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Nonempty (SortableTailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available)) := by
  obtain ⟨rightDomain⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget domainChild domain domainAvailable
  exact ⟨fits.pushCertificates originalDomain domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered⟩


theorem HereditaryTailJoint.right
    {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : HereditaryTailJoint env registry context left right type) :
    HereditaryTailJoint env registry context right right type := original.symm.left henv hscoped
end OriginalTail

end Lean4Lean.AnchoredSource.Adapted
