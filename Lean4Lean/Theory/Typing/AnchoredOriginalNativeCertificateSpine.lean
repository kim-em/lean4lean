import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredNativeBinderPair

/-! Native binders retain their finite, source-syntactic certificates rather
than erasing them into `PairedFits`. This permits the common equation prefix
to be rebuilt at its own actual original domain references. Legacy certificates
do not carry an outer original endpoint, so this reconstruction copies their
payloads; it does not reorigin any rich original query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

inductive NativeCertificateSpine (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    (source : List VExpr) → Subst → Subst → Valuation → Type where
  | nil : NativeCertificateSpine env U registry target [] σ τ (fun _ => [])
  | cons {source : List VExpr} {σ τ : Subst} {available : Valuation}
      {domain x y : VExpr} {support input : Profile n} {footprint : Footprint}
      (previous : NativeCertificateSpine env U registry target source σ τ available)
      (certificate : CodeCert env U registry target (List.range source.length) σ
        domain support footprint)
      (resources : footprint.Available available) (typed : input.HasType support)
      (arguments : Related env U registry target x y (domain.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      NativeCertificateSpine env U registry target (domain :: source)
        (σ.cons x) (τ.cons y) (available.push needs)

/-- Rebuild at the given original context, using its actual references and
exactly the finite stored certificates. There is no semantic callback. -/
noncomputable def NativeCertificateSpine.frame
    (spine : NativeCertificateSpine env U registry target source σ τ available)
    (context : ContextDerivation sourceEnv U source) :
    OriginalRichFrame sourceEnv env U registry target context (List.range source.length)
      σ τ available := by
  match spine, context with
  | .nil, .nil => exact .nil
  | .cons previous certificate resources typed arguments needs bounded covered, .cons tail domain =>
    simpa only [List.length_cons, List.range_succ_eq_map, Locals.push] using
      OriginalRichFrame.bind (previous.frame tail) domain
        (.legacy (.ofCode certificate certificate.formed)) resources typed arguments needs bounded covered
termination_by structural spine

theorem NativeCertificateSpine.fitsLeft
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (spine : NativeCertificateSpine env U registry target source σ τ available) :
    PairedFits env U registry source target (List.range source.length) σ σ available := by
  induction spine with
  | nil => exact .nil
  | cons previous certificate resources typed arguments needs bounded covered ih =>
    simpa only [List.length_cons, List.range_succ_eq_map, Locals.push] using
      ih.pushCertificates henv formed certificate certificate resources resources typed typed
        arguments.left_diagonal arguments.left_diagonal needs bounded covered

/-- Removing a common-prefix suffix retains the very same stored tail. -/
def NativeCertificateSpine.tail
    (spine : NativeCertificateSpine env U registry target (domain :: source) σ τ available) :
    NativeCertificateSpine env U registry target source σ.tail τ.tail (fun i => available (i + 1)) := by
  cases spine with
  | cons previous certificate resources typed arguments needs bounded covered => exact previous

def NativeCertificateSpine.drop
    (later : List VExpr)
    (spine : NativeCertificateSpine env U registry target (later ++ source) σ τ available) :
    NativeCertificateSpine env U registry target source
      (fun i => σ (i + later.length)) (fun i => τ (i + later.length))
      (fun i => available (i + later.length)) := by
  cases later with
  | nil => exact spine
  | cons domain later =>
    simpa only [List.length_cons, Subst.tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      spine.tail.drop later
termination_by later.length

/-- The operative binder step constructs the stored relation from its actual
guard and admitted argument. It retains the exact certificate and demand pack
needed by subsequent native capture replay. -/
noncomputable def NativeCertificateSpine.bindGuard
    (henv : env.Ordered)
    (spine : NativeCertificateSpine env U registry target source σ τ available)
    {domain : VExpr} {key : Key n} {support packed : Profile n}
    {domainFootprint required outside : Footprint}
    (certificate : CodeCert env U registry target (List.range source.length) σ
      domain support domainFootprint)
    (guard : LambdaGuard env U registry target σ domain key support)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : (domainFootprint ++ outside).Available available)
    {argument : VExpr} (admitted : Admitted env U registry target key argument argument) :
    NativeCertificateSpine env U registry target (domain :: source)
      (σ.cons key.anchor) (τ.cons argument)
      (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available) := by
  have domainResources : domainFootprint.Available available :=
    fun i need hm => resources i need (List.mem_append_left _ hm)
  have bounds := pack.atomized_localNeeds
  have related : Related env U registry target key.anchor argument
      (domain.subst σ) key.input support := by
    obtain ⟨_, _, _, _, _, _, anchor, _⟩ := admitted
    exact Related.convert henv guard.inputTyped guard.domains anchor
  exact .cons spine certificate domainResources guard.inputTyped related
    (required.localNeeds ++ required.localNeeds.flatMap Need.singletons)
    (fun need hm => (bounds need hm).1)
    (fun need hm atom ha => covered atom ((bounds need hm).2 atom ha))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
