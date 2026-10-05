import Lean4Lean.Theory.Typing.AnchoredNativeSpineCertificate
import Lean4Lean.Theory.Typing.AnchoredDomainChainView
import Lean4Lean.Theory.Typing.AnchoredNativeInitialArguments

/-! One concrete retelescoping step. A selected row of the actual registered
header retains its source domain/body certificates. Its finite domain chain
moves the anchor admission to the registered domain; the reverse value view
records the change back to the original natural-domain key. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

structure NativeRetelescopeBinder (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (A B : VExpr) (key : Key n) (output : Atom n) where
  result : Profile n
  row : PiRowCertificate env U registry target locals σ available A B key result
  resultTyped : (Profile.singleton output).HasType result
  guard : LambdaGuard env U registry target σ A (domainKey key (A.subst σ)) row.domainSupport

namespace NativeRetelescopeBinder
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
  {A B : VExpr} {key : Key n} {output : Atom n}
  (binder : NativeRetelescopeBinder env U registry target locals σ available A B key output)

def actualKey (_binder : NativeRetelescopeBinder env U registry target locals σ available A B key output) : Key n := domainKey key (A.subst σ)

def support : Profile (n + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) binder.row.domainSupport [(binder.actualKey, binder.result)]

def footprint : Footprint := binder.row.domainFootprint ++ binder.row.outside

/-- The recovered codomain child and its pack are literally unchanged. -/
noncomputable def certificate : CodeCert env U registry target locals σ (.forallE A B)
    binder.support binder.footprint := by
  apply CodeCert.piLiteral binder.row.domain
  simpa only [List.append_nil, actualKey] using
    PiRows.cons binder.guard binder.row.body binder.row.pack binder.row.covered PiRows.nil

theorem resources : binder.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (binder.row.domainAvailable i need)
    (binder.row.outsideAvailable i need)

theorem typed : (Profile.fn binder.actualKey output).HasType binder.support := by
  apply Profile.HasType.fn _ (List.mem_singleton_self _) binder.resultTyped
  refine Profile.WF.pi_iff.mpr ⟨binder.row.domain.formed, ?_⟩
  intro k r member
  cases List.mem_singleton.mp member
  exact ⟨binder.row.inputTyped, binder.row.body.formed.wf_value⟩

noncomputable def forward : AtomView env U registry target (n := n + 1)
    (AtomData.fn key output) (AtomData.fn binder.actualKey output) := by
  have view := binder.row.alignment.view key.anchor output
  cases key
  exact view

noncomputable def backward (henv : env.Ordered) : AtomView env U registry target (n := n + 1)
    (AtomData.fn binder.actualKey output) (AtomData.fn key output) :=
  binder.forward.inverse henv

/-- Rebuild only after the actual computational child footprint has been
packed. The header row's code-footprint pack does not stand in for this pack. -/
def initialTree
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    (binder : NativeRetelescopeBinder env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available A B key output)
    (origin : signature.domains[arguments.length]? = some A)
    {bodyFootprint outside : Footprint} {packed : Profile n}
    (body : NativeInitialTree env U registry target signature (arguments ++ [key.anchor])
      (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    NativeInitialTree env U registry target signature arguments
      (Profile.fn binder.actualKey output) (binder.row.domainFootprint ++ outside) :=
  .binder origin binder.row.domain binder.guard body pack covered

def plan
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    (binder : NativeRetelescopeBinder env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available A B key output)
    (origin : signature.domains[arguments.length]? = some A)
    {bodyFootprint outside : Footprint} {packed : Profile n}
    (body : NativePlan env U registry target signature (arguments ++ [key.anchor])
      (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    NativePlan env U registry target signature arguments
      (Profile.fn binder.actualKey output) (binder.row.domainFootprint ++ outside) :=
  .binder origin binder.row.domain binder.guard body pack covered

end NativeRetelescopeBinder

/-- Extract and reconstruct one registered binder through the original header
formation payload. No typing of the native head itself is interpreted. -/
theorem CodeCert.retelescopedBinder
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr}
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile (n + 1)} {footprint : Footprint} {key : Key n} {output : Atom n}
    (certificate : CodeCert env U registry target locals σ (.forallE A B) support footprint)
    (resources : footprint.Available available)
    (typed : (Profile.fn key output).HasType support) :
    Nonempty (NativeRetelescopeBinder env U registry target locals σ available A B key output) := by
  obtain ⟨domainLevel, rawDomain, originalDomain⟩ := header.domain.1
  obtain ⟨bodyLevel, rawBody, originalBody⟩ := header.codomain.1
  obtain ⟨result, ⟨row⟩, resultTyped⟩ := certificate.piRow henv hscoped hTarget closed
    (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) substitutions fits
    originalDomain originalBody resources typed
  obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    (originalDomain target locals σ σ available closed hTarget substitutions fits).1 row.domainAvailable
  have anchor := row.alignment.admission henv row.anchor
  exact ⟨{
    result := result
    row := row
    resultTyped := resultTyped
    guard := ⟨row.inputTyped, row.domain.formed, .refl, domain.related, anchor⟩ }⟩

end Lean4Lean.AnchoredSource.Adapted
