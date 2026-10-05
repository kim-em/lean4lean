import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiShape
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
theorem SortablePiProfileOrigins.value_shape
    {value : Profile n} {atom : Atom n}
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile n))
    (typed : value.HasType profile)
    (member : atom ∈ value.atoms) : NormalFunction atom := by
  induction n with
  | zero =>
    obtain ⟨cover, hm, _⟩ := typed atom member
    exact (origins cover hm).elim
  | succ n ih =>
    obtain ⟨cover, hm, ht⟩ := typed.2.2 atom member
    have origin := origins cover hm
    cases cover with
    | sort | fn | family | ctor | record => exact origin.elim
    | pi protoDomain protoBody domain rows =>
      cases atom with
      | sort | pi | pad | family | ctor | record => contradiction
      | fn key output => exact ⟨AdapterNormal.key key, AdapterNormal.atom output, rfl⟩
    | pad cover =>
      cases atom with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad atom =>
        have smaller : SortablePiProfileOrigins env U registry target locals σ available A B
            (Profile.singleton cover) := by
          intro a hm
          cases List.mem_singleton.mp hm
          exact origin
        have shape := ih smaller ht (List.mem_singleton_self _)
        cases n with
        | zero => exact shape.elim
        | succ n =>
          obtain ⟨key, output, he⟩ := shape
          refine ⟨AdapterNormal.shiftKey key, AdapterNormal.shiftAtom output, ?_⟩
          rw [AdapterNormal.atom_pad, he]
          rfl
theorem SortableCert.piRowOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    {profile : Profile (n + 1)}
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile) :
    ∃ result, Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := certificate.piOriginsOriginal henv hscoped hle hTarget closed context
    originalDomain originalBody substitutions tail domainIH bodyIH resources
  exact ⟨result, certificate.piRowOfOrigins origins member row, resultTyped⟩

end Lean4Lean.AnchoredSource.Adapted
