import Lean4Lean.Theory.Typing.AnchoredNativeRetelescopeBinder

/-! Registered-prefix advancement for actual source code rows. Empty result
profiles are allowed: no invented function output atom or intrinsic fn typing
is needed to traverse a domain-only request. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace PiRowCertificate
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
  {A B : VExpr} {key : Key n} {result : Profile n}
  (row : PiRowCertificate env U registry target locals σ available A B key result)

def codeNeeds : List Need :=
  row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons

theorem codeCoverage :
    ∀ need ∈ row.codeNeeds, need.rank ≤ n ∧
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
  intro need member
  obtain ⟨bound, included⟩ := row.pack.atomized_localNeeds need member
  exact ⟨bound, fun atom ha => row.covered atom (included atom ha)⟩

theorem codeClosed (closed : available.AtomClosed) :
    (Valuation.push row.codeNeeds available).AtomClosed :=
  Valuation.push_atomized_closed closed _

theorem codeAvailable :
    row.bodyFootprint.Available (Valuation.push row.codeNeeds available) :=
  row.pack.available_atomized_localNeeds row.outsideAvailable

/-- The registered domain's ORIGINAL formation child interprets the actual
row certificate. Its finite domain chain transfers the stored anchor admission,
and the resulting pair of substitutions supports exactly the row body's leaves. -/
theorem pushCode
    {sourceEnv : VEnv} (henv : env.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ env) {source : List VExpr} {level : VLevel}
    (originalDomain : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available) :
    Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) ∧
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons key.anchor) (Valuation.push row.codeNeeds available) ∧
    row.bodyFootprint.Available (Valuation.push row.codeNeeds available) := by
  obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    (originalDomain.2 target locals σ σ available closed hTarget substitutions fits).1
    row.domainAvailable
  have admitted := row.alignment.admission henv row.anchor
  obtain ⟨_, anchorTyped, _, _, _, _, anchorRelated, _⟩ := admitted
  have related := Related.retag henv row.inputTyped domain.related anchorRelated
  exact ⟨.cons substitutions (originalDomain.1.defeq.mono hle) anchorTyped,
    fits.pushDiagonal henv hTarget row.domain row.domainAvailable row.inputTyped related
      row.codeNeeds (fun need hm => (row.codeCoverage need hm).1)
      (fun need hm => (row.codeCoverage need hm).2), row.codeAvailable⟩

end PiRowCertificate
end Lean4Lean.AnchoredSource.Adapted
