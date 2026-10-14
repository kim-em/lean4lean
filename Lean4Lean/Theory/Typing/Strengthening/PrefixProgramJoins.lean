import Lean4Lean.Theory.Typing.Strengthening.SeparatedConfluence
import Lean4Lean.Theory.Typing.Strengthening.ClosedSingletonUnfolding
import Lean4Lean.Theory.Typing.Strengthening.ClosedQuotUnfolding

/-! # Exact joins between generated prefix programs

Even an indexed singleton's checked prefixes share a generated zero-prefix
syntax template. Beta specializes that template at each supplied argument list.
The template is used only as a raw common ancestor: no unfolding equation or
check at the zero prefix is asserted. Raw separated confluence therefore joins
changed prefix programs without aligning their lambda annotations by normal
comparison or assuming a strengthening front.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params] {D : Definitions}

/-- Beta paths are included in separated computation. -/
theorem SeparatedPatternCompute.of_beta (R : BetaRed a b) : SeparatedPatternCompute D a b :=
  .base (.base (.of_beta R))

/-- Compute a head and all arguments along an application spine. -/
theorem SeparatedPatternCompute.mkApps (HF : SeparatedPatternCompute D f f')
    (HA : List.Forall₂ (SeparatedPatternCompute D) args args') :
    SeparatedPatternCompute D (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

/-- Any two checked singleton prefixes at the same registered head and universe
instance are beta specializations of one raw template, even when indexed. The
contexts and supplied prefix lengths may differ. -/
theorem singleton_common_template
    (H1 : PrefixUnfold env univs recursorData Γ1 name levels args1 rhs1)
    (H2 : PrefixUnfold env univs recursorData Γ2 name levels args2 rhs2) :
    ∃ template, BetaRed (mkApps template args1) rhs1 ∧ BetaRed (mkApps template args2) rhs2 := by
  cases H1 with
  | intro hlookup hr hname hlarge hw hz hg hc =>
    cases H2 with
    | intro hlookup' hr' hname' hlarge' hw' hz' hg' hc' =>
      cases Option.some.inj (hlookup.symm.trans hlookup')
      obtain ⟨zero, hg0⟩ := RecursorData.singletonUnfolding_anyArity hg (args' := []) (by simp)
      exact ⟨zero.rhs, ClosedSingleton.generated_prefix_beta henv hr hlarge hz hg0 hg,
        ClosedSingleton.generated_prefix_beta henv hr hlarge hz hg0 hg'⟩

/-- The quotient generator likewise supplies a shared raw zero-prefix template. -/
theorem quotient_common_template
    (H1 : QuotPrefixUnfold env univs Γ1 levels args1 rhs1)
    (H2 : QuotPrefixUnfold env univs Γ2 levels args2 rhs2) :
    ∃ template, BetaRed (mkApps template args1) rhs1 ∧ BetaRed (mkApps template args2) rhs2 := by
  cases H1 with
  | intro hr hw hz hg hc =>
    cases H2 with
    | intro hr' hw' hz' hg' hc' =>
      obtain ⟨zero, hg0⟩ := QuotPrefixUnfolding.generate_anyArity hg (args' := []) (by simp)
      exact ⟨zero.rhs, ClosedQuot.generated_prefix_beta hg0 hg, ClosedQuot.generated_prefix_beta hg0 hg'⟩

/-- Two specializations of one template join after computation of supplied
arguments. The template and its intermediate applications need no typing. -/
theorem specialized_program_join
    (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HB1 : BetaRed (mkApps template args1) rhs1)
    (HB2 : BetaRed (mkApps template args2) rhs2)
    (HA : List.Forall₂ (SeparatedPatternCompute D) args1 args2) :
    ∃ out, SeparatedPatternCompute D rhs1 out ∧ SeparatedPatternCompute D rhs2 out := by
  have R : SeparatedPatternCompute D (mkApps template args1) (mkApps template args2) :=
    .mkApps (.base (.base .refl)) HA
  exact (SeparatedPatternCompute.of_beta HB1).confluent hd hr (R.trans (.of_beta HB2))

/-- Changed singleton prefix arguments yield an exact computational join of the
checked generated outputs, including all their domain annotations. -/
theorem singleton_program_join
    (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H1 : PrefixUnfold env univs recursorData Γ1 name levels args1 rhs1)
    (H2 : PrefixUnfold env univs recursorData Γ2 name levels args2 rhs2)
    (HA : List.Forall₂ (SeparatedPatternCompute D) args1 args2) :
    ∃ out, SeparatedPatternCompute D rhs1 out ∧ SeparatedPatternCompute D rhs2 out := by
  obtain ⟨template, HB1, HB2⟩ := singleton_common_template H1 H2
  exact specialized_program_join hd hr HB1 HB2 HA

/-- The same exact join covers changed quotient prefix arguments. -/
theorem quotient_program_join
    (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H1 : QuotPrefixUnfold env univs Γ1 levels args1 rhs1)
    (H2 : QuotPrefixUnfold env univs Γ2 levels args2 rhs2)
    (HA : List.Forall₂ (SeparatedPatternCompute D) args1 args2) :
    ∃ out, SeparatedPatternCompute D rhs1 out ∧ SeparatedPatternCompute D rhs2 out := by
  obtain ⟨template, HB1, HB2⟩ := quotient_common_template H1 H2
  exact specialized_program_join hd hr HB1 HB2 HA

end Lean4Lean.VEnv.Strengthening.PureObservation
