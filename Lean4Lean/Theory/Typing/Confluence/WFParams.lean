import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.Confluence.QuotCoverage
import Lean4Lean.Theory.Typing.Confluence.SingletonPatCoverage
import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.CanonicalEq

/-! # Confluence of a well-formed environment

The `Params` instance of a well-formed environment (`VEnv.WF.params`), its coverage of the
stored equations (`VEnv.WF.equationCoverage`: the δ rules of the definitions and the quotient
rule) and of the registered ι rules (`VEnv.WF.patCoverage`), and the confluence theorem
`VEnv.WF.church_rosser` for every well-formed environment with canonical `Eq`.

A registered ι rule (`IsDefEq.pat`) fired at a typed instance is a pattern step of the engine
(`ParRed.extra`) unless its recursor is large-eliminating and the source of the instance's
major is `Prop`; that instance is covered by the singleton prefix unfolding
(`VEnv.WF.singletonPatCoverage`). -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The stored quotient rule is installed only with the quotient declaration. -/
theorem WF'.quotRegistered {env : VEnv} {ds : List VDecl} (H : env.WF' ds)
    (hq : env.defeqs quotDefEq) : QuotRegistered env := by
  induction H with
  | empty => cases hq
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    exact (ihCtors (by simpa using hq)).mono addProjections_le
  | @decl d env' ds env hd H ih =>
    have old : env.defeqs quotDefEq → QuotRegistered env' := fun h => (ih h).mono hd.le
    have notDef : ∀ ci : VDefVal, quotDefEq ≠ ci.toDefEq := fun ci h => by
      have := congrArg VDefEq.lhs h
      simp [quotDefEq, VDefVal.toDefEq] at this
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 => rw [addConst_defeqs h2] at hq; exact old hq
    | «example» _ => exact ih hq
    | «def» _ h2 =>
      rcases hq with h | h
      · exact (notDef _ h).elim
      · rw [addConst_defeqs h2] at h; exact old h
    | mutualDef _ h2 _ =>
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hq
      rcases hq with hm | h
      · obtain ⟨ci, -, h⟩ := List.mem_map.1 hm; exact (notDef _ h.symm).elim
      · rw [addConsts_defeqs h2] at h; exact old h
    | quot _ h2 =>
      exact ⟨addQuot_quot h2, addQuot_quotMk h2, addQuot_quotLift h2, addQuot_quotInd h2,
        addQuot_defeq h2⟩
    | induct _ h2 => rw [addInduct_defeqs h2] at hq; exact old hq

section
variable {env : VEnv} (henv : env.WF) (U : Nat)

private theorem PatternReductionTrace.of_definition
    (H : PatternReductionTrace env U (DefinitionPattern env.definitionRegistry) Γ left right) :
    PatternReductionTrace env U (ConcretePattern env) Γ left right := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih ih' => exact .trans ih ih'
  | pattern hp hm hc => exact .pattern (.inl hp) hm hc
  | beta => exact .beta
  | app _ _ ih ih' => exact .app ih ih'
  | lam _ ih => exact .lam ih

/-- **Coverage of the stored equations**: the δ rule of a definition and the quotient rule
join at every universe specialization. -/
theorem WF.equationCoverage : @FullEquationCoverage (henv.params U) := by
  letI := henv.params U
  refine ⟨fun {Γ equation levels} hΓ hdf hw hl => ?_⟩
  obtain ⟨ds, H⟩ := henv
  rcases H.defeqs_origin hdf with rfl | ⟨value, hv, rfl⟩
  · have hr := H.quotRegistered hdf
    exact QuotRegistered.equation_covered hΓ hr (.inr (.inl (.intro hr))) hw hl
  · have hlookup := WF.definitionRegistry_of_defeq ⟨ds, H⟩ hv
    have htrace := (DefinitionPattern.equation_trace (U := U) (Γ := Γ) hlookup
      (hv.closed ⟨ds, H⟩) hl).of_definition
    exact ⟨_, _, htrace.parRedS.full, .rfl,
      .refl (IsDefEq.extra (Γ := Γ) hdf hw hl).hasType.2⟩

theorem _root_.Lean4Lean.InductiveSignature.RecursorData.guard_OK {data : RecursorData}
    {p : Pattern} {df : VExpr → VExpr → Prop} {m1 : List VLevel} {m2 : p.Path → VExpr} :
    (data.guard p).OK df m1 m2 ↔
      ¬(data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero) := by
  unfold RecursorData.guard
  split <;> simp_all [Pattern.Check.OK]

/-- **Coverage of the registered ι rules**: every typed instance of a registered rule joins its
reduct, by one pattern step where the universe guard of its recursor holds, and by the singleton
prefix unfolding where the source of its major is `Prop`. -/
theorem WF.patCoverage (heq : env.HasCanonicalEq) : @FullPatCoverage (henv.params U) := by
  letI := henv.params U
  refine ⟨fun {Γ p r e m1 m2 A chk} hΓ hp hm he hr hall => ?_⟩
  obtain ⟨recN, major, ctor, fields, data, rfl, hl, -, -, hG⟩ := henv.pats_guarded hp
  have hred := IsDefEq.pat hp hm he hr hall
  by_cases hzero : data.largeTarget = true ∧
      (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero
  · exact WF.singletonPatCoverage henv U heq hΓ hp
      (by rw [SimplePattern.iota_headConst]; exact hl) hzero.1 hzero.2 hm he
  · have hok : (data.guard _).OK (IsDefEqU env U Γ) m1 m2 := RecursorData.guard_OK.mpr hzero
    have hstep : ParRed Γ e (r.1.apply m1 m2) :=
      ParRed.extra (r := (r.1, data.guard _)) (.inr (.inr hG)) hm hok fun _ => .rfl
    exact ⟨_, _, .tail .rfl (.core hstep), .rfl, .refl hred.hasType.2⟩

end

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv

/-- **Church-Rosser for definitional equality.** In a well-formed environment with canonical
`Eq`, two definitionally equal terms reduce, in the full presentation, to normally equal terms:
terms equal up to universe levels, proof irrelevance and eta.

Canonical `Eq` types the singleton prefix unfolding at a universe specialization whose source
is `Prop` (`WF.singletonPatCoverage`): the proof fields of the reconstructed constructor are
extracted by the recursor itself into `Prop`, with the earlier data fields cast along `Eq`. -/
theorem WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂' := by
  letI := henv.params U
  haveI := henv.equationCoverage U
  haveI := henv.patCoverage U heq
  obtain ⟨-, -, h⟩ := IsDefEq.full_church_rosser (Γ := Γ) hΓ H
  exact h

end Lean4Lean.VEnv
