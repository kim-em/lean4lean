import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPairedApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence

/-! # A beta-only obstruction to common paired instantiation

A recursive type and its unfolded Pi are definitionally equal but beta-normal.
Common checking ignores their annotations on diagonal lambdas. Self-application
then forces an inferred function comparison, which retains those annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace ScopedLoopBoundary
open ProofShape
open private ctx_wf fn_typed fn_not_proof domain_typed body_typed diagonal_typed diagonal_at_domain
  from Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop

private abbrev emptyStep : List ProofShape → ProofShape → ProofShape → Prop := fun _ _ _ => False
private def body : ProofShape := .app (.bvar 0) (.bvar 0)
private def diagonal (D : ProofShape) : ProofShape := .lam D body
private def loop (D : ProofShape) : ProofShape := .app (diagonal D) (diagonal D)

omit [Params] in
private theorem empty_beta (H : ScopedCompute emptyStep Δ a b) : ProofShape.BetaRed a b := by
  induction H with
  | base H => exact H.elim
  | beta H => exact H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

omit [Params] in
private theorem normal_fixed (hn : NormalSyntax (fun _ _ => False) a)
    (H : ScopedCompute emptyStep Δ a b) : b = a := (empty_beta H).fixed_of_normal hn

omit [Params] in
private theorem diagonal_normal (hn : NormalSyntax (fun _ _ => False) D) :
    NormalSyntax (fun _ _ => False) (diagonal D) := by
  exact ⟨fun _ H => H, hn, fun _ H => H, (fun _ _ H => nomatch H),
    ⟨fun _ H => H, trivial⟩, ⟨fun _ H => H, trivial⟩⟩

omit [Params] in
private theorem loop_beta_fixed (hn : NormalSyntax (fun _ _ => False) D)
    (R : ProofShape.BetaRed (loop D) out) : out = loop D := by
  suffices aux : ∀ {e out}, ProofShape.BetaRed e out → e = loop D → out = loop D from aux R rfl
  intro e out R
  induction R with
  | refl => exact id
  | trans _ _ ih₁ ih₂ => exact fun E => ih₂ (ih₁ E)
  | app Rf Ra =>
    intro E
    cases E
    rw [Rf.fixed_of_normal (diagonal_normal hn), Ra.fixed_of_normal (diagonal_normal hn)]
    rfl
  | beta =>
    intro E
    cases E
    simp [loop, diagonal, body, ProofShape.inst, ProofShape.liftN_zero]
  | proj | lam | forallE => intro E; cases E

omit [Params] in
private theorem no_lift_zero (f : ProofShape) : f.liftN 1 ≠ .bvar 0 := by
  cases f <;> simp [ProofShape.liftN, liftVar]

omit [Params] in
private theorem no_eta_diagonal (H : EtaHead (diagonal D) f) : False := by
  generalize E : diagonal D = a at H
  cases H with
  | boundVar => exact no_lift_zero _ (ProofShape.app.inj (ProofShape.lam.inj E).2).1.symm
  | proof => cases (ProofShape.app.inj (ProofShape.lam.inj E).2).2

omit [Params] in
private theorem no_constructor_diagonal
    (E : diagonal D = ProofShape.mkApps (.const c ls) args) : False := by
  have H := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead_mkApps, ProofShape.constHead, diagonal] at H
  cases H

omit [Params] in
private theorem no_constructor_loop
    (E : loop D = ProofShape.mkApps (.const c ls) args) : False := by
  have H := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead_mkApps, loop, diagonal, ProofShape.constHead] at H
  cases H

private theorem diagonal_domains
    (hn : NormalSyntax (fun _ _ => False) D) (hn' : NormalSyntax (fun _ _ => False) D')
    (H : ScopedCompare emptyStep Δ mode (diagonal D) (diagonal D')) (hm : mode = false) :
    ScopedCompare emptyStep Δ true D D' := by
  generalize EA : diagonal D = a at H
  generalize EB : diagonal D' = b at H
  induction H generalizing D D' with
  | leaf H =>
    cases H with
    | refl => cases ProofShape.lam.inj (EA.trans EB.symm) |>.1; exact .refl
    | sort | const => cases EA
    | etaL | etaR => cases hm
  | lam HD HB => cases EA; cases EB; exact HD.common
  | lamSorted _ _ HD HB => cases EA; cases EB; exact HD
  | etaLams HD HE =>
    cases EA; cases EB
    exact (HE.elim no_eta_diagonal no_eta_diagonal).elim
  | compute RA RB HC ih =>
    exact ih hn hn' hm (normal_fixed (diagonal_normal hn) (EA ▸ RA)).symm
      (normal_fixed (diagonal_normal hn') (EB ▸ RB)).symm
  | symm HC ih => exact (ih hn' hn hm EB EA).symm
  | structFields => exact (no_constructor_diagonal EA).elim
  | lamCommon | etaBodyL | etaBodyR => cases hm
  | app | proj | forallE | forallSorted => cases EA

private theorem loop_domains
    (hn : NormalSyntax (fun _ _ => False) D) (hn' : NormalSyntax (fun _ _ => False) D')
    (H : ScopedCompare emptyStep Δ mode (loop D) (loop D')) :
    ScopedCompare emptyStep Δ true D D' := by
  generalize EA : loop D = a at H
  generalize EB : loop D' = b at H
  induction H generalizing D D' with
  | leaf H =>
    cases H with
    | refl =>
      have E := congrArg (fun x => match x with | .app (.lam D _) _ => D | _ => .proof) (EA.trans EB.symm)
      cases E; exact .refl
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | app HF HX => cases EA; cases EB; exact diagonal_domains hn hn' HF rfl
  | compute RA RB HC ih =>
    exact ih hn hn' (loop_beta_fixed hn (empty_beta (EA ▸ RA))).symm
      (loop_beta_fixed hn' (empty_beta (EB ▸ RB))).symm
  | symm HC ih => exact (ih hn' hn EB EA).symm
  | structFields => exact (no_constructor_loop EA).elim
  | etaBodyR => cases EB
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA

private def piHead : ProofShape → Bool
  | .forallE _ _ => true
  | _ => false

private theorem fixed_pi_head
    (H : ScopedCompare emptyStep Δ mode a b)
    (FA : ∀ {out}, ScopedCompute emptyStep Δ a out → out = a)
    (FB : ∀ {out}, ScopedCompute emptyStep Δ b out → out = b)
    (NA : ∀ A body, a ≠ .lam A body) (NB : ∀ A body, b ≠ .lam A body)
    (CA : ∀ {family info ls args}, env.projections family info →
      a ≠ ProofShape.mkApps (.const info.ctorName ls) args)
    (CB : ∀ {family info ls args}, env.projections family info →
      b ≠ ProofShape.mkApps (.const info.ctorName ls) args) : piHead a = piHead b := by
  induction H with
  | leaf H =>
    cases H with
    | refl | sort | const => rfl
    | etaL H => obtain ⟨A, body, E, _⟩ := H.shape; exact (NA A _ E).elim
    | etaR H => obtain ⟨A, body, E, _⟩ := H.shape; exact (NB A _ E).elim
  | app | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaLams => rfl
  | etaBodyL => exact (NA _ _ rfl).elim
  | etaBodyR => exact (NB _ _ rfl).elim
  | structFields hi => exact (CA hi rfl).elim
  | compute RA RB HC ih =>
    have EA := FA RA
    have EB := FB RB
    subst_vars
    exact ih FA FB NA NB CA CB
  | symm HC ih => exact (ih FB FA NB NA CB CA).symm

private def rawDomain (c : Name) : ProofShape := .app (.const c []) (.bvar 0)
private def rawUnfolded (c : Name) : ProofShape := .forallE (rawDomain c) (.sort .zero)

omit [Params] in
private theorem rawDomain_normal : NormalSyntax (fun _ _ => False) (rawDomain c) := by
  exact ⟨fun _ H => H, (fun _ _ H => nomatch H), ⟨fun _ H => H, trivial⟩, ⟨fun _ H => H, trivial⟩⟩

omit [Params] in
private theorem rawUnfolded_normal : NormalSyntax (fun _ _ => False) (rawUnfolded c) :=
  ⟨fun _ H => H, rawDomain_normal, ⟨fun _ H => H, trivial⟩⟩

private theorem domains_not_compare
    (hc : ∀ {family info}, env.projections family info → c ≠ info.ctorName)
    (H : ScopedCompare emptyStep Δ mode (rawDomain c) (rawUnfolded c)) : False := by
  have HE := fixed_pi_head H (normal_fixed rawDomain_normal) (normal_fixed rawUnfolded_normal)
    (fun _ _ H => nomatch H) (fun _ _ H => nomatch H) ?_ ?_
  · cases HE
  · intro family info ls args hi E
    have EH := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, rawDomain, ProofShape.constHead] at EH
    exact hc hi (Option.some.inj EH)
  · intro family info ls args hi E
    have EH := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, rawUnfolded, ProofShape.constHead] at EH
    cases EH

private theorem loops_not_compare
    (hc : ∀ {family info}, env.projections family info → c ≠ info.ctorName) :
    ¬ ScopedCompare emptyStep Δ mode (loop (rawDomain c)) (loop (rawUnfolded c)) :=
  fun H => domains_not_compare hc (loop_domains rawDomain_normal rawUnfolded_normal H)

private theorem erase_body (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ RecursiveDomain.selfBody (.sort .zero)) :
    proofErase Γ RecursiveDomain.selfBody = body := by
  have hn := not_isProof_of_sort hΓ ht
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  have hv := not_isProof_fn hΓ hf hx hn
  rw [show proofErase Γ RecursiveDomain.selfBody = .app _ _ from if_neg hn,
    show proofErase Γ (.bvar 0) = .bvar 0 from if_neg hv]
  rfl

private theorem erase_diagonal (hΓ : OnCtx Γ (env.IsType univs))
    (hD : env.HasType univs Γ D (.sort u))
    (hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero)) :
    proofErase Γ (RecursiveDomain.diagonal D) = diagonal (proofErase Γ D) := by
  have hn := not_isProof_function_to_sort hΓ (HasType.lam hD hb)
  rw [show proofErase Γ (RecursiveDomain.diagonal D) = .lam _ _ from if_neg hn,
    erase_body (Γ := D :: Γ) ⟨hΓ, u, hD⟩ hb]
  rfl

private theorem erase_loop (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (RecursiveDomain.omegaTerm D) (.sort .zero))
    (ED : proofErase Γ (RecursiveDomain.diagonal D) = diagonal d) :
    proofErase Γ (RecursiveDomain.omegaTerm D) = loop d := by
  rw [show proofErase Γ (RecursiveDomain.omegaTerm D) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ ht), ED]
  rfl

/-- Even a reflexively compared body can fail paired instantiation in the
beta-only fragment. All context, body and argument typings are supplied, and
the arguments share a common-lambda certificate. The recursive declaration's
unfolding is deliberately absent from this computation relation. -/
theorem same_body_beta_failure
    (hc : env.constants c = some (RecursiveDomain.declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    ∃ Γ A b B x y, OnCtx (A :: Γ) (env.IsType univs) ∧
      env.HasType univs (A :: Γ) b B ∧ env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      ScopedCompare (fun _ _ _ => False) (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y) ∧
      ¬ ScopedCompare (fun _ _ _ => False) (proofEraseCtx Γ) true
        (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have hΓ := ctx_wf
  have hD := domain_typed hc
  have HD := RecursiveDomain.domain_recursive hδ
  have hb := body_typed hδ
  let D := RecursiveDomain.domainL c
  let D' := VExpr.forallE D (.sort .zero)
  have hD' : env.HasType univs RecursiveDomain.loopCtx D' (.sort (.succ .zero)) := HD.hasType.2
  have hb' : env.HasType univs (D' :: RecursiveDomain.loopCtx) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx := diagonal_at_domain hc hδ
  have hy := HD.symm.defeq Hdiag.hasType.2
  have ED : proofErase RecursiveDomain.loopCtx D = rawDomain c := by
    have hn := not_isProof_of_sort hΓ hD
    have hcfn := not_isProof_function_to_sort hΓ (RecursiveDomain.family_typed hc univs RecursiveDomain.loopCtx)
    rw [show proofErase RecursiveDomain.loopCtx D = .app _ _ from if_neg hn,
      show proofErase RecursiveDomain.loopCtx (.const c []) = .const c [] from if_neg hcfn,
      show proofErase RecursiveDomain.loopCtx RecursiveDomain.fn = .bvar 0 from if_neg fn_not_proof]
    rfl
  have ED' : proofErase RecursiveDomain.loopCtx D' = rawUnfolded c := by
    rw [show proofErase RecursiveDomain.loopCtx D' = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hD'),
      ED, show proofErase (D :: RecursiveDomain.loopCtx) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort (Γ := D :: RecursiveDomain.loopCtx) ⟨hΓ, _, hD⟩ (HasType.sort (by trivial)))]
    rfl
  have EX : proofErase RecursiveDomain.loopCtx (RecursiveDomain.diagonal D) = diagonal (rawDomain c) :=
    (erase_diagonal hΓ hD hb).trans (congrArg diagonal ED)
  have EY : proofErase RecursiveDomain.loopCtx (RecursiveDomain.diagonal D') = diagonal (rawUnfolded c) :=
    (erase_diagonal hΓ hD' hb').trans (congrArg diagonal ED')
  have HX : ScopedCompare emptyStep (proofEraseCtx RecursiveDomain.loopCtx) true
      (proofErase RecursiveDomain.loopCtx (RecursiveDomain.diagonal D))
      (proofErase RecursiveDomain.loopCtx (RecursiveDomain.diagonal D')) := by
    rw [EX, EY]
    exact .lamCommon .refl
  refine ⟨RecursiveDomain.loopCtx, D, RecursiveDomain.selfBody, .sort .zero,
    RecursiveDomain.diagonal D, RecursiveDomain.diagonal D', ⟨hΓ, _, hD⟩, hb, hx, hy, HX, ?_⟩
  intro H
  have hleft := RecursiveDomain.omega_typed hc hδ
  have hright : env.HasType univs RecursiveDomain.loopCtx (RecursiveDomain.omegaTerm D') (.sort .zero) :=
    HasType.app Hdiag.hasType.2 hy
  have EL := erase_loop hΓ hleft EX
  have ER := erase_loop hΓ hright EY
  change ScopedCompare emptyStep (proofEraseCtx RecursiveDomain.loopCtx) true
    (proofErase RecursiveDomain.loopCtx (RecursiveDomain.omegaTerm D))
    (proofErase RecursiveDomain.loopCtx (RecursiveDomain.omegaTerm D')) at H
  rw [EL, ER] at H
  apply loops_not_compare (c := c) ?_ H
  intro family info hi E
  have HR : env.Rigid c := E ▸ henv.projectionCtorRigid hi
  exact IsDefEqU.rigidApp_forallE_inv (args := [RecursiveDomain.fn]) (ls := []) henv hΓ HR hD ⟨_, HD⟩

/-- Primitive descent and substitution stability do not imply common paired
instantiation. The failure already uses identical bodies, and does not refute
the law for computation including all installed definitions. -/
theorem not_paired_beta
    (hc : env.constants c = some (RecursiveDomain.declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    ¬ ScopedPairedInstantiation (fun _ _ _ => False) := by
  intro Hinst
  obtain ⟨Γ, A, b, B, x, y, hΓ, hb, hx, hy, HX, HN⟩ := same_body_beta_failure hc hδ
  exact HN (Hinst hΓ hb hb hx hy .refl HX)

/-- There is no uniform paired-instantiation theorem from primitive descent
and interpreted substitution stability alone, even with fully typed bodies and
arguments. A stronger theorem must constrain the computation relation. -/
theorem no_uniform_paired
    (hc : env.constants c = some (RecursiveDomain.declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    ¬ (∀ (Step : List ProofShape → ProofShape → ProofShape → Prop),
      ErasedScopedPrimitiveDescent Step →
      (∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
        Step Δ' (a.subst τ) (b.subst τ)) → ScopedPairedInstantiation Step) := by
  intro H
  apply not_paired_beta hc hδ
  exact H (fun _ _ _ => False)
    (by unfold ErasedScopedPrimitiveDescent; intros; contradiction)
    (by intros; contradiction)

omit [Params] in
/-- The beta-only paired-instantiation obstruction occurs in an actual
well-formed extension preserving canonical Eq. Primitive descent and interpreted
substitution stability hold for the empty primitive relation, so they cannot
alone establish this paired law. -/
theorem canonical_beta_paired_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (RecursiveDomain.extended base c).HasCanonicalEq ∧
    letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
    ¬ ScopedPairedInstantiation (fun _ _ _ => False) := by
  refine ⟨RecursiveDomain.extended_canonicalEq heq hfresh, ?_⟩
  letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
  apply not_paired_beta (c := c)
  · change (RecursiveDomain.extended base c).constants c = _
    simp [RecursiveDomain.extended, RecursiveDomain.stub, VEnv.addDefEq]
  · exact fun Γ => RecursiveDomain.equation 0 Γ

/-- The actual stored recursive equation repairs the two looping endpoints by
delta/beta computation of their annotations. The self-application bodies need
not normalize. Thus the beta-only obstruction is not a counterexample for the
full stored-definition core relation. -/
theorem delta_repair (hd : env.defeqs (RecursiveDomain.declaration c).toDefEq) :
    PureObservation.Compute ErasedCore.definitions
      (RecursiveDomain.omegaTerm (RecursiveDomain.domainL c))
      (RecursiveDomain.omegaTerm (.forallE (RecursiveDomain.domainL c) (.sort .zero))) := by
  have HD : ErasedCore.definitions.unfolds c [] (RecursiveDomain.familyValue c) := by
    apply Or.inl
    refine ⟨(RecursiveDomain.declaration c).toDefEq, [], hd, by simp, rfl, rfl, ?_⟩
    simp [RecursiveDomain.declaration, VDefVal.toDefEq, RecursiveDomain.familyValue,
      RecursiveDomain.argType, Developments.tower, VExpr.instL, VLevel.inst]
  have RD : PureObservation.Compute ErasedCore.definitions (RecursiveDomain.domainL c)
      (.forallE (RecursiveDomain.domainL c) (.sort .zero)) := by
    apply PureObservation.Compute.trans (.app (.delta HD) .refl)
    simpa [RecursiveDomain.familyValue, RecursiveDomain.domainL, VExpr.inst, instVar] using
      (PureObservation.Compute.beta (D := ErasedCore.definitions)
        (A := RecursiveDomain.argType)
        (b := VExpr.forallE (.app (.const c []) (.bvar 0)) (.sort .zero)) (a := RecursiveDomain.fn))
  exact .app (.lam RD .refl) (.lam RD .refl)

/-- The repair is visible in the actual erased core relation as well. It uses
only the installed recursive definition and beta, with both looping originals
retaining their exact erased endpoints. -/
theorem erased_delta_repair
    (hc : env.constants c = some (RecursiveDomain.declaration c).toVConstant)
    (hd : env.defeqs (RecursiveDomain.declaration c).toDefEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    ProofShape.Compute ErasedCore.Step
      (proofErase RecursiveDomain.loopCtx (RecursiveDomain.omegaTerm (RecursiveDomain.domainL c)))
      (proofErase RecursiveDomain.loopCtx
        (RecursiveDomain.omegaTerm (.forallE (RecursiveDomain.domainL c) (.sort .zero)))) := by
  have hδ (Γ) : env.IsDefEq univs Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType := by
    have H := IsDefEq.extra (Γ := Γ) (uvars := univs) (ls := []) hd (by simp) rfl
    simpa [RecursiveDomain.declaration, VDefVal.toDefEq, RecursiveDomain.familyType,
      RecursiveDomain.familyValue, RecursiveDomain.argType, Developments.tower,
      VExpr.instL, VLevel.params, VLevel.inst] using H
  exact proofErase_pattern_compute_forward
    (RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)) hcon ctx_wf
    (RecursiveDomain.omega_typed hc hδ) (.base (.base (delta_repair hd)))

end ScopedLoopBoundary
end Lean4Lean.VEnv.Strengthening
