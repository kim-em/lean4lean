import Lean4Lean.Theory.Typing.Strengthening.PrefixArgumentExchange
import Lean4Lean.Theory.Typing.Strengthening.StructurePrefixDisjoint

/-! # Exchange of ordinary paths with actual prefix roots

At a checked unsaturated prefix, ordinary computation preserves the head and
acts only on supplied arguments. The actual stored/structure definition union
has no delta at that head and those universes. Full generated-program congruence
therefore moves the entire ordinary path past the checked prefix contraction.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params

/-- A non-unfolding head is preserved at its exact universe instance. No
assumption about the same name at other universes is needed. -/
theorem Compute.const_spine_of (R : Compute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (Compute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | refl => exact ⟨_, he.symm, List.forall₂_of_getElem rfl (fun _ _ _ => .refl)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | delta hd =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh
    exact (hn _ hd).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | beta | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

variable [Params]

/-- Projection roots cannot alter a constant spine; delta exclusion is needed
only at the displayed universe instance. -/
theorem ProjectionCompute.const_spine_of
    (R : ProjectionCompute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (ProjectionCompute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.const_spine_of hn
    exact ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 he
    obtain ⟨_, h2, hl2⟩ := ih2 h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | projIota | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Excluding matches at every shorter prefix preserves an entire finite
ordinary-computation spine, with componentwise argument paths. -/
theorem PatternCompute.const_spine_of
    (R : PatternCompute D (VExpr.mkApps (.const c ls) args) out)
    (hn : ∀ rhs, ¬ D.unfolds c ls rhs)
    (hno : ∀ {p r pre lv vals}, Pat p r → pre.length ≤ n →
      p.Matches (VExpr.mkApps (.const c ls) pre) lv vals → False)
    (hlen : args.length ≤ n) :
    ∃ args', out = VExpr.mkApps (.const c ls) args' ∧ List.Forall₂ (PatternCompute D) args args' := by
  generalize he : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base R =>
    rw [← he] at R
    obtain ⟨args', h, HA⟩ := R.const_spine_of hn
    exact ⟨args', h, HA.imp (fun _ _ h => .base h)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, h1, hl1⟩ := ih1 hlen he
    obtain ⟨_, h2, hl2⟩ := ih2 (by rw [← hl1.length_eq]; exact hlen) h1.symm
    exact ⟨_, h2, hl1.trans (fun _ _ _ h h' => h.trans h') hl2⟩
  | pattern hp hm _ => exact (hno hp hlen (he.symm ▸ hm)).elim
  | app _ Ra ihf _ =>
    obtain ⟨args0, rfl, hh⟩ := RigidHead.const.mkApps_eq_app he
    obtain ⟨args1, h1, hl⟩ := ihf (by simp only [List.length_append, List.length_singleton] at hlen; omega) hh.symm
    exact ⟨args1 ++ [_], by rw [mkApps_snoc, ← h1], hl.append' (.cons Ra .nil)⟩
  | lam | forallE | proj =>
    have hh := congrArg getAppFn he
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Ordinary computation supplies the full untyped congruence interface. -/
theorem patternCompute_congrRel : CongrRel (fun _ => PatternCompute D) where
  rfl := .refl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN _ R := by
    simp only [← lift'_consN_skipN, RecursorData.lift'_eq_subst]
    exact R.subst

/-- An actual singleton prefix excludes all stored and selected-structure
unfoldings at the same head and universe instance. -/
theorem singleton_no_registered_definition
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs) :
    ∀ value, ¬ (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)).unfolds
      name levels value := by
  rintro value (HD | HD)
  · cases H with
    | intro hlookup hr hname hlarge hw hz hg hc =>
      obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
      obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
      exact Definitions.ofEnv_no_registered henv hr ⟨index, howner⟩ (hname ▸ HD)
  · exact HD.no_singleton H

/-- The registered quotient prefix likewise excludes the entire closed
stored/structure collection at its head. -/
theorem quotient_no_registered_definition
    (H : QuotPrefixUnfold env univs Γ levels args rhs) :
    ∀ value, ¬ (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)).unfolds
      ``Quot.lift levels value := by
  rintro value (HD | HD)
  · obtain ⟨value, hreg, hname, _⟩ := Definitions.ofEnv_origin henv HD
    have hv := (definitionRegistry_registered hreg).1
    exact henv.quotLift_not_definition H.registered.equation hv.2 (VLevel.params value.uvars)
      (by simp only [VDefVal.toDefEq, hname])
  · exact HD.not_quotient H.registered rfl

/-- Every ordinary finite path from a checked singleton prefix computes only
its supplied arguments. No source typing beyond the actual check is needed. -/
theorem singleton_ordinary_spine
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (R : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))
      (VExpr.mkApps (.const name levels) args) out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧
      List.Forall₂ (PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)))
        args args' := by
  have hn := singleton_no_registered_definition H
  cases H with
  | intro hlookup hr hname hlarge hw hz hg hc =>
    exact R.const_spine_of hn (fun hp hlen hm => Params.no_match_delta_prefix hlookup hp hlen hm)
      (RecursorData.singletonUnfolding_spec hg).1

/-- Ordinary finite paths from quotient prefixes also retain their exact head,
universe syntax and arity. -/
theorem quotient_ordinary_spine
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (R : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))
      (VExpr.mkApps (.const ``Quot.lift levels) args) out) :
    ∃ args', out = VExpr.mkApps (.const ``Quot.lift levels) args' ∧
      List.Forall₂ (PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)))
        args args' := by
  have hn := quotient_no_registered_definition H
  cases H with
  | intro hr hw hz hg hc =>
    exact R.const_spine_of hn (fun hp hlen hm => Params.no_match_quot_prefix hr hp hlen hm)
      (QuotPrefixUnfolding.generate_spec hg).2.1

/-- A finite ordinary path and a singleton root contraction commute exactly:
the residual root is actually checked and the other residual is still ordinary. -/
theorem singleton_ordinary_exchange (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (R : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))
      (VExpr.mkApps (.const name levels) args) out) :
    ∃ args' rhs', out = VExpr.mkApps (.const name levels) args' ∧
      PrefixUnfold env univs recursorData Γ name levels args' rhs' ∧
      PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) rhs rhs' := by
  obtain ⟨args', he, HA⟩ := singleton_ordinary_spine H R
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  obtain ⟨rhs', H', HR⟩ := singleton_prefix_congr patternCompute_congrRel
    (patternCompute_congrRel.argRel (fun hΓ R ht => R.simAt hs hΓ _ ht)) hΓ H HA
  exact ⟨args', rhs', he, H', HR⟩

/-- The analogous exact exchange for quotient roots and whole ordinary paths. -/
theorem quotient_ordinary_exchange (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (R : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))
      (VExpr.mkApps (.const ``Quot.lift levels) args) out) :
    ∃ args' rhs', out = VExpr.mkApps (.const ``Quot.lift levels) args' ∧
      QuotPrefixUnfold env univs Γ levels args' rhs' ∧
      PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) rhs rhs' := by
  obtain ⟨args', he, HA⟩ := quotient_ordinary_spine H R
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  obtain ⟨rhs', H', HR⟩ := quotient_prefix_congr patternCompute_congrRel
    (patternCompute_congrRel.argRel (fun hΓ R ht => R.simAt hs hΓ _ ht)) hΓ H HA
  exact ⟨args', rhs', he, H', HR⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
