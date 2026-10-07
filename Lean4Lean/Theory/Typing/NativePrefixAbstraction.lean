import Lean4Lean.Theory.Typing.NativePrefixEta
import Lean4Lean.Theory.Typing.NativePrefixStrengthening

/-! Typed abstraction of an opened native prefix. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.NativeRecursorData

theorem HasType.nativeSupply (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ fn type) (H : VExpr.WF env U Γ (mkApps fn args))
    (hg : supplyType args type = some residual) :
    env.HasType U Γ (mkApps fn args) residual := by
  induction args generalizing fn type with
  | nil => cases hg; exact hf
  | cons arg args ih =>
    cases type <;> try contradiction
    rename_i domain body
    have hfa : VExpr.WF env U Γ (.app fn arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app fn arg) H
    obtain ⟨domain', body', hf', ha⟩ := hfa.app_inv henv.ordered hΓ
    obtain ⟨⟨_, hdom⟩, _, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
    have harg := ha.defeqU_r henv hΓ ⟨_, hdom.symm⟩
    exact ih (hf.app harg) H hg

theorem native_takeForalls_sound
    (H : NativeRecursorData.takeForalls count type = some (domains, result)) :
    type = wrapForalls domains result := by
  induction count generalizing type domains result with
  | zero => cases H; rfl
  | succ count ih =>
    cases type <;> try contradiction
    simp only [NativeRecursorData.takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, ht, he⟩ := H
    cases he
    exact congrArg (VExpr.forallE _) (ih ht)

/-- Successful native generation determines the actual type of any
well-formed occurrence of that registered recursor prefix. -/
theorem NativeRecursorRegistered.prefixType {data : NativeRecursorData}
    {levels : List VLevel} {program : PrefixProgram}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : NativeRecursorRegistered env data)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hg : data.singletonProgram env U levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const data.name levels) args)) :
    env.HasType U Γ (mkApps (.const data.name levels) args) program.type := by
  unfold singletonProgram at hg
  dsimp only at hg
  split at hg <;> try contradiction
  rename_i hguard
  simp at hguard
  have hlen : levels.length = data.uvars := hguard.1
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨nativeType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, _, equation, _, body, _, hg⟩ := hg
  split at hg <;> try contradiction
  cases hg
  have hf : env.HasType U Γ (.const data.name levels) (nativeType.instL levels) :=
    .const (H.recursorType htype) hlevels hlen
  have hh := hf.nativeSupply henv hΓ ht hsupply
  rw [native_takeForalls_sound htake] at hh
  exact hh

/-- Abstract a fresh final supplied argument back into the native program.
The generated binder domain is retained and is typed-equal to the caller's
binder domain; no literal equality of arbitrary typing witnesses is used. -/
theorem NativeDeltaRule.abstract {name : Name} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hfn : env.HasType U Γ (mkApps (.const name levels) args) (.forallE A B))
    (H : NativeDeltaRule env U registry (A :: Γ) name levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) rhs) :
    ∃ domain, (∃ u, env.IsDefEq U Γ A domain (.sort u)) ∧
      NativeDeltaRule env U registry Γ name levels args (.lam domain rhs) := by
  cases H with
  | @intro data late hl hr hn ht hw hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold singletonProgram at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    obtain ⟨domain, hearly⟩ := singletonProgram_open_inv htype (hr.recursorType_closed henv htype) hg
    have hsource := hr.prefixType henv hΓ hw hearly
      (by simpa only [hn] using (show VExpr.WF env U Γ _ from ⟨_, hfn⟩))
    simp only [hn] at hsource
    have hsource' : env.HasType U Γ (mkApps (.const name levels) args)
        (.forallE domain late.type) := hsource
    obtain ⟨⟨u, hd⟩, _, _⟩ := (hfn.uniqU henv hΓ hsource').forallE_inv henv hΓ
    have replay' := replay.defeqDFC henv hΓ (IsDefEqCtx.succ .zero hd)
    have hsame : late.domains.reverse ++ domain :: Γ =
        (domain :: late.domains).reverse ++ Γ := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    have hnew : NativePrefixReplay env U Γ (mkApps (.const name levels) args)
        { late with domains := domain :: late.domains } := by
      refine {
        source_typed := hsource
        remaining_nonempty := List.cons_ne_nil _ _
        equation_present := replay'.equation_present
        equation_body := replay'.equation_body
        levels_wf := replay'.levels_wf
        levels_length := replay'.levels_length
        captures_length := replay'.captures_length
        captures_typed := ?_
        major_prop := ?_
        native_lhs := ?_ }
      · intro j hj hd
        simpa only [hsame] using replay'.captures_typed j hj hd
      · simpa only [hsame] using replay'.major_prop
      · have hpos : 0 < late.domains.length := List.length_pos_iff.mpr replay.remaining_nonempty
        have he : late.domains.length = (late.domains.length - 1) + 1 := by omega
        have hbody : nativeEtaBody late.domains.length (mkApps (.const name levels) args) =
            nativeEtaBody (late.domains.length - 1)
              (mkApps (.const name levels) (args.map VExpr.lift ++ [VExpr.bvar 0])) := by
          conv => lhs; rw [he]
          change nativeEtaBody (late.domains.length - 1)
            ((mkApps (.const name levels) args).lift.app (.bvar 0)) = _
          congr 1
          rw [mkApps_append]
          change (VExpr.liftN 1 (mkApps (.const name levels) args) 0).app (.bvar 0) = _
          rw [liftN_mkApps]
          rfl
        simpa only [List.length_cons, Nat.add_sub_cancel, hsame, ← hbody] using replay'.native_lhs
    exact ⟨domain, ⟨u, hd⟩, .intro hl hr hn ht hw hz hearly hnew⟩

end Lean4Lean.VEnv
