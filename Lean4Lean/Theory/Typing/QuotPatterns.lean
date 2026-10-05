import Lean4Lean.Theory.Typing.DefinitionHeadExclusivity
import Lean4Lean.Theory.Typing.PatternIotaLemmas

/-! The concrete primitive quotient iota pattern. Parameter guards compare
actual captured terms; the source-universe guard leaves proof-source
computation to the closed quotient prefix program. -/

namespace Lean4Lean.VEnv

abbrev quotPattern : Pattern := (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern

def quotPatternRHS : quotPattern.RHS :=
  .app (.var (.inl (some none))) (.var (.inr none))

def quotPatternCheck : quotPattern.Check :=
  .nonzero (.param 0)
    (.defeq (.var (.inl (some (some (some (some none))))))
      (.var (.inr (some (some none))))
      (.defeq (.var (.inl (some (some (some none)))))
        (.var (.inr (some none))) .true))

inductive QuotPattern (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop where
  | intro : QuotRegistered env → QuotPattern env quotPattern (quotPatternRHS, quotPatternCheck)

namespace QuotPattern

theorem simple (H : QuotPattern env p rhs) : ∃ s : SimplePattern, p = s.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : QuotPattern env p rhs) : NativePatternOrigin env p := by
  cases H with
  | intro hr => exact ⟨quotDefEq, ``Quot.lift, [.param 0, .param 1], hr.equation, rfl, rfl⟩

theorem shape (H : QuotPattern env p rhs) : p = quotPattern := by cases H; rfl

theorem registered (H : QuotPattern env
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, rhs.2 = .nonzero (.param 0) rest := by
  have he : (SimplePattern.iota recursor major ctor fields).toPattern = quotPattern := H.shape
  have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter quotPattern =
      some quotPattern := by rw [he]; exact Pattern.inter_self _
  simp only [quotPattern, SimplePattern.toPattern, Pattern.inter, bind,
    Option.bind_eq_some_iff] at hi
  obtain ⟨left, hl, right, hr, _⟩ := hi
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hl
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hr
  cases H with
  | intro hr => exact ⟨hr, rfl, rfl, rfl, rfl, _, rfl⟩

theorem unique (H : QuotPattern env p rhs) (H' : QuotPattern env q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H
  cases H'
  obtain ⟨he, _⟩ := SimplePattern.iota_overlap (by intros; rfl) (by decide) hs hi
  exact ⟨rfl, he.symm, HEq.rfl⟩

theorem app_l (H : QuotPattern env p rhs) (hs : Subpattern (.app fn arg) p) :
    ¬Subpattern (.app left right) fn := by
  cases H
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  exact Subpattern.constVarN_noapp

theorem app_l_uniq (H : QuotPattern env p rhs) (H' : QuotPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_l_uniq (by intros; rfl) hb

theorem app_uniq (H : QuotPattern env p rhs) (H' : QuotPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_uniq (by decide) hl hr

end QuotPattern

theorem QuotRegistered.definition_names (henv : env.WF) (H : QuotRegistered env)
    (hd : DefinitionRegistered env value) : value.name ≠ ``Quot.lift ∧ value.name ≠ ``Quot.mk := by
  have hm : quotDefEq.HasConstructorMajor ``Quot.mk :=
    ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
  constructor
  · intro hn
    exact hd.not_constructor_equation henv H.equation (by rw [hn]; rfl) hm
  · intro hn
    apply henv.native_constructor_rigid H.equation hm value.toDefEq hd.2 (VLevel.params value.uvars)
    change VExpr.const value.name _ = VExpr.const ``Quot.mk _
    rw [hn]

def DefinitionQuotPattern (env : VEnv) (registry : Name → Option VDefVal)
    (p : Pattern) (rhs : p.RHS × p.Check) : Prop :=
  DefinitionPattern registry p rhs ∨ QuotPattern env p rhs

namespace DefinitionQuotPattern

theorem simple (H : DefinitionQuotPattern env registry p rhs) :
    ∃ s : SimplePattern, p = s.toPattern := H.elim DefinitionPattern.simple QuotPattern.simple

theorem origin
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionQuotPattern env registry p rhs) : NativePatternOrigin env p :=
  H.elim (DefinitionPattern.origin hregistry) QuotPattern.origin

theorem unique (henv : env.WF)
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionQuotPattern env registry p rhs) (H' : DefinitionQuotPattern env registry q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  rcases H with H | H <;> rcases H' with H' | H'
  · exact H.unique H' hs hi
  · cases H
    cases H'
    cases hs
    contradiction
  · cases H with
    | intro hr =>
      cases H' with
      | @intro value hl hc =>
        cases sub <;> try contradiction
        rename_i name
        simp only [Pattern.inter, Option.ite_none_right_eq_some, Option.some.injEq] at hi
        have hn := hs.iota_const
        have hd := hr.definition_names henv (hregistry _ _ hl)
        exact (hn.elim (fun he => hd.1 (hi.1.trans he))
          (fun he => hd.2 (hi.1.trans he))).elim
  · exact H.unique H' hs hi

theorem app_l (H : DefinitionQuotPattern env registry p rhs) (hs : Subpattern (.app fn arg) p) :
    ¬Subpattern (.app left right) fn := by
  rcases H with H | H
  · exact (H.no_app_subpattern hs).elim
  · exact H.app_l hs

theorem app_l_uniq (H : DefinitionQuotPattern env registry p rhs)
    (H' : DefinitionQuotPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  rcases H with H | H
  · exact (H.no_app_subpattern hs).elim
  rcases H' with H' | H'
  · exact (H'.no_app_subpattern hs').elim
  exact H.app_l_uniq H' hs hs' hb

theorem app_uniq (H : DefinitionQuotPattern env registry p rhs)
    (H' : DefinitionQuotPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  rcases H with H | H
  · exact (H.no_app_subpattern hs).elim
  rcases H' with H' | H'
  · exact (H'.no_app_subpattern hs').elim
  exact H.app_uniq H' hs hs' hl hr

end DefinitionQuotPattern
theorem QuotPattern.equation_trace (hr : QuotRegistered env) (hn : ¬ u ≈ .zero) :
    NativeReductionTrace env U (QuotPattern env) Γ
      (quotDefEq.lhs.instL [u,v]) (quotDefEq.rhs.instL [u,v]) := by
  apply NativeReductionTrace.lam
  apply NativeReductionTrace.lam
  apply NativeReductionTrace.lam
  apply NativeReductionTrace.lam
  apply NativeReductionTrace.lam
  apply NativeReductionTrace.lam
  refine .native (QuotPattern.intro hr)
    (.app (.var (.var (.var (.var (.var .const))))) (.var (.var (.var .const)))) ?_
  exact ⟨hn, ⟨_, HasType.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))⟩,
    ⟨_, HasType.bvar (.succ (.succ (.succ (.succ .zero))))⟩, trivial⟩

end Lean4Lean.VEnv
