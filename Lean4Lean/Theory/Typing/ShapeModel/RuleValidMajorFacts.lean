import Lean4Lean.Theory.Typing.ShapeModel.RuleValidNativeSlot

/-!
# Semantic facts about the constructors and families of rules recorded along a history

For a constructor recorded in the tables `T` of an earlier point of the history of a well-formed
environment (whose families all have semantic headers), the constructor has its signature data,
its family has a semantic header, and every structure registered for the constructor has its
semantic type facts (`major_facts`). A recorded family is neither a constructor nor the head of a
rule (`fam_facts`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem major_facts (H : env.WF) {T : Tables} {E : VEnv} (hT : T.Inv E)
    (hext : T.Extends (envTables env))
    (hfam : ∀ I d, T.fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    {c : Name} {k : CtorData} (hc : T.ctor c = some k) :
    letI := envSig env
    ∃ ci d, sigCtor env c = some ci ∧ ci.family = k.family ∧ famOf env ci.family = some d ∧
      FamSem env ci.family d.resultLevel (d.nparams + d.nindices) ∧
      ∀ {s info}, env.projections s info → info.ctorName = c → FamTypeSem env s info := by
  letI := envSig env
  have hctorOf : ctorOf env c = some k := hext.ctor hc
  obtain ⟨d, hd, -⟩ := (hT.views.ctor hc).2
  have hfamd : famOf env k.family = some d := hext.fam hd
  have hci := sigCtor_of_shape (c := c) (.inl (by rw [hctorOf]; simp)) (ctorOf_shape' H hctorOf)
  refine ⟨_, d, hci, rfl, hfamd, hfam _ _ hd, fun {s info} hp hcn => ?_⟩
  have h1 := ctorOf_projection H hp
  rw [hcn, hctorOf] at h1
  cases h1
  have h2 := famOf_projection H hp
  rw [hfamd] at h2
  cases h2
  exact famTypeSem_of_famSem H hp (hfam _ _ hd)

theorem fam_facts (H : env.WF) {F : Name} {d : FamData} (h : famOf env F = some d) :
    sigCtor env F = none ∧ ∀ r, EnvRule env r → r.head ≠ .const F := by
  have hne : (envTables env).fam F ≠ none := by
    change famOf env F ≠ none; rw [h]; simp
  have hct : ctorOf env F = none := (envTables_inv H).views.fam_ctor hne
  refine ⟨?_, fun r hr => EnvRule.head_not_rigid H ((envTables_inv H).views.rigid (.inl hne)) hr⟩
  unfold sigCtor
  rw [if_neg]
  rintro (h' | ⟨-, h'⟩)
  · exact h' hct
  · rw [h] at h'; cases h'

end

end Lean4Lean.ShapeModel
