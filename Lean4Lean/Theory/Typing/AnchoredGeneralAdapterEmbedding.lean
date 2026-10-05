import Lean4Lean.Theory.Typing.AnchoredGeneralAdapters

/-! The existing finite adapter programs embed structurally in the hereditary
code-capable grammar. Actual guards and key admissions are unchanged. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

mutual
noncomputable def AtomAdapter.toGeneral {a b : Atom n}
    (adapter : AtomAdapter env U registry Γ a b) : GeneralAtomAdapter env U registry Γ a b :=
  match n, a, b, adapter with
  | _, _, _, .refl atom => .refl atom
  | _ + 1, _, _, .fn keys result => .fn keys.toGeneral result.toGeneral
  | _ + 1, _, _, .pad child => .pad child.toGeneral
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileAdapter.toGeneral {p q : Profile n}
    (adapter : ProfileAdapter env U registry Γ p q) : GeneralProfileAdapter env U registry Γ p q :=
  match adapter with
  | .nil source => .nil source
  | .cons member head tail => .cons member head.toGeneral tail.toGeneral
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def KeyProgram.toGeneral {a b : Key n}
    (program : KeyProgram env U registry Γ a b) : GeneralKeyProgram env U registry Γ a b :=
  match program with
  | .refl key => .refl key
  | .input seed arguments => .input seed arguments.toGeneral
  | .reanchor admitted => .reanchor admitted
  | .domainRekey path typed formed bridge => .domainRekey path typed formed bridge
  | .comp first second => .comp first.toGeneral second.toGeneral
termination_by (3 * n + 2, sizeOf program)
decreasing_by all_goals simp_wf; omega
end

end Lean4Lean.AnchoredSemantics
