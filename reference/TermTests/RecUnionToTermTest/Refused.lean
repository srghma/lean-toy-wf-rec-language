module

public import TermTests.RecUnionToTermTest.K0
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k`: what the translation refuses

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.

A deeper look may go into a subvalue at the node the branch stands at
(`LeanScript.FoldKBranch.deep`) or into one at a node above it on the path
(`LeanScript.FoldKBranch.deepOuter`), so a structural recursion that reads below several
subvalues at once — the sum of the labels at even levels, which reads the answers at the
grandchildren below **both** children — is a fold too, of depth `2`
(`TermTests/RecUnionToTermTest/BothSubtrees.lean`).  What is refused is a recursion that
needs more looks than the translation searches for (the option
`leanscript.toTerm.maxRecUnionRecDepth`, `16` by default; lowered to `6` below). -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## Refused: deeper than the translation looks

The answer at a node reads the answer eight levels down its left spine, which takes seven
looks: that is a `recTaggedUnion_rec 7`, one more than the translation tries once the bound
is lowered to `6`.  (With the default bound it translates:
`TermTests/StructRecTest/DeepFolds.lean`.) -/

def leftEighth : Tree → Nat
  | .node (.node (.node (.node (.node (.node (.node (.node a _ _) _ _) _ _) _ _) _ _) _ _)
      _ _) v _ => v + leftEighth a
  | _ => 0

set_option leanscript.toTerm.maxRecUnionRecDepth 6 in
example : Term sigAdd [] (treeT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term leftEighth
  exact treeSum_with_k0_term

end TermTests.RecUnionToTerm

end
