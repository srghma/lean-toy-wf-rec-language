import RequestProject.WFLang.Capture.Meta.Agree

/-!
# Reading a well-founded Lean function (metaprogramming for the capture)

* reading a Lean function: its signature (`signatureOf`), the right-hand side of its unfolding
  equation (`withEqnRhs`), the `WellFounded.fix` Lean used to define it (`findFixIn`), the
  decreasing proofs at its recursive call sites (`callSiteProofs`), and the pull-back of its
  well-founded relation to environments (`pullBackRel`, `closedRel`, `closedFixOf`);
* calls to other user functions: the attribute `@[inlinable]`; non-recursive `@[inlinable]`
  functions are inlined (`inlineCalls`), recursive `@[inlinable]` ones are reported
  (`recCallees`) so that the capture turns them into loops at the call site (if they are
  tail-recursive) or global functions, and the other ones are collected as global functions of
  the program (`collectGlobals`);
  calls whose arguments are all known are evaluated first (`foldCall?`, `wfFoldCalls`);
* the skeleton of the agreement tactic (`agreeTarget`, `agreeRec`, `rewriteCalleesWith`) and the
  tactics `wf_dec` (one decrease obligation) and `wf_close` (the goals left after unfolding).

The implementation is split into the files of `Capture/Meta/` (each importing the previous one):
`Signature`, `Fix`, `Calls`, `Callees`, `WFRel`, `Mutual`, `Tactics`, `Agree`.
-/
