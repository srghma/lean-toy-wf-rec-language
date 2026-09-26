import RequestProject.WFLang.PCL.Lang.Simp

/-!
# Language `PCL`: well-founded recursion as a construct of the grammar (proof-carrying calls)

The language is split into the files of `PCL/Lang/` (each importing the previous one):

* `Syntax`: global functions, join points and the statements `Expr` (the grammar, with its
  overview);
* `Eval`: the evaluator `Expr.eval` (the reference semantics), and the soundness of recursive
  join points (`joinFn`);
* `Machine`: the jump machine `Expr.evalS`, which runs loops and tail calls without using stack,
  its proof of agreement with `Expr.eval`, and the `@[csimp]` lemma that makes compiled code
  (and `#eval`) run it;
* `Fix`: global functions (`fixFn`), their soundness, and `fixS`, which runs them with the
  machine (`@[csimp]`);
* `While`: well-founded `while` loops, a derived form (`Expr.whileLoop`);
* `Program`: the global context, programs (`PTerm`, `Term`, `Term.eval`) and tuples;
* `Simp`: the simplification lemmas used by the capture tactics.
-/
