module

public meta import LeanScript.ToTerm.TransRec
public meta import LeanScript.ToTerm.Brec

@[expose] public section

meta section

/-!
# The translation: structural recursion

`transBrecOn`, the clause of the translation for a structural recursion as Lean compiled
it.  Like the clauses of `LeanScript.ToTerm.TransRec`, it takes the translation itself as
its first argument `trans`.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The array whose elements an expression lists: `a` for `Array.toList a` (or the
    projection it unfolds to). -/
def arrayOfToList? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .proj ``Array 0 a => some a
  | e' =>
      match e'.getAppFnArgs with
      | (``Array.toList, #[_, a]) => some a
      | _ => none

/-- A structural recursion on a list, run on the **elements of an array**:
    `List.brecOn a.toList F`, which is what `go a.toList` unfolds to when `go` is a
    structurally recursive function on lists.  That is the fold of the array,
    `LeanScript.Term.array_rec' k`.

    The depth `k` is found as for a `Nat`: the branch is instantiated at the list
    `hd :: y₁ :: … :: yₖ :: rest`, with the `k + 1` nearest entries of the history — the
    values at `y₁ :: … :: rest`, …, `rest` — replaced by variables, and the smallest `k`
    at which nothing of the history and of `rest` is left is the depth.  The branch of
    `array_rec` is given the head, the tail as an array and the fold values; an element
    `yᵢ` past the head that the branch reads is taken off the tail by `i` nested
    `array_casesOn`s (whose empty cases are never taken there: the tail has at least `k`
    elements).  A branch that reads the rest of the list after them is refused.

    The lists of at most `k` elements are the base answers (`LeanScript.ArrayRecBases`):
    the branch at `[x₁, …, xⱼ]`, each one reading the answers at its own suffixes. -/
def transArrayBrecOn (trans : TransFn) (c : TCtx) (τLean τ α brecF : Expr)
    (historyTy : Expr → MetaM Expr) (arr : Expr) : MetaM Expr := do
  let u ← getDecLevel α
  let listTy := mkApp (mkConst ``List [u]) α
  let consE (hd tl : Expr) : Expr := mkApp3 (mkConst ``List.cons [u]) α hd tl
  let nilE := mkApp (mkConst ``List.nil [u]) α
  let listOf (xs : Array Expr) (tail : Expr) : Expr := xs.foldr consE tail
  let σ ← tyOfType α
  let arrTy ← tyOfType (mkApp (mkConst ``Array [u]) α)
  -- the branch at a concrete list, the history read as `ihs` (nearest first)
  let valueAt (l : Expr) (ihs : Array Expr) : MetaM Expr := do
    let ht ← historyTy l
    withLocalDeclD `history ht fun hist => do
      let body ← reduceBranchMatches =<< reduceBrecBodyDeep (mkApp2 brecF l hist)
      let body := substHistory body hist.fvarId! ihs
      if body.containsFVar hist.fvarId! then
        throwError "`#leanscript_to_term`: this recursion on the elements of an array \
          reads the value of the function at a list that is not one of the suffixes the \
          fold has computed"
      pure body
  -- the branch at `hd :: y₁ :: … :: yₖ :: rest`, translated in the context of `array_rec`
  let stepAt (k : Nat) : MetaM Expr :=
    withLocalDeclD `head α fun hd => do
      let yDecls : Array (Name × (Array Expr → MetaM Expr)) :=
        (Array.range k).map fun i => (Name.mkSimple s!"y{i + 1}", fun _ => pure α)
      withLocalDeclsD yDecls fun ys =>
        withLocalDeclD `rest listTy fun rest => do
          let ihDecls : Array (Name × (Array Expr → MetaM Expr)) :=
            (Array.range (k + 1)).map fun i =>
              (Name.mkSimple s!"ih{i}", fun _ => pure τLean)
          withLocalDeclsD ihDecls fun ihs => do
            let body ← valueAt (consE hd (listOf ys rest)) ihs
            if body.containsFVar rest.fvarId! then
              throwError "`#leanscript_to_term`: at depth {k} the branch still reads the \
                rest of the list"
            -- the elements `y₁ … yₘ` past the head that the branch reads, `m ≤ k`
            let m := (ys.toList.zipIdx.filterMap fun (y, i) =>
              if body.containsFVar y.fvarId! then some (i + 1) else none).foldl max 0
            let arrLean := mkApp (mkConst ``Array [u]) α
            withLocalDeclD `tail arrLean fun tl => do
              let c' := c.pushFields
                (#[(hd.fvarId!, σ), (tl.fvarId!, arrTy)] ++ ihs.map fun ih => (ih.fvarId!, τ))
              -- the tails `tail₁ … tailₘ` that the dispatches on the tail bind
              let tDecls : Array (Name × (Array Expr → MetaM Expr)) :=
                (Array.range m).map fun i => (Name.mkSimple s!"tail{i + 1}", fun _ => pure arrLean)
              withLocalDeclsD tDecls fun tls => do
                -- the contexts of the nested dispatches: `cs[i]` binds `y₁ … yᵢ`
                let mut cs : Array TCtx := #[c']
                for i in [0:m] do
                  cs := cs.push ((cs.getD i c').pushFields
                    #[(ys[i]!.fvarId!, σ), (tls[i]!.fvarId!, arrTy)])
                let tailAt (i : Nat) : Expr := if i == 0 then tl else tls[i - 1]!
                let mut acc ← trans (cs.getD m c') body
                for r in [0:m] do
                  let i := m - 1 - r
                  -- the tail has at least `k` elements at this branch, so its empty case
                  -- is never taken: it answers the value at the tail, which is at hand
                  let scrut ← trans (cs.getD i c') (tailAt i)
                  let dead ← trans (cs.getD i c') ihs[0]!
                  acc := mkAppN (mkConst `LeanScript.Term.array_casesOn')
                    #[c.sg, (cs.getD i c').gamma, σ, τ, scrut, dead, acc]
                pure acc
  let mut found : Option (Nat × Expr) := none
  let maxK ← maxNatRecDepth
  for k in [0:maxK + 1] do
    if found.isNone then
      found ← try pure (some (k, ← stepAt k)) catch _ => pure none
  let some (k, branch) := found
    | throwError "`#leanscript_to_term`: this recursion on the elements of an array is not \
        the fold of an array at any depth up to {maxK} (the option \
        `leanscript.toTerm.maxNatRecDepth`) — the fold `array_rec k` gives its branch the \
        head, the tail and the values at the `k + 1` nearest suffixes of the tail, and the \
        branch may read the first `k` elements of the tail, so a branch that reads the rest \
        of the list after them, or the value at a list that is not a suffix, has no term"
  -- the answers for the lists of at most `k` elements, `[x₁, …, xⱼ]`, `x₁` bound first
  let xDecls : Array (Name × (Array Expr → MetaM Expr)) :=
    (Array.range k).map fun i => (Name.mkSimple s!"x{i + 1}", fun _ => pure α)
  let bases ← withLocalDeclsD xDecls fun xs => do
    let mut levels : Array (Expr × Expr) := #[]
    let mut cj := c
    for j in [0:k + 1] do
      if j > 0 then cj := cj.push xs[j - 1]!.fvarId! σ
      let elems := xs.extract 0 j
      -- the values at the suffixes, the shortest first
      let mut vals : Array Expr := #[]
      for i in [0:j + 1] do
        let start := j - i
        let v ← valueAt (listOf (elems.extract start j) nilE) vals.reverse
        vals := vals.push v
      let t ← trans cj vals.back!
      levels := levels.push (cj.gamma, t)
    let (gk, tk) := levels[k]!
    let mut acc := mkAppN (mkConst `LeanScript.ArrayRecBases.nil) #[c.sg, gk, σ, τ, tk]
    for i in [0:k] do
      let j := k - 1 - i
      let (gj, tj) := levels[j]!
      acc := mkAppN (mkConst `LeanScript.ArrayRecBases.cons)
        #[c.sg, gj, σ, τ, mkNatLit (k - 1 - j), tj, acc]
    pure acc
  let scrutT ← trans c arr
  return mkAppN (mkConst `LeanScript.Term.array_rec')
    #[c.sg, c.gamma, σ, τ, mkNatLit k, scrutT, bases, branch]

/-- A structural recursion as Lean compiled it: `Nat.brecOn` or `List.brecOn`.

    The branch of a `brecOn` is given the **history** of the recursion — the value of the
    function at every smaller argument — and the grammar's folds give it the value at the
    immediate predecessor only.  So the history is reduced away here: the branch is
    instantiated at the two constructors of its type, with the head of the history
    replaced by a variable standing for the value at the predecessor, and what is left is
    the pair of branches of `Nat.rec` / `List.rec`, which
    `LeanScript.ToTerm.transRecCore` turns into `nat_rec` / `recTaggedUnion_rec` (or the
    case analysis, when the branch does not use that value).

    On a `Nat` the depth is not fixed at one.  If the branch at `n + 1` reads more of the
    history than its head, the depths `1, 2, …` are tried in turn: at depth `k` the
    branch is instantiated at `n + k + 1` with the `k + 1` nearest entries of the history
    replaced by variables, and the first depth at which nothing of the history is left is
    the depth of the `nat_rec` that is built — with the answers below it, the branch at
    `0, …, k`, as its base values.  A recursion that reads the history at an argument
    that is not a fixed number of steps back is refused. -/
def transBrecOn (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let isNat := n == ``Nat.brecOn
  let mIdx := if isNat then 0 else 1
  let arity := mIdx + 3
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[mIdx]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  let major := args[mIdx + 1]!
  let brecF := args[mIdx + 2]!
  -- the motive may depend on the argument (`Vec α n` for a recursion building a vector
  -- of length `n`), provided the language's type of the answers does not: it is the same
  -- type at every argument.  `τLeanAt t` is the Lean type of the answer at `t`.
  let (τLean, τ, dependent) ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    let dependent := body.containsFVar xs[0]!.fvarId!
    let depErr : MetaM Unit := throwError "`#leanscript_to_term`: {n} is used with a \
      dependent motive, which the language has no eliminator for"
    let τ ← try instantiateMVars (← tyOfType body)
      catch ex => do if dependent then depErr
                     throw ex
    if τ.containsFVar xs[0]!.fvarId! then depErr
    return (body, τ, dependent)
  let τLeanAt (t : Expr) : MetaM Expr :=
    if dependent then whnf (motive.beta #[t]) else pure τLean
  let brecFTy ← inferType brecF
  -- the type of the history at a given argument
  let historyTy (t : Expr) : MetaM Expr := do
    return (← whnf (← instantiateForall brecFTy #[t])).bindingDomain!
  -- the branch at a constructor, with the head of the history read as `ih`
  let branchAt (scrutinee : Expr) (ih? : Option Expr) : MetaM Expr := do
    let ht ← historyTy scrutinee
    withLocalDeclD `history ht fun hist => do
      let body ← reduceBranchMatches =<< reduceBrecBodyDeep (mkApp2 brecF scrutinee hist)
      let body := match ih? with
        | some ih => substHistoryHead body hist.fvarId! ih
        | none => body
      if body.containsFVar hist.fvarId! then
        throwError "`#leanscript_to_term`: this recursion reads the value of the \
          function at an argument that is not the immediate predecessor, and the \
          grammar's folds descend one step at a time"
      return body
  -- what to do with the arguments a saturated `brecOn` is applied to on top of its own
  let finish (core : Expr) : MetaM Expr := do
    let extra := args.extract arity args.size
    if extra.isEmpty then return core
    applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra
  if isNat then
    -- one step first: that is `Nat.rec`, and `transRecCore` may still turn it into the
    -- case analysis when the branch does not use the value of the fold
    let depth0? : Option (Array Expr) ←
      try
        let z ← branchAt (mkConst ``Nat.zero) none
        let s ← withLocalDeclD `n (mkConst ``Nat) fun nv => do
          withLocalDeclD `ih (← τLeanAt nv) fun ih => do
            let body ← branchAt (mkApp (mkConst ``Nat.succ) nv) (some ih)
            mkLambdaFVars #[nv, ih] body
        pure (some #[z, s])
      catch _ => pure none
    if let some minors := depth0? then
      let some (.recInfo ri) := (← getEnv).find? ``Nat.rec
        | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
      return ← finish (← transRecCore trans c ri τ minors major)
    -- more than one step: the branch at `n + k + 1`, with the `k + 1` nearest answers
    -- read out of the history and bound as `ih₀, …, ihₖ` — nearest first
    let stepAt (k : Nat) : MetaM Expr :=
      withLocalDeclD `n (mkConst ``Nat) fun nv => do
        let mut scrutE := nv
        for _ in [0:k + 1] do scrutE := mkApp (mkConst ``Nat.succ) scrutE
        -- `ihᵢ` is the answer at `n + k - i`
        let ihDecls : Array (Name × (Array Expr → MetaM Expr)) :=
          (Array.range (k + 1)).map fun i =>
            (Name.mkSimple s!"ih{i}", fun _ => do
              let mut t := nv
              for _ in [0:k - i] do t := mkApp (mkConst ``Nat.succ) t
              τLeanAt t)
        withLocalDeclsD ihDecls fun ihs => do
          let ht ← historyTy scrutE
          withLocalDeclD `history ht fun hist => do
            let body ← reduceBranchMatches =<< reduceBrecBodyDeep (mkApp2 brecF scrutE hist)
            let body := substHistory body hist.fvarId! ihs
            if body.containsFVar hist.fvarId! then
              throwError "`#leanscript_to_term`: this recursion reads the value of the \
                function at an argument that is not one of its {k + 1} nearest \
                predecessors"
            mkLambdaFVars (#[nv] ++ ihs) body
    let mut found : Option (Nat × Expr) := none
    let maxK ← maxNatRecDepth
    for k in [1:maxK + 1] do
      if found.isNone then
        found ← try pure (some (k, ← stepAt k)) catch _ => pure none
    let some (k, s) := found
      | throwError "`#leanscript_to_term`: this recursion does not descend by a fixed \
          number of steps, at most {maxK} (the option `leanscript.toTerm.maxNatRecDepth`) \
          — the fold of a natural number the grammar has gives its branch \
          the answers at the `k + 1` nearest predecessors, so a call at an argument such \
          as `n / 2` has no term"
    -- the answers below the depth: the branch at `0, …, k`, each one allowed to read the
    -- answers already known
    let mut baseVals : Array Expr := #[]
    for j in [0:k + 1] do
      let mut jE : Expr := mkConst ``Nat.zero
      for _ in [0:j] do jE := mkApp (mkConst ``Nat.succ) jE
      let ht ← historyTy jE
      let v ← withLocalDeclD `history ht fun hist => do
        let body ← reduceBranchMatches =<< reduceBrecBodyDeep (mkApp2 brecF jE hist)
        let body := substHistory body hist.fvarId! baseVals.reverse
        if body.containsFVar hist.fvarId! then
          throwError "`#leanscript_to_term`: the answer at {j} reads the value of the \
            function at an argument the fold has not computed yet"
        pure body
      baseVals := baseVals.push v
    let scrutT ← trans c major
    let natTy ← tyOfType (mkConst ``Nat)
    -- the base values are written nearest first: `(f k, …, f 1, f 0)`
    let baseTerms ← baseVals.reverse.mapM fun v => trans c v
    let base := mkNatRecBase c τ baseTerms
    let core ← lambdaBoundedTelescope s (k + 2) fun xs body => do
      let c' := c.pushFields
        (#[(xs[0]!.fvarId!, natTy)] ++ (xs.extract 1 xs.size).map fun x => (x.fvarId!, τ))
      return mkAppN (mkConst `LeanScript.Term.nat_rec')
        #[c.sg, c.gamma, τ, mkNatLit k, scrutT, base, ← trans c' body]
    return ← finish core
  -- a recursion on the elements of an array, `go a.toList`: the fold of the array
  if let some arr := arrayOfToList? major then
    if dependent then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    return ← finish (← transArrayBrecOn trans c τLean τ args[0]! brecF historyTy arr)
  let minors ←
    do
      let α := args[0]!
      let listTy := mkApp (mkConst ``List [← getDecLevel α]) α
      let nil := mkApp (mkConst ``List.nil [← getDecLevel α]) α
      let z ← branchAt nil none
      let s ← withLocalDeclD `head α fun hd =>
        withLocalDeclD `tail listTy fun tl => do
          withLocalDeclD `ih (← τLeanAt tl) fun ih => do
            let cons := mkApp3 (mkConst ``List.cons [← getDecLevel α]) α hd tl
            let body ← branchAt cons (some ih)
            mkLambdaFVars #[hd, tl, ih] body
      pure #[z, s]
  let some (.recInfo ri) := (← getEnv).find? ``List.rec
    | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
  finish (← transRecCore trans c ri τ minors major)

end LeanScript.ToTerm

end

end
