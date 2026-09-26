module

public import LeanScript.Expr.Build
public import LeanScript.Eval
public import TermTests.FamilyRecDepthTest
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# Folds over a mutual family: crossing members, and the other two member shapes

`TermTests/FamilyRecDepthTest.lean` writes the `fib` suite — the `n + 2` recursion, the
tail-recursive loop, the pair recursion, the tribonacci … hexanacci numbers and the
continuant — as folds over a mutual family at depths zero to five.  Every family there is
made of members with **constructors**, and every deeper look stays inside the member it
started in, because the two members of that family do not mention each other.

This file is the other half of the exercise, and its terms are checked the same way — by
their types, and by running them against the Lean references (§3):

* §1 folds over a family whose two members are defined **in terms of each other**, so
  every deeper look crosses from one member to the other;
* §2 folds over a family with all three member shapes — a **record** member, a member with
  **constructors** and a **newtype** member — written in a scope of three members, where
  both recursive members descend and the newtype member answers.

The reference Lean programs are checked here too, as they are there.
-/

namespace TermTests.FamilyRecDepthMembers

open LeanScript

open TermTests.FamilyRecDepth (natT sigAdd addT)

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 1. A deeper look into the **other** member

The family of `TermTests/FamilyRecDepthTest.lean` is a `mutual` block whose members do not
mention each other, so every descent there stays inside the member it started in.  A family whose members are defined *in
terms of each other* makes a deeper look cross from one to the other:

```lean
mutual
inductive Ev where
  | zero
  | succ (o : Od)
inductive Od where
  | zero
  | succ (e : Ev)
end
```

A value of either is a chain of `succ`s, alternating between the two members, and `fib` of
the chain's length is the `fib` of the request again — read one member at a time:

```lean
mutual
def Ev.fib : Ev → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ e) => Ev.fib e + Od.fib (.succ e)
def Od.fib : Od → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ o) => Od.fib o + Ev.fib (.succ o)
end
```

So the depth-one branch of `Ev.succ` descends into a field that is an occurrence of member
`1`, and the branches it is then given are **`Od`'s**. -/

mutual

/-- The first member of the alternating family. -/
inductive Ev where
  /-- The chain ends. -/
  | zero
  /-- One more link, of the other member. -/
  | succ (o : Od)

/-- The second member of the alternating family. -/
inductive Od where
  /-- The chain ends. -/
  | zero
  /-- One more link, of the other member. -/
  | succ (e : Ev)

end

deriving instance LeanScriptTyWf for Ev
deriving instance LeanScriptTyWf for Od

mutual

/-- `fib` of the length of an `Ev` chain. -/
def Ev.fib : Ev → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ e) => Ev.fib e + Od.fib (.succ e)

/-- `fib` of the length of an `Od` chain. -/
def Od.fib : Od → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ o) => Od.fib o + Ev.fib (.succ o)

end

mutual

/-- An `Ev` chain of `n` links. -/
def Ev.ofNat : Nat → Ev
  | 0 => .zero
  | n + 1 => .succ (Od.ofNat n)

/-- An `Od` chain of `n` links. -/
def Od.ofNat : Nat → Od
  | 0 => .zero
  | n + 1 => .succ (Ev.ofNat n)

end

-- [SKIPPED BY PROFILE_LAKE] #guard Ev.fib (Ev.ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard Od.fib (Od.ofNat 10) = 55

/-- Both members compute the ordinary `fib` of the chain's length. -/
theorem Ev.fib_ofNat : (n : Nat) →
    Ev.fib (Ev.ofNat n) = TermTests.FibWindow.fib n ∧
      Od.fib (Od.ofNat n) = TermTests.FibWindow.fib n
  | 0 => ⟨rfl, rfl⟩
  | 1 => ⟨rfl, rfl⟩
  | n + 2 => by
      have h0 := Ev.fib_ofNat n
      have h1 := Ev.fib_ofNat (n + 1)
      refine ⟨?_, ?_⟩
      · show Ev.fib (Ev.ofNat n) + Od.fib (Od.ofNat (n + 1)) = _
        rw [h0.1, h1.2]
        rfl
      · show Od.fib (Od.ofNat n) + Ev.fib (Ev.ofNat (n + 1)) = _
        rw [h0.2, h1.1]
        rfl

/-- Member `0` of the alternating family: `zero | succ (o : member 1)`. -/
def memEv : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 1).toTyWfIn, []⟩ []))

/-- Member `1` of the alternating family: `zero | succ (e : member 0)`. -/
def memOd : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 0).toTyWfIn, []⟩ []))

/-- The alternating family, selecting member `0`. -/
def famEv : LeanMutualRecFamily (TyWfIn 2) := .selectedThenMore [] memEv memOd []

/-- That it describes types. -/
theorem evWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famEv) := by ty_wf

/-- The type of member `0` of the alternating family. -/
def evTy : TyWf := .mutualRecursiveFamily famEv evWf

/-- How the value of a fold over the alternating family reaches a branch. -/
abbrev ebind (τ : TyWf) : List (TyWfIn 2) → List TyWf := TyWf.famRecBinders famEv evWf τ

/-- The context the fold below is written in. -/
abbrev ECtx : Ctx := [evTy]

/-- The fields of `Ev.succ`: one occurrence of member `1`. -/
abbrev evSuccFields : List (TyWfIn 2) := [(Ty.familyMember 1).toTyWfIn]

/-- The fields of `Od.succ`: one occurrence of member `0`. -/
abbrev odSuccFields : List (TyWfIn 2) := [(Ty.familyMember 0).toTyWfIn]

-- The branch of `Ev.succ` binds an `Od` and the answer at it; the branch of `Od.succ`
-- binds an `Ev` and the answer at it.  The two members have *different* types, so the
-- contexts differ, and a motive that answers for both is what makes one fold of them.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : ebind τ evSuccFields = [TyWf.famMemberTy famEv evWf 1, τ] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : ebind τ odSuccFields = [evTy, τ] := by kernel_rfl

-- It is the tree `LeanScriptTyWf` derives for the Lean `Ev`, so `Ev.fib` translates to a
-- term of this type.
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf Ev = evTy := by kernel_rfl

/-- **`fib` over a family whose members mention each other**: `Ev.fib`, translated to the
    depth-one fold.  Each member's `succ` descends into the **other** member —
    `FamilyMemberAt.there .here` from `Ev`, `FamilyMemberAt.here` from `Od` — and answers
    with the two answers it then has in hand. -/
def evFibTerm : Term sigAdd [] (evTy ⇒ natT) := #leanscript_to_term Ev.fib

/-- The branches of `fib` over the alternating family, read back out of `evFibTerm`. -/
def evFibCases :
    FamilyFoldKCases sigAdd 0 famEv.members (ebind natT) ECtx natT famEv.members 1 :=
  #leanscript_fold_branch evFibTerm

/-! ## 2. The other two member shapes: a record member and a newtype member

Both families so far are made of `ctors` members.  A member of a family can also be a
**record** or a **newtype**, and a fold has to answer for those too — and may descend into
them.  The family here has all three, so it is written in a scope of three members
(`TyWfIn 3`, the node's `n = 1`):

```lean
mutual
inductive Node where
  | mk (label : Nat) (next : Opt) (tags : Tags)   -- a record member
inductive Opt where
  | none
  | some (n : Node)                               -- a member with constructors
inductive Tags where
  | mk (ts : Array Nat)                           -- a newtype member, its wrapper erased
end
```

Counting every constructor, a `Node` is one level above its `next` and an `Opt.some` one
level above its `Node`, so `fib` of that count is the `fib` of the request once more — and
at depth one **both** recursive members descend: the `Node` branch into the `Opt`, and the
`Opt.some` branch into the `Node`.  The `Tags` branch answers: its body is an array of
naturals, which is not an occurrence of a member, so the fold has nothing to give it. -/

mutual

/-- The record member: a label, a link and some tags. -/
inductive Node where
  /-- The only constructor of a record member. -/
  | mk (label : Nat) (next : Opt) (tags : Tags)

/-- The member with constructors: the link may end. -/
inductive Opt where
  /-- The chain ends. -/
  | none
  /-- One more node. -/
  | some (n : Node)

/-- The newtype member. -/
inductive Tags where
  /-- The wrapper, which is erased. -/
  | mk (ts : Array Nat)

end

mutual

/-- How many constructors of the family a `Node` is made of. -/
def Node.len : Node → Nat
  | .mk _ o _ => 1 + Opt.len o

/-- How many constructors of the family an `Opt` is made of. -/
def Opt.len : Opt → Nat
  | .none => 0
  | .some n => 1 + Node.len n

end

/-- `fib` of the number of constructors of a `Node`. -/
def Node.fib (n : Node) : Nat := TermTests.FibWindow.fib (Node.len n)

/-- `fib` of the number of constructors of an `Opt`. -/
def Opt.fib (o : Opt) : Nat := TermTests.FibWindow.fib (Opt.len o)

/-- A chain of `n` nodes. -/
def Node.ofNat : Nat → Node
  | 0 => .mk 0 .none (.mk #[])
  | n + 1 => .mk 0 (.some (Node.ofNat n)) (.mk #[])

-- A chain of `n` nodes is `2 * n + 1` constructors, so its answer is `fib (2 * n + 1)`.
-- [SKIPPED BY PROFILE_LAKE] example : Node.fib (Node.ofNat 5) = 89 := by kernel_rfl

/-- The `Node` branch of the recursion: a node whose link ends answers `1`. -/
theorem Node.fib_none (l : Nat) (t : Tags) : Node.fib (.mk l .none t) = 1 := rfl

/-- The `Node` branch of the recursion: a node whose link goes on answers with the answer
    at the node below it and the answer at its own link — the two values the depth-one
    branch of the fold is given. -/
theorem Node.fib_some (l : Nat) (m : Node) (t : Tags) :
    Node.fib (.mk l (.some m) t) = Node.fib m + Opt.fib (.some m) := by
  show TermTests.FibWindow.fib (1 + (1 + Node.len m)) =
    TermTests.FibWindow.fib (Node.len m) + TermTests.FibWindow.fib (1 + Node.len m)
  rw [show 1 + (1 + Node.len m) = Node.len m + 2 from by omega,
    show 1 + Node.len m = Node.len m + 1 from by omega]
  rfl

/-- The `Opt` branch of the recursion: an ended link answers `0`. -/
theorem Opt.fib_none : Opt.fib .none = 0 := rfl

/-- The `Opt` branch of the recursion: a link that goes on answers with the answer at its
    node and the answer at *that* node's link — the two values the depth-one branch of the
    fold is given, after descending into the record member. -/
theorem Opt.fib_some (l : Nat) (o : Opt) (t : Tags) :
    Opt.fib (.some (.mk l o t)) = Node.fib (.mk l o t) + Opt.fib o := by
  show TermTests.FibWindow.fib (1 + (1 + Opt.len o)) =
    TermTests.FibWindow.fib (1 + Opt.len o) + TermTests.FibWindow.fib (Opt.len o)
  rw [show 1 + (1 + Opt.len o) = Opt.len o + 2 from by omega,
    show 1 + Opt.len o = Opt.len o + 1 from by omega]
  show TermTests.FibWindow.fib (Opt.len o) + TermTests.FibWindow.fib (Opt.len o + 1) = _
  omega

/-- Member `0`: a record of a label, a link and the tags. -/
def memNode : LeanFamMemberSchema (TyWfIn 3) :=
  .record ⟨(Ty.prim .nat).toTyWfIn, (Ty.familyMember 1).toTyWfIn,
    [(Ty.familyMember 2).toTyWfIn]⟩

/-- Member `1`: `none | some (n : member 0)`. -/
def memOpt : LeanFamMemberSchema (TyWfIn 3) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 0).toTyWfIn, []⟩ []))

/-- Member `2`: a newtype whose body is an array of naturals. -/
def memTags : LeanFamMemberSchema (TyWfIn 3) :=
  .alias (Ty.array (Ty.prim .nat)).toTyWfIn

/-- The three-member family, selecting the record member. -/
def famNode : LeanMutualRecFamily (TyWfIn 3) :=
  .selectedThenMore [] memNode memOpt [memTags]

/-- That it describes types. -/
theorem nodeWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famNode) := by ty_wf

/-- The type of member `0`. -/
def nodeTy : TyWf := .mutualRecursiveFamily famNode nodeWf

/-- How the value of a fold over this family reaches a branch. -/
abbrev nbind (τ : TyWf) : List (TyWfIn 3) → List TyWf :=
  TyWf.famRecBinders famNode nodeWf τ

/-- The context the fold below is written in. -/
abbrev NCtx : Ctx := [nodeTy]

-- The record member binds its label, its link and the answer at the link, its tags and
-- the answer at them; the newtype member binds its body, an array of naturals, and gets
-- no answer, since an array of naturals is not an occurrence of a member.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     nbind τ [(Ty.prim .nat).toTyWfIn, (Ty.familyMember 1).toTyWfIn,
-- [SKIPPED BY PROFILE_LAKE]       (Ty.familyMember 2).toTyWfIn] =
-- [SKIPPED BY PROFILE_LAKE]       [natT, TyWf.famMemberTy famNode nodeWf 1, τ, TyWf.famMemberTy famNode nodeWf 2, τ] :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : nbind τ [(Ty.array (Ty.prim .nat)).toTyWfIn] = [TyWf.array natT] := by kernel_rfl

/-- The branches of `fib` over the three-member family: the record member descends into
    the link (member `1`), the `some` branch of the link descends into the node
    (member `0`, a **record** member, so what it is given is that record's one branch), and
    the newtype member answers.

    These are written out rather than translated: `Tags` does not mention `Node` or `Opt`,
    so `LeanScriptTyWf` models it as a type of its own (a type has one model: a `mutual`
    block is split into the groups of declarations that mention each other), and no Lean
    type has this three-member family as its tree. -/
def nodeFibCases :
    FamilyFoldKCases sigAdd 1 famNode.members (nbind natT) NCtx natT famNode.members 1 :=
  .cons
    (.record
      (.deep (.there (.here rfl)) (.there .here)
        (.ctors
          (.skip (.here (.nat_mk 1))
            (.here (.here (addT (.var (v♯1)) (.var (v♯4)))) .nil)))))
    (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.record (.here (addT (.var (v♯6)) (.var (v♯2))))))
            .nil)))
      (.cons (.alias (.here (.nat_mk 0))) .nil))

/-- `Node.fib`, as a term: the depth-one fold of a family of a record, a union and a
    newtype. -/
def nodeFibTerm : Term sigAdd [] (nodeTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec' 1 (.var (v♯0)) nodeFibCases)

/-! ## 3. Running the terms

A mutual family denotes the indexed W-tree of its members (`LeanScript.Ty.Den`), so the
evaluator runs both folds above.  The checks below build chains as terms — crossing from
one member to the other at every link — run the programs on them with `add` supplied as
`Nat.add`, and compare with the Lean references; they are closed by the kernel. -/

open TermTests.FamilyRecDepth (envAdd)

/-- The alternating family, selecting member `1`. -/
def famOd : LeanMutualRecFamily (TyWfIn 2) := .selectedLast memEv [] memOd

/-- The type of member `1` of the alternating family. -/
def odTy : TyWf := .mutualRecursiveFamily famOd

mutual

/-- An `Ev` chain of `n` links, as a term. -/
def evNat : Nat → Term sigAdd [] evTy
  | 0 => .mutualRecursiveFamily_mk famEv evWf (value := .ctors _ 0 (fields := .nil))
  | n + 1 =>
      .mutualRecursiveFamily_mk famEv evWf (value := .ctors _ 1 (fields := .cons (odNat n) .nil))

/-- An `Od` chain of `n` links, as a term. -/
def odNat : Nat → Term sigAdd [] odTy
  | 0 => .mutualRecursiveFamily_mk famOd (value := .ctors _ 0 (fields := .nil))
  | n + 1 =>
      .mutualRecursiveFamily_mk famOd (value := .ctors _ 1 (fields := .cons (evNat n) .nil))

end

-- [SKIPPED BY PROFILE_LAKE] example : (List.range 11).map (fun n => Term.run envAdd (.ap evFibTerm (evNat n))) =
-- [SKIPPED BY PROFILE_LAKE]     (List.range 11).map (fun n => Ev.fib (Ev.ofNat n)) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-- The three-member family, selecting the `Opt` member. -/
def famOpt : LeanMutualRecFamily (TyWfIn 3) := .selectedThenMore [memNode] memOpt memTags []

/-- The three-member family, selecting the `Tags` member. -/
def famTags : LeanMutualRecFamily (TyWfIn 3) := .selectedLast memNode [memOpt] memTags

/-- The type of the `Opt` member. -/
def optTy : TyWf := .mutualRecursiveFamily famOpt

/-- The type of the `Tags` member. -/
def tagsTy : TyWf := .mutualRecursiveFamily famTags

/-- No tags, as a term: the newtype member wraps an empty array. -/
def tagsNil : Term sigAdd [] tagsTy :=
  .mutualRecursiveFamily_mk famTags (value := .alias _ (Term.array_mk .nil : Term sigAdd [] (TyWf.array natT)))

/-- A node with label `0`, the given link and no tags, as a term. -/
def nodeOf (o : Term sigAdd [] optTy) : Term sigAdd [] nodeTy :=
  .mutualRecursiveFamily_mk famNode nodeWf
    (value := .record _ (.cons (.nat_mk 0) (.cons o (.cons tagsNil .nil))))

/-- The link below a chain of `n` nodes, as a term. -/
def optNat : Nat → Term sigAdd [] optTy
  | 0 => .mutualRecursiveFamily_mk famOpt (value := .ctors _ 0 (fields := .nil))
  | n + 1 =>
      .mutualRecursiveFamily_mk famOpt
        (value := .ctors _ 1 (fields := .cons (nodeOf (optNat n)) .nil))

/-- A chain of `n` nodes, as a term. -/
def nodeNat (n : Nat) : Term sigAdd [] nodeTy := nodeOf (optNat n)

-- [SKIPPED BY PROFILE_LAKE] example : (List.range 6).map (fun n => Term.run envAdd (.ap nodeFibTerm (nodeNat n))) =
-- [SKIPPED BY PROFILE_LAKE]     (List.range 6).map (fun n => Node.fib (Node.ofNat n)) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

end TermTests.FamilyRecDepthMembers
