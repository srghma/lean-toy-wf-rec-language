module

public import LeanScript.CtorFn
public import LeanScript.Eval

@[expose] public section

open LeanScript

namespace CtorFnModuleTest

inductive Color | red | green | blue

structure Pt where
  x : Nat
  y : Nat

def natT : TyWf := .prim .nat

def green : Term ⟨[], List.nodup_nil⟩ [] (#leanscript_layout `Color `green) := #leanscript_ctor `Color `green
def pt : Term ⟨[], List.nodup_nil⟩ [] (#leanscript_layout `Pt) := #leanscript_ctor `Pt (.nat_mk 1) (.nat_mk 2)
def some3 : Term ⟨[], List.nodup_nil⟩ [] (#leanscript_layout `Option `some natT) :=
  #leanscript_ctor `Option `some natT (.nat_mk 3)

end CtorFnModuleTest
