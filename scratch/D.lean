import RequestProject.WFLang.Tests.Joins
open WFLang PCL
namespace JoinEx
def seq2 (n : Nat) : Nat :=
  if n = 0 then 0 else
    (if n % 2 == 0 then seq2 (n - 1) else 1) +
    (if n % 3 == 0 then seq2 (n - 1) else 2)
termination_by n
def seq3 (n : Nat) : Nat :=
  if n = 0 then 0 else
    (if n % 2 == 0 then seq3 (n - 1) else 1) +
    (if n % 3 == 0 then seq3 (n - 1) else 2) +
    (if n % 5 == 0 then seq3 (n - 1) else 3)
termination_by n
end JoinEx
set_option wfLang.joinPoints false in
def s2d : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq2
#eval s2d.size
set_option maxHeartbeats 2000000 in
set_option wfLang.joinPoints false in
def s3d : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq3
#eval s3d.size
def s2 : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq2
def s3 : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq3
#eval (s2.size, s3.size)
