import RequestProject.WFLang.Tests.Basic

/-! Benchmark: `diagonal_tr m 0 0` (about `m²/2` tail calls), natively and through the `PCL`
evaluator. Usage: `lake exe wfbench <native|pcl> <m>` -/

def main (args : List String) : IO Unit := do
  let (lang, m) := match args with
    | [l, m] => (l, m.toNat!)
    | _ => ("pcl", 1000)
  let t0 ← IO.monoMsNow
  let r := match lang with
    | "native" => Tco.diagonal_tr m 0 0
    | _ => ExPCL.diagonal_tr_run m 0 0
  IO.println s!"{lang} m={m}: result {r}"
  IO.println s!"{(← IO.monoMsNow) - t0} ms"
