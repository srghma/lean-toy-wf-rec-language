import RequestProject.WFLang.Examples.Langs

/-! Benchmark: `diagonal_tr m 0 0` (about `m²/2` tail calls) through each evaluator and
natively. Usage: `lake exe wfbench <native|pcl|tail|meas> <m>` -/

def main (args : List String) : IO Unit := do
  let (lang, m) := match args with
    | [l, m] => (l, m.toNat!)
    | _ => ("tail", 1000)
  let t0 ← IO.monoMsNow
  let r := match lang with
    | "native" => Tco.diagonal_tr m 0 0
    | "pcl" => ExPCL.diagonal_tr_run m 0 0
    | "meas" => ExMeas.diagonal_tr_run m 0 0
    | _ => ExTail.diagonal_tr_run m 0 0
  IO.println s!"{lang} m={m}: result {r}"
  IO.println s!"{(← IO.monoMsNow) - t0} ms"
