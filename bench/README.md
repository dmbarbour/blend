# Blend's benchmarks

How Blend's cost grows with the modules it emits. Each family is measured
at N, 2N and 4N, as one size hides superlinear growth.

- `families.bend` prints a module of N definitions of one shape, each
  definition i calling earlier ones, and a `main` calling the last:
  `chain`, i calling i-1; `fan`, i-1, i-2, i/2 and i/3; `dense`, every
  earlier definition; `down`, i calling i+1, written top down, so that
  the walk's stack holds the whole chain; `copies`, in an object, each
  shared and calling a copied definition, written last, twice, so that
  it has 2N numbered copies.

      bend bench/families.bend chain|fan|dense|down|copies N > module.blend

- `measure.sh` emits a family at N, 2N and 4N with Blend's built
  executable, each run capped (`scripts/capped.sh`, 4,000 MB and 600 s
  by default), and prints its instructions (`scripts/count.sh`, under
  `perf`) and seconds, recording them in the analysis store
  (`scripts/results.py`: a run, each size a row of `counts`, its seconds
  a metric). The modules and what Blend writes go to
  `results/bench` (out of git).

      bench/measure.sh chain|fan|dense|down|copies N [MB SECONDS]

- `andor.bend` reproduces a Bend behavior Blend's code must reckon
  with: `&&` and `||` evaluate both sides in a native build, a false
  left side under `&&` and a true one under `||` costing the right
  side's work (Bend 2.0.39, 2026-11-06; each case's work grows with N,
  the control's too). Decide on a cheap test in a helper matching a
  `Bool` parameter instead (`docs/Proving.md`).
      bend bench/andor.bend -o andor; andor CASE N
Results and what they found are in the plan step that uses them,
`blend-scale` (`docs/plans/Blend_2026-11-04.md`).
