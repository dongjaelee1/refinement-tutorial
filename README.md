# refinement-tutorial
Tutorial for refinement-based verification

Work In Progress.

## Build
Requirement: opam (>=2.0.0), Coq 8.15.0
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## Structure
All the files are in `src/tutorial/`.

`Refinement.v`

-> `Imp.v`

-> `FiniteSimulation.v`

-> `Example1.v`

-> `Example2.v`

-> `Simulation.v`

-> `Example3.v`
