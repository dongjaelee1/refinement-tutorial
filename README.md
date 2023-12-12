# refinement-tutorial
Tutorial for refinement-based verification.

Work In Progress.

Some helpful references:

A convenient technique for stuttering simulation:
Minki Cho, Youngju Song, Dongjae Lee, Lennard Gäher, and Derek Dreyer. 2023. Stuttering for Free. Proc. ACM Program. Lang. 7, OOPSLA2, Article 281 (October 2023), 28 pages. https://doi.org/10.1145/3622857.

Paco: A Coq Library for Parameterized Coinduction (https://plv.mpi-sws.org/paco/).

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

-> `Example3.v` (WIP)
