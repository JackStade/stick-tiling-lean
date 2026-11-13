# Stick Tiling in Lean

This Lean project formalises the reduction from Section 2 of [*Two Tiling is
Undecidable*](https://arxiv.org/abs/2506.11628). The reduction is from Wang tiling
to tiling the hexagonal grid by one stick polyhex with edge-to-edge matching rules.

The results that we formalise are:

- the computable reductions Wang tiling → AB tiling and AB tiling → stick tiling;
- undecidability of stick tiling;
- co-RE hardness of stick tiling.

The statements of these results and necessary definitions are contained in **[Tiling/MainResults/README.md](Tiling/MainResults/README.md)**.
Technical proofs live in `Tiling/Proofs`. The main result is also available as
`StickPolyhex.ABSim.theorem2` in `Tiling/Proofs/Undecidability.lean`. 
The undecidability and co-RE hardness results use [`lean-wang`](https://github.com/edemaine/lean-wang) to provide a formalisation of the undecideability and hardness of Wang tiling.
The project and its dependencies are pinned to Lean and mathlib 4.31.0.

## Changes from the Paper

The formal proof here incorporates a couple of minor changes compared to the one in the paper. 
These are explained in detail in [DEPARTURES.md](DEPARTURES.md).

## Build

Check the public interface and its proof dependencies with:

```sh
lake build Tiling.MainResults.Main
```

Build the complete development with:

```sh
lake build
```

## AI Use

The code in this project was produced primarirly by [Aristotle](https://aristotle.harmonic.fun).

Some smaller edits and refactoring were done using ChatGPT 5.6 Sol and ChatGPT 6 Astra.

## License

Copyright 2026 Jack Stade

This project is licensed under the [Apache License 2.0](LICENSE).


