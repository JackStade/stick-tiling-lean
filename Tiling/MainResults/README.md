# Definitions and main results

Start with **[Reductions.lean](Reductions.lean)** and
**[Undecidability.lean](Undecidability.lean)**. Each main theorem has a short proof
referring to the technical development outside this folder.

The complexity result is **co-RE hardness**: every co-RE predicate computably
many-one reduces to stick tiling. All four main results below are unconditional.

## Statements to check

All names below are in `Tiling.MainResults`.

| Declaration | Statement | Status |
|---|---|---|
| `exists_computable_wang_to_AB` | There is a computable map from Wang instances to AB instances preserving tilability in both directions. | Proved |
| `exists_computable_AB_to_stick` | There is a computable map from AB instances to marked sticks preserving tilability in both directions. | Proved |
| `stickTiling_undecidable` | `¬ ComputablePred StickPolyhex.StickTilesGrid` | Proved |
| `stickTiling_coREHard` | `LeanWang.CoREHard StickPolyhex.StickTilesGrid` | Proved |

The two reductions quantify over **all** inputs, including empty lists. AB input
lists may have different lengths. The stick problem here is the finite `MarkData`
model of a single marked stick with the eleven base matching rules and the extra
arrow/triangle rules. It is not a statement about undecorated sticks.

## Definitions, in reading order

1. [Computability.lean](Computability.lean): meanings and checked expansions of
   computable many-one reduction, co-RE membership, and hardness.
2. [WangTiling.lean](WangTiling.lean): the Wang tile fields, input encoding, and a
   checked expansion of plane tilability. The authoritative Wang definitions are
   imported from the pinned `lean-wang` dependency, rather than duplicated.
3. [ABTiling.lean](ABTiling.lean): `ABTile`, `ABTileSet`, their encodings,
   `tileHeight`, `ValidABTiling`, and `ABTilesPlane`.
4. [HexGrid.lean](HexGrid.lean): cells, the six directions, and neighbours.
5. [StickDefinitions.lean](StickDefinitions.lean): `StickTiling`, boundary labels,
   every base forbidden pair, general matching rules, `SatisfiesRules`, markings,
   every extra forbidden pair, and `markedRules`.
6. [StickInstance.lean](StickInstance.lean): finite `MarkData`, its encoding and
   interpretation as matching rules, and the decision predicate `StickTilesGrid`.

These are the actual definitions used by the proofs. Elementary encoding and
well-formedness proofs are included next to
these definitions. The standard foundations (`Computable`, `REPred`,
`Primcodable`, integers, lists, etc.) remain in Mathlib. Wang definitions remain in
[LeanWang.Basic](../../.lake/packages/lean_wang/LeanWang/Basic.lean), and the co-RE
interface in [LeanWang.CoRE](../../.lake/packages/lean_wang/LeanWang/CoRE.lean).

## Technical proofs outside this folder

| Result | Proof implementation |
|---|---|
| Wang → AB | [ABTiling.lean](../Proofs/ABTiling.lean) |
| AB → stick, including empty inputs and computability | [ABReduction.lean](../Proofs/ABReduction.lean) |
| Wang → stick | [Reduction.lean](../Proofs/Reduction.lean), [ReductionConverse.lean](../Proofs/ReductionConverse.lean), [ReductionCompute.lean](../Proofs/ReductionCompute.lean) |
| Undecidability and co-RE hardness | [Undecidability.lean](../Proofs/Undecidability.lean) |
| Compactness | [Compactness.lean](../Proofs/Compactness.lean) |

The remaining geometric and gadget proofs live in `Tiling/Proofs`, outside
`MainResults`.
Definition modules in this folder do not import those geometric or gadget proofs;
the result modules do, so Lean checks the full justification of every exported theorem.

## Checking

From the project root:

```sh
lake build Tiling.MainResults.Main
lake build
```

For a single public import in another Lean file:

```lean
import Tiling.MainResults.Main
```

To print the exact theorem types and the logical axioms used by their proofs:

```sh
lake env lean Tiling/MainResults/Audit.lean
```

The audit confirms that both reduction proofs use only `propext`,
`Classical.choice`, and `Quot.sound`. Undecidability and hardness additionally
inherit the generated `native_decide` axioms of the
pinned `lean-wang` Robinson certificate. The audit prints those assumptions in
full; none of these four results depends on `sorryAx`.
