# Departures from the Paper

Here, we explain a couple of minor changes in the formal proof compared to the proof in the original paper. 

## Extra Arrow Marks on Extreme Buckets

During the formalisation process, a small bug was found in the original proof of the gap conditions.
Specifically, the conditions can fail if the interval `I_i` for one of the first or last buckets does not contain `0`.
This does not meaningfully affect the construction, because it only uses `I_i` that contain `0`.
The paper was changed to require that each `I_i` contains `0`.
The formalisation instead adds some extra arrow marks to the extreme buckets when `I_i` does not contain `0`.
This does not change the actual construction used, because `I_i` always contains `0`.

## Outer Bucket-Boundary Arrows are Dropped

The paper places arrow markings are the first and last intervals of every bucket.
The formalisation omits the arrow markings at the start of the first bucket and at the end of
the last bucket.
These arrow markings are unnecessary, and it slightly simplifies the proof to drop them.

## Increasing the Value of `d`

The construction from Sections 2.6-2.9 of the paper use a spacing parameter `d`. 
In Section 2.8, this is set to `d=12k`, where `k` is the number of colors in the AB tiling instance.
The formalisation uses the larger value of `d=(12k+t)`, where `t` is the number of `A` or `B` tiles.
This does not meaningfully affect the construction or the verification, but it simplifies some of the
formal proofs.