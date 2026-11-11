import Tiling.MainResults.Main

/-!
# Print the public theorem types and their logical assumptions

Run `lake env lean Tiling/MainResults/Audit.lean` from the project root.
All four main results are unconditional, including co-r.e. hardness.
-/

open Tiling.MainResults

#check exists_computable_wang_to_AB
#check exists_computable_AB_to_stick
#check stickTiling_undecidable
#check stickTiling_coREHard

#print axioms exists_computable_wang_to_AB
#print axioms exists_computable_AB_to_stick
#print axioms stickTiling_undecidable
#print axioms stickTiling_coREHard
