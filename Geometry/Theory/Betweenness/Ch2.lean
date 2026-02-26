import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Tactics

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Betweenness

-- TODO: For this and other commutative properties, I think there is a class to instantiate to get that .symm thing to
-- work.

/-- a line doesn't care about the order of the points it guards -/
lemma guards_commutes : (L guards A and B) -> (L guards B and A) := by
    intro LguardsAB
    unfold SameSide at *; rw [<- Line.segment_AB_eq_segment_BA] ; tauto

/-- a line doesn't care about the order of the points it splits -/
lemma splits_commutes : (L splits A and B) -> (L splits B and A) := by
    intro LsplitsAB
    unfold SameSide at *; rw [<- Line.segment_AB_eq_segment_BA] ; tauto


end Betweenness

end Geometry.Theory
