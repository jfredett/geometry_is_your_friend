
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Ch1
import Geometry.Theory.Ch2
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch2

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex


/-- p112. Given A - B - C and A - C - D, then B - C - D and A - B - D (see Figure 3.9) -/
theorem P3.left : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> B - C - D := by 
  /- (1) A, B, C, and D are distinct, collinear points (see Exercise 1). -/
  intro A B C D ⟨ABC, ACD⟩
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  have ⟨colABC, colBCD⟩ := Ex1.b ⟨ABC, ACD⟩
  /- (2) There exists a point E not on the line through A,B,C,D (Proposition 2.3) -/
  -- NOTE: WLOG, we can pick any two points because all these points are collinear
  let L := line A D
  have ⟨E, EoffL⟩ := Ch2.Prop.P3 L
  /- (3) Consider line EC. Since (by hypothesis) AD meets this line in point C,... -/
  let EC := line E C
  have LintECatC : L intersects EC at C := by
    sorry
  /- ... points A and D are on opposite sides of EC -/
  have ECsplitsAandD : EC splits A and D := by
    sorry
  /- (4) We claim A and B are on the same side of EC. Assume on the contrary that A and B are on opposite sides of EC
     (RAA Hypothesis) -/
  by_cases raa : EC splits A and B
  · /- p113. (5) Then EC meets AB in a point between A and B (definition of "opposite sides" [ed. "splits" in our parlance]). -/
    have ⟨X, ECintABatX, AXB⟩ : ∃ X : Point, (EC intersects (segment A B) at X) ∧ (A - X - B) := by sorry
    /- (6) That point must be C (Proposition 2.1) -/
    have XeqC : X = C := by sorry -- intersection is uniq 
    /- (7) Thus A - B - C and A - C - B, which contradicts Betweenness Axiom 3. -/
    have ACB : A - C - B := by sorry
    exfalso
    exact Betweenness.absurdity_abc_acb ⟨ABC, ACB⟩
  · /- (8) Hence, A and B are on the same side of EC (RAA conclusion)
       (9) B and D are on opposite sides of EC (steps 3 and 8 and the corrolary to Betweenness Axiom 4). -/
    have ECsplitsBandD : EC splits B and D := by sorry
    /- (10) Hence, the point C of intersection of lines EC and BD lies between B and D (definition of "opposite sides";
       Proposition 2.1, i.e., that the point of intersection is unique). -/
    have BCD : B - C - D := by sorry
    exact BCD
  /- A similar argument involving EB proves that A - B - D -/

  /- TODO: Ed: time to break out `suffices` or some other clever thing... -/
  

-- theorem P3.right : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> B - C - D := by sorry
-- theorem P3.left : ∀ A B C D : Point, (A - B - C) ∧ (A - C - D) -> A - B - D := by sorry


end Geometry.Ch3.Prop
