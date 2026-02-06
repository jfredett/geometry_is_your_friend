/- -- this is Prop 3.3
@[simp] theorem P3 {A B C X : Point} : A - C - X -> A - X - B -> A - C - B := by
  intro ACX AXB
  obtain ⟨⟨AneC, CneX, AneX⟩, ⟨⟨L, AonL, ConL, XonL⟩, ACXCol⟩⟩ := B1a ACX
  obtain ⟨⟨AneX, XneB, AneB⟩, ⟨⟨M, AonM, XonM, BonM⟩, AXBCol⟩⟩ := B1a AXB
  have LeqM : L = M := Line.equiv L M A X AneX ⟨AonL, AonM, XonL, XonM⟩
  -- there is only one line here, and B is on it.
  rw [<- LeqM] at BonM
  have CneB : C ≠ B := by
    by_contra! hNeg
    rw [hNeg] at ACX
    -- need A B X and A X B are a contradiction
    exact absurdity_abc_acb ⟨ACX, AXB⟩
  have hDistinct : A ≠ B ∧ A ≠ C ∧ A ≠ X ∧ B ≠ X ∧ B ≠ X ∧ C ≠ X := by tauto
  -- FIXME: This sucks. A better way to construct distinct-blocks would be nice.
  have distinctACBX : distinct A C X B := by simp_all only [ne_eq, not_false_eq_true, B1a, and_self_left,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, implies_true, and_self,
    IsEmpty.forall_iff, List.Pairwise.nil]
  have ACBCol : Collinear A C B := Collinear.inclusion distinctACBX ⟨ACXCol, AXBCol⟩
  -- the diagram is:  A - C - X - B
  rcases B3 A C B ⟨AneC, CneB, AneB, ACBCol⟩ with ⟨ACB, nCAB, nABC⟩ | ⟨nACB, CAB, nABC⟩ | ⟨nACB, nCAB, ABC⟩
  exact ACB -- simple case
  -- the line is A -- C -- X
  --             A ------- X -- B
  -- maybe an intermediate? If ACX and AXB then CXB?
  exfalso;
  -- CAB = BAC, BAC + ACX -> BAX
  sorry -- ACX contradicts CAB, since A is 'to the left' of C and B is 'to the right' of A, so B can't be 'to the left' of A
  exfalso; sorry -- ACX contradicts ABC, since
-/
