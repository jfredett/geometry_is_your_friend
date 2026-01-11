# Rough layout

- Theory.lean
    - Core theory additions/extensions.
- Defs
    - Definitions, depends on Theory, sparingly other defs.
- Prop
    - Propositions, depends on Theory and Defs
- Ex
    - Relevant Exercises, depends on all others.

# TODO

```lean

-- p92. "For each pair of axioms of incidence geometry, invent an interpretation in which those two axioms are satisfied,
-- but the third is not. (This will show that the three axioms are _independent_ in the sense that it is impossible to
-- prove any one of them from the other two)."
-- theorem ex_2_7_ia_independence := by sorry

-- p92. "Show that the interpretations in examples 3 and 4 of [chapter 2] are models of incidence geometry and that the
-- Euclidian and hyperbolic parallel properties, respectively, hold for them."
-- theorem ex_2_8_model := by sorry

-- p93. "
-- A. Show that when each of two models of incidence geometry has exactly three "points" in it, the models are
-- isomorphic
-- theorem ex_2_10a := by sorry
-- B. Must two models having exactly four "points" be isomorphic? [Prove or provide counterex]"
-- theorem ex_2_10b := by sorry
-- [ED: C. Omitted since we're not doing ex 9.]

-- p93. "Invent a model of incidence geometry that has neither the elliptic, hyperbolic, nor Euclidean parallel
-- properties... [ED: Definitions follow]"
-- example ex_2_11 := by sorry

-- exercise 2.12 := by sorry

-- FIXME: Ideally, propositions would be under their own ns, and exercises another. so the result'd be something like:
-- Geometry.ch2.props.p1 -> prop 2.1
-- Geometry.ch2.exers.e1 -> exercise 1 of ch2

-- TODO: Macro for prop vs theorem that does the above.

-- NOTE: Exercises are only going to be done where it makes sense to do them, e.g., if they have geometric value.
-- many of the exercises, especially in the early chapters, are just exercising basic logic rules, and while that's
-- valuable and you should do it, it's assumed that if you know what Lean4 is, have assessed this work as _somehow_
-- having value, and are reading this comment, that you know how to manipulate logical sentences relatively well.

```