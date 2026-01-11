module

public import Mathlib.Data.Set.Basic
public import Geometry.Ch2.Theory
public import Geometry.Ch3.Theory

@[expose] public section

namespace Geometry.Ch3.Defs

open Geometry.Ch2.Theory
open Geometry.Ch3.Theory

variable [FreeGeometry]
variable [IncidenceGeometry]
variable [G : BetweenGeometry]



def Segment (A B : G.Point) : Set G.Point := {A} ∪ {B} ∪ {P : G.Point | G.Between A P B}

def Ray (A B : G.Point) : Set G.Point := Segment A B ∪ {P : G.Point | G.Between A B P}

-- Ed Note: It is convenient to just rely on the Prop 3.1 union-of-ray's definition here, rather than
-- do a bunch of work to build it based purely on incidence. In the IA proofs in Ch.2, This set-theoretic
-- approach might be useful in some circumstances, but the purely-axiomatic approach is nice.
-- I think it's likely possible to also define these as pure Props, but it would quickly become tedious
-- to do all that work.
def LineThrough (A B : G.Point) : Set G.Point := (Ray A B) ∪ (Ray B A)


end Geometry.Ch3.Defs
