# 25-FEB-2026

## 0028

I can't believe I didn't have this going already.

I'm trying to reorganize things a bit. I have a huge pile of general theory that I had to build up to formalize 3.2, and
I learned a bunch about the namespace system, and I have a rough idea of what I want to do, but I'm trying to think of
the best way to structure things.

My current setup has

```
Geometry/
    ChX/ -- directory per chapter
        Prop/
            PY.lean -- file per proposition and related correlaries. Currently contains a bunch of loose theory
        Ex/
            ExZ.lean -- file per exercise (if multipart, it's all here).
        Prop.lean
        Ex.lean
        README.md
    Theory/
        Concept/ -- A directory for each "Concept", e.g., Line, Betweenness, Collinearity, Intersection, etc
            ChX.lean -- A file for all the general theory needed for that chapter. May depend on previous chapters.
            ChX/ -- if there is a directory, ChX.lean should exist to bring in it's contents
    Syntax.lean -- any custom syntax I need at the topmost level, mostly empty
    Tactics.lean -- imports mathlib tactics
    Theory.lean -- imports everything, main entry point to the theory
Geometry.lean -- pulls in the chapter propositions and exercises via the `Prop.lean`
```

This mostly lets me interleave and get all the ordering right, but it's a bear to build the main import file
(Theory.lean) because the order of the tree is wrong, chapters should parent concepts, but then I have the opposite
problem in the directory structure -- I have to replicate the concept folders over and over.

I _really_ wish that lean just jammed everything into a database, worked out the dependencies, and complained when it
couldn't. Maybe the module system will fix this? I haven't really looked too much into it except for my initial attempt,
I'll have to investigate.

For now I suppose I can write a script to generate the theory file.

I added a flake.nix and set up python, so I suppose I'll use that. I saw the blueprint tool uses python to interact with
the lean code to generate the graphviz file, so maybe I can crib from them a bit.

Unrelated, it'd be very cool to build some kind of geogebra/lean connection (maybe using
[proofwidgets](https://github.com/leanprover-community/ProofWidgets4)?), not sure the feasibility (especially since I'm
not on vscode which I suspect is required, but haven't found an explicit statement thereof).


# 25-FEB-2026

## 2235

I got pretty much everything reorganized, it wasn't _too_ painful. I also rewrote a bunch of proofs in a much nicer way;
in particular `Line.line_trichotomy` is a really handy tool.

The debate now is whether I'm going to automate generating the Geometry.lean and Theory.lean files; and more generally
it'd be nice to have some scaffolding scripts for creating new chapters/etc in the correct structure. I had a `ChX`
chapter-template, but I wasn't sure what I was doing when I originally made it. The things I'd like some kind of
template/script for are:

1. Constructing the Geometry.lean, which includes all the actual chapters
2. Constructing the Theory.lean, which is where all the general theory and lemmas go
3. Constructing the `web` and `print` blueprint files via some introspection over all the theorems/lemmas in the
   codebase
4. Creating a new chapter/theory section according to whatever strictures I need.

I don't think I'm going to do this now, I'd like to get back to proving, but something to think on.

# 26-FEB-2026

## 2145

I'm making good headway on formalizing Greenberg's proof of 3.3; there was mostly just small stuff missing; my proof of
step (5) is close to done, but the proof is quite big as a result, and it's a conjuction of two similar but very
slightly different arguments that is going to be hard to `suffice` away.

I also ran into a new problem, speed. I made liberal use of `tauto` across this code base and it is starting to hurt.
It's mostly just laziness and a misunderstanding of cost; I've started taking it out where possible. I'll need to add
another script (or maybe a lint) to count these and chase them away. I'll also need to add a profile step to the CI. The
stats it produces are pretty basic, but it's more than enough to chase away performance blowups. The issue does seem
local to the proof (which makes sense, as it's essentially just hammering away using the available hypothesis, which
don't cut across proofs), it's interesting how proof complexity becomes a performance hazard; you lose a powerful tool
when the proof is too large. Even if you don't intend to keep the tauto, knowing that your environment has all the
equipment needed to finish the proof is quite useful, and if the proof is so complex that tauto takes forever, you are
essentially blinded by your own inefficiency.

Refactoring has always felt like an 'elegant' thing to do; and it's neat to see that mathematical parsimony, clever
argument, and smart lemma choices; things that feel themselves like elegance, are directly correlated with each other in
such a nice way.

I fucking love math.

Going to take a break from 3.3 and clean up tautos for a few commits.
