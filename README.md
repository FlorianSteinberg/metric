This repository provides a formalization of metric spaces roughly following the layout of Coquelicot.
However, in contrast to Coquelicot, some axioms are assumed in addition to the axioms the standard library uses for the real numbers:
Proofirrelevance is used so it is possible to talk about subspaces and some parts assume FunctionalCountableChoice and classical reasoning.
For instance the proof that sequential continuity is equivalent to regular continuity does so.
The "coquelicot" file provides compatibility with the NormedModule, AbsRing and UniformSpaces structures from Coquelicot and a translation lemma for continuity.
The "standard" file provides compatibility with the Metric_Space class from the standard library and proves equivalence of the limit notions.
The dependencies are Coquelicot, mathcomp and some parts from my rlzrs library that can also be found on github.
