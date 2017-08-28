# Proofs of IceDust properties

Several properties of IceDust are worth proving:

* Type soundness
* Multiplicity soundness
* Preservation of Bidirectionality (*)
* Correctness of incremental runtime (*)

(*) Argued informally in the [IceDust 2 paper](http://doi.org/10.4230/LIPIcs.ECOOP.2017.14)

## Type- and Multiplicity Soundness
We prove type- and multiplicity soundess for the majority of the IceDust expression language in [multiplicities.v](multiplicities.v).
It includes all language constructs without environments (no `filter`, `find` and `orderBy`) and objects.

These proofs can be extended to cover expressions with need for environments by adding environments to the interpreter.

For adding objects, the model (including derived value fields), the interpreter has to be changed to a non-terminating interpreter.
This means termination has to be relaxed to progress, or to fuel-based interpretation.

## Preservation of bidirectionality
This property is only interesting to guarantee if multiplicity bounds are guaranteed at the same time as outlined in the IceDust 2 paper.

The simple version of this proof would cover IceDust without derived values: just an object graph with getters and setters.

This proof can then be extended with derived relations.

## Correctness of incremental calculation strategies
For all programs that terminate with the non-incremental runtime, it holds that the incremental runtime returns the same value as the non-incrmental runtime.
(For cyclic programs the incremental runtime returns a fixed point, while the non-incremental runtime does not terminate.)

A simple version of this proof would cover a single IceDust object (or rather a language with no objects, and just a set of global fields).
This proof would include an invariant such as "reevaluating an expression results in exactly the cached value \/ the up-to-date flag is false" (taken from the IceDust 2 paper).
Moreover this proof would need include a simple version of the path-based abstract interpretation from the [IceDust 1 paper](http://doi.org/10.4230/LIPIcs.ECOOP.2016.11).
The simplest proof can completely ignore multiplicities and only have integer expressions.

This proof can then be extended to IceDust 1, with derived attributes and bidirectional relations (but not derived bidirectional relations).
This requires modeling multiplicities (to be able to do path-inversion) and the path-based abstract interpretation dealing with both paths that are extendible and that are not (see abstract interpretation in IceDust 1 paper).

Then, that proof can be extended to cover derived relation as well.
This means that the graph which is used for dirty flagging is dynamic as well.

Another extension for the proof is to cover both eager-incremental (update all caches on write) and lazy-incremental (dirty caches on write, update un read).

The proof also could be extended with the `(inline)` behavior.

Finally, the proof could be extended to deal with calculation strategy composition.
