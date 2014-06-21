# TODO:

* Implement shortcuts desugarings: auto add shortcuts

# Differences between formal specification and implementation

* Formal: inverses and shortcuts, Implementation: navigators  --> change implementation
* Formal: no default values  --> possibly update formal definition
* Formal: Cartesian product for all operators, Implementation: only specified for [0,1] --> change typing rules and extend Java library
* Formal: lookup expression, Implementation: data section with identifiers --> dump lookup expression, possibly add data section to formalism.
