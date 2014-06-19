# TODO:

* Implement inverses with partial classes (in a different name space)
* Implement shortcuts with desugarings

# Differences between formal specification and implementation

* Formal: inverses and shortcuts, Implementation: navigators
* Formal: no default values
* Formal: Cartesian product for all operators, Implementation: only specified for [0,1]
* Formal: lookup expression, Implementation: data section with identifiers

Issues

* The collection operations are based on sets, but taking the average of grades, where the grades are a set of values (without duplicates) gives the wrong average
