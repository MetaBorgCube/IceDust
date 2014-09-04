# Create Update and Delete (multiplicity-safe)
How to possibly reach invalid multiplicities, and how to repair those states.

## Entity
### Create
Invalid multiplicity is *always* reached by:

* If entity is participant (has inverse) in a relation with [1,1] or [1,n), violating lower bound
	* Add a new relation
	* Or, change the participant of existing relation to this new entity

### Delete
Invalid multiplicity *might* be reached by:

* If entity is participant (has inverse) in a relation with [0,1] *might*, [0,n) *might*, [1,1] *always* or [1,n) *always*, violating that a role must always be set in a relation
	* Delete relations
	* Or, change participant of existing relation to another entity
	* Or, abort

### Update (attributes)
No invalid multiplicity reachable

## Relation
### Create
Invalid multiplicity *might* be reached by:

* Any role with [0,1] *might* or [1,1] *always*, violating upper bound
	* Delete other relation
	* Or, abort

### Delete
Invalid multiplicity *might* be reached by:

* Any role with [1,1] *always* or [1,n) *might*, violating lower bound
	* Delete entity
	* Or, add another relation
	* Or, change another relation to have the entity as participant
	* Or, abort

### Update (attributes)
No invalid multiplicity reachable

### Update (roles)
Invalid multiplicity *might* be reached by

* New participating entity in role: Any role with [0,1] *might* or [1,1] *always*, violating upper bound
	* Delete other relations
	* Or, abort
* Old participating entity in role: Any role with [1,1] *always* or [1,n) *might*, violating lower bound
	* Delete entity
	* Or, add another relation
	* Or, change another relation to have the entity as participant
	* Or, abort