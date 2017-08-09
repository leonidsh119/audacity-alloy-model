
module System

open util/ordering[Time]
open History2[Time]

sig Time {
}

sig Value {
	selected: set Time
}

pred Init[t:Time] {
	one selected.t
}

pred Set[t,t':Time, newValue:Value] {
	selected.t != newValue
	selected.t' = newValue
}

/* 

An equivalence predicate on the system's state that is used to enable cooperation with undo mechanism.

To understand how this mechanism operates we must make a distinction between the problem domain state variables 
(that represent the state of the problem domain entities), and the history state variables.

When we undo a system oepration we don't roll back to an actual previous system state, because the history state 
variables must change. But we must move to a system state that is equivalent to the previous system state in that 
the problem domain state variables in both states must be equal.

This predicate is the only place that needs to change if we add or modify the normal state variables. 

*/


pred Equiv[t1:Time, t2:Time] {
	selected.t1 = selected.t2
}

// System level operations (original system + undo mechanism)

pred System_Init[t:Time] {
	this/Init[t]
	History2/Init[t]
}

pred System_Set[t,t':Time, newValue: Value] {
	Set[t,t',newValue] 
	History2/Change[t, t']
}

pred System_Undo[t,t':Time] {
		History2/Undo[t,t']	
		Equiv[t', History2/Current[t']]
}

pred System_Redo[t,t':Time] {
		History2/Redo[t,t']	
		Equiv[t', History2/Current[t']]
}

pred System_Inv[t:Time] {
		Equiv[t, History2/Current[t]]
}

check {
	all t : Time | System_Inv[t]
} for 3 but 6 seq, 6 Time

fact {
	System_Init[first]
	all t,t':Time | 
		t->t' in next => some newValue: Value | 
			System_Set[t,t',newValue]  or System_Undo[t,t'] or System_Redo[t,t']
}

run {} for 3 but 6 Time
