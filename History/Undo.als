/*

a simple undo/redo mechanism

the ordering of the time objects represents the entire history and future of the system. 

time	T$0	T$1	T$2	T$3, ... , T$N
x			0		1		2		3

suppose we apply an undo operation at time T$3. The effect is that the state variables will now take the same
values as they had at time T$2. 

pred Undo[t,t': Time] {
	t != first
	
	x.t' = x.(t.prev)
	...
}

so now at T$4 the value of x is 2. If we perform undo again the vlaue of x must be as it was at T$1 

time	T$0	T$1	T$2	T$3	T$4 T$5
x			0		1		2		3		2		1

but this is not what will happen in our simple implementation. instead the second undo will undo the effect
of the first undo.

instead we have to keep track of the 'present' by keeping track of the history in a separate relation

time 		T$0		T$1				T$2						T$3
x				0			1					2							3
history	T$0		T$0,T$1		T$0,T$1,T$2		T$0,T$1,T$2,T$3
present ^					^							^									^

now when we undo at T$4 we move 'present' back one place in the history

time 		T$0		T$1				T$2						T$3								T$4
x				0			1					2							3									2
history	T$0		T$0,T$1		T$0,T$1,T$2		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3
present ^					^							^									^							^

and another undo moves present to T$2 

time 		T$0		T$1				T$2						T$3								T$4								T$5
x				0			1					2							3									2									1
history	T$0		T$0,T$1		T$0,T$1,T$2		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3
present ^					^							^									^							^							^

if we 'redo' then move forward in the history

time 		T$0		T$1				T$2						T$3								T$4								T$5								T$6
x				0			1					2							3									2									1									2
history	T$0		T$0,T$1		T$0,T$1,T$2		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3
present ^					^							^									^							^							^											^

now when we perform a 'real' operation we cut the rest of the history and add the next moment in time

time 		T$0		T$1				T$2						T$3								T$4								T$5								T$6								T$7
x				0			1					2							3									2									1									2									7
history	T$0		T$0,T$1		T$0,T$1,T$2		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$3		T$0,T$1,T$2,T$7
present ^					^							^									^							^							^											^											^

*/

open util/ordering[Time]

abstract sig Action {
	action : set Time // Only set, when used?
}

one sig InitAction, ChangeAction, UndoAction, RedoAction extends Action {
}

sig Data {
	data : set Time
}

sig Time {}

one sig History {
	history : (seq Time) -> Time,
	present : Int -> Time
}

pred Init[t : Time] {
	one data.t
	History.history.t = 0 -> first
	History.present.t = 0	
	action.t = InitAction
}

pred Change[t, t' : Time,  newData : Data] {
	newData != data.t
	data.t' = newData
	History.history.t' = ((History.history.t).subseq[0, History.present.t]).add[t']  
	History.present.t' = (History.present.t).add[1] 
	action.t' = ChangeAction
}

pred Undo[t, t' : Time] {
	History.present.t > 0
	History.present.t' = (History.present.t).sub[1]
	data.t' = data.((History.history.t)[History.present.t'])
	History.history.t' = History.history.t
	action.t' = UndoAction
}

pred Redo[t, t' : Time] {
	History.present.t < (#(History.history.t)).sub[1]
	History.present.t' = (History.present.t).add[1]
	data.t' = data.((History.history.t)[History.present.t'])
	History.history.t' = History.history.t
	action.t' = RedoAction
}

pred Inv[t : Time] {
	data.t = data.((History.history.t)[History.present.t])
}

fact {
	Init[first]
}

fact {
	all t, t' : Time | t->t' in next => some newData : Data | Change[t, t', newData] or Undo[t, t'] or Redo[t, t']
}

run {} for 3 but 6 Time

check { all t : Time | Inv[t] } for 3 but 5 int, 8 Time, 8 seq


