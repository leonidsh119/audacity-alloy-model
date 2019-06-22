module History

open Time


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

one sig History {
	_history : (seq Time) -> Time,
	_present : Int -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred InitHistory[t : Time] {
	History._history.t = 0 -> t
	History._present.t = 0
}

pred AdvanceHistory[t, t' : Time] {
	History._history.t' = ((History._history.t).subseq[0, History._present.t]).add[t']  
	History._present.t' = (History._present.t).add[1] 
}

pred PreserveHistory[t, t' : Time] {
	_history.t' = _history.t
	_present.t' = _present.t
}

pred UndoHistory[t, t' : Time] {
	History._present.t > 0
	History._history.t' = History._history.t
	History._present.t' = (History._present.t).sub[1]
}

pred RedoHistory[t, t' : Time] {
	History._present.t < (#(History._history.t)).sub[1]
	History._history.t' = History._history.t
	History._present.t' = (History._present.t).add[1]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun current[t : Time] : Time {
	(History._history.t)[History._present.t]
}
