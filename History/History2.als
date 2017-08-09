module History2[Time]

abstract sig Action {
	action : set Time
}

one sig InitAction, ChangeAction, UndoAction, RedoAction extends Action {
}

one sig History {
	history : (seq Time) -> Time,
	present : Int -> Time
}

pred Init[t:Time] {
	History.history.t = 0 -> t
	History.present.t = 0	
	action.t = InitAction
}

pred Change[t,t':Time] {

	History.history.t' = ((History.history.t).subseq[0, History.present.t]).add[t']  
	History.present.t' = (History.present.t).add[1] 

	action.t' = ChangeAction

}

pred Undo[t,t':Time] {
	History.present.t > 0

	History.present.t' = (History.present.t).sub[1]

	History.history.t' = History.history.t

	action.t' = UndoAction
}

pred Redo[t,t':Time] {
	History.present.t < (#(History.history.t)).sub[1]

	History.present.t' = (History.present.t).add[1]

	History.history.t' = History.history.t

	action.t' = RedoAction
}

fun Current[t:Time] : Time {
	(History.history.t)[History.present.t]
}

run {} for 3 but 6 Time


