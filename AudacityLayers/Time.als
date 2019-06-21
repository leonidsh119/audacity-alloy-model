module Time

open util/ordering[Time]


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Time {}

abstract sig Action {
	_action : set Time
}

one sig InitAction, ImportAction, CutNoMoveAction, CutMoveAction, CutZoomInAction, PasteAction, ZoomInAction , ZoomOutAction, PreserveAction, UndoAction, RedoAction, SplitAction, InsertAction, DeleteAction extends Action {}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred SetAction[action : Action, t : Time] {
	_action.t = action
}
