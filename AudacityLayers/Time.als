module Time

open util/ordering[Time]


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Time {}

abstract sig Action {
	_action : set Time
}

one sig InitAction, ImportAction, CutNoMoveAction, CutMoveAction, CutZoomInAction, PasteAction, ZoomInAction , ZoomOutAction, UndoAction, RedoAction, SkipAction, SplitAction, InsertAction, DeleteAction extends Action {}
