module BFAudacity

open Time
open BlockFile
open BFContainer
open BFWindow
open History


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

one sig Clipboard extends BFContainer {
}

sig Track extends BFContainer {
	_tracks : set Time,
	_window : Window
}

fact {
	_window in Track one -> Window // TODO: Add to sig Track
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[t : Time] {
	all track : _tracks.t | 
		BFContainer/Inv[track, t] &&
		BFWindow/Inv[track._window, t] &&
		getEnd[track._window, t] < countAllSamples[track, t] &&
		readAllSamples[track._window, t] = readSamples[track, getStart[track._window, t], getEnd[track._window, t], t] // All samples in window are from samples of track in the window's range
	this/Equiv[t, current[t]]
}

pred Init[t : Time] {
	no _tracks.t
	BFContainer/Init[Clipboard, t]
	History/Init[t]
	SetAction[InitAction, t]
}

pred Equiv[t1 : Time, t2 : Time] {
	_tracks.t1 = _tracks.t2
	BFContainer/Equiv[Clipboard, t1, t2]
	all track : _tracks.t1 |
		BFContainer/Equiv[track, t1, t2] &&
		BFWindow/Equiv[track._window, t1, t2]
	// NOTE: No History/Equiv[] is here, to allow the Audacyty state to be the same in t1 and t2, but different appeearences in Undo/Redo stack
}

pred Import[t, t' : Time, track : Track] {
	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	BFContainer/Inv[track, t]
	BFWindow/Inv[track._window, t]

	// Preserved
	BFContainer/Equiv[Clipboard, t, t']
	BFContainer/Equiv[track, t, t']
	all otherTrack : _tracks.t | 
		BFContainer/Equiv[otherTrack, t, t'] &&
		BFWindow/Equiv[otherTrack._window, t, t']

	// Updated
	_tracks.t' = _tracks.t + track
	SetWindow[track._window, 0, lastContSampleIdx[track, t], readAllSamples[track, t], t']
	History/Advance[t, t']
	SetAction[ImportAction, t']
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] <= countSamples[track, getEnd[track._window, t], countAllSamples[track, t].sub[1], t].sub[1] // number for cut samples is SMALLER than number of samples from the left of the visible winfow

	// Updated
	SetWindow[
		track._window, 
		getStart[track._window, t], // Window Start preserved
		getEnd[track._window, t], // Window End preserved
		readSamples[track, getStart[track._window, t'], getEnd[track._window, t'], t'],  // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
		t']
	SetAction[CutNoMoveAction, t']
}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] > countSamples[track, getEnd[track._window, t], countAllSamples[track, t].sub[1], t].sub[1] // number for cut samples is LARGER than number of samples from the left of the visible winfow, but...
	to.sub[from].add[1] <= countSamples[track, getEnd[track._window, t], countAllSamples[track, t].sub[1], t].sub[1].add[countSamples[track, 0, getStart[track._window, t], t]].sub[1] // number for cut samples is SMALLER than number of sequences from the left AND from the right of the visible winfow, but...

	// Updated
	SetWindow[
		track._window, 
		getEnd[track._window, t'].sub[getEnd[track._window, t].sub[getStart[track._window, t]]], // moved visible window size is preserved
		countAllSamples[track, t'].sub[1], // visible vindow is moved to the end of the track
		readSamples[track, getStart[track._window, t'], getEnd[track._window, t'], t'],  // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
		t']
	SetAction[CutMoveAction, t']
}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] > countSamples[track, getEnd[track._window, t], countAllSamples[track, t], t].sub[1].add[countSamples[track, 0, getStart[track._window, t], t]].sub[1] // number for cut samples is LARGER than number of sequences from the left AND from the right of the visible winfow

	// Updated
	SetWindow[
		track._window, 
		0, // the visible window shrinking to display all the remaining samples
		countAllSamples[track, t'].sub[1], // the visible window shrinking to display all the remaining samples
		readSamples[track, getStart[track._window, t'], getEnd[track._window, t'], t'],  // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
		t']
	SetAction[CutZoomInAction, t']
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	from >= 0
	to >= from // there are at least one sample selected to cut
	to <= countAllSamples[track, t]
	to.sub[from].add[1] <= countAllSamples[track, t].sub[2] // don't leave the track without at least 2 samples
	IsRangeDisplayed[track._window, from, to, t]

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t | 
		BFContainer/Equiv[otherTrack, t, t'] &&
		BFWindow/Equiv[otherTrack._window, t, t']

	// Updated
	readSamples[track, 0, from.sub[1], t'] = readSamples[track, 0, from.sub[1], t]
	readAllSamples[Clipboard, t'] = readSamples[track, from, to, t]
	readSamples[track, from, lastContSampleIdx[track, t'], t'] = readSamples[track, to.add[1], lastContSampleIdx[track, t], t]
	CutNoMove[t, t', track, from, to] or CutMove[t, t', track, from, to] or CutZoomIn[t, t', track, from, to]
	History/Advance[t, t']
}

pred Paste[t, t' : Time, track : Track, into : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	!BFContainer/Empty[Clipboard, t]
	IsRangeDisplayed[track._window, into, into, t]

	// Preserved
	_tracks.t' = _tracks.t
	BFContainer/Equiv[Clipboard, t, t']
	all otherTrack : _tracks.t - track | 
		BFContainer/Equiv[otherTrack, t, t'] &&
		BFWindow/Equiv[otherTrack._window, t, t']

	// Updated
	InsertSamples[track, Clipboard, into, t, t']
	SetWindow[
		track._window, 
		getStart[track._window, t], 
		getEnd[track._window, t], 
		readSamples[track, getStart[track._window, t], getEnd[track._window, t], t'], 
		t']
	History/Advance[t, t']
	SetAction[PasteAction, t']
}

pred ZoomIn[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	CanZoomIn[track._window, newStart, newEnd, t]
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newEnd.sub[newStart] > 1 // new window will have the minimum required size
	
	// Preserved
	_tracks.t' = _tracks.t
	BFContainer/Equiv[Clipboard, t, t']
	BFContainer/Equiv[track, t, t']
	all otherTrack : _tracks.t - track | 
		BFContainer/Equiv[otherTrack, t, t'] &&
		BFWindow/Equiv[otherTrack._window, t, t']

	// Updated
	SetWindow[track._window, newStart, newEnd, readSamples[track, newStart, newEnd, t], t']
	History/Advance[t, t']
	SetAction[ZoomInAction, t']
}

pred ZoomOut[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	CanZoomOut[track._window, newStart, newEnd, t]
	countAllSamples[track, t] > countAllSamples[track._window, t] // the window can grow
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newEnd < countAllSamples[track, t] // new window boundaries are inside the track's samples (end)
	newStart < newEnd // new window is a positive range

	// Preserved
	_tracks.t' = _tracks.t
	BFContainer/Equiv[Clipboard, t, t']
	BFContainer/Equiv[track, t, t']
	all otherTrack : _tracks.t - track | 
		BFContainer/Equiv[otherTrack, t, t'] &&
		BFWindow/Equiv[otherTrack._window, t, t']

	// Updated
	SetWindow[track._window, newStart, newEnd, readSamples[track, newStart, newEnd, t], t']
	History/Advance[t, t']
	SetAction[ZoomInAction, t']
}

pred Preserve[t, t' : Time] {
	this/Equiv[t, t']
	History/Equiv[t, t']
	SetAction[PreserveAction, t']
}

pred Split[cont : BFContainer, blockIdx : Int, head, tail : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	(BlockFile/countSamples[head]).add[BlockFile/countSamples[tail]] > 1

	let block = blockForBlockIndex[cont, blockIdx, t] | {
		// Precondition
		BlockFile/Merge[block, head, tail]

		// Preserved
		all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
		_tracks.t' = _tracks.t

		// Updated
		_blocks.t' = _blocks.t ++ cont -> insert[insert[cont._blocks.t, blockIdx, tail], blockIdx, head]
	}
	History/Equiv[t, t']
	SetAction[SplitAction, t']
}

pred Insert[cont : BFContainer, blockIdx : Int, emptyBlock : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	BlockFile/Empty[emptyBlock]

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> insert[cont._blocks.t, blockIdx, emptyBlock]
	History/Equiv[t, t']
	SetAction[InsertAction, t']
}

pred Delete[cont : BFContainer, blockIdx : Int, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	BlockFile/Empty[blockForBlockIndex[cont, blockIdx, t]]

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> delete[cont._blocks.t, blockIdx]
	History/Equiv[t, t']
	SetAction[DeleteAction, t']
}

pred Undo[t, t' : Time] {
	History/Undo[t, t']
	this/Equiv[t', current[t']]
	SetAction[UndoAction, t']
}

pred Redo[t, t' : Time] {
	History/Redo[t, t']
	this/Equiv[t', current[t']]
	SetAction[RedoAction, t']
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	this/Init[first]
	all t, t' : Time | t -> t' in next implies 
		some track : Track, i, j : Int |
			Import[t, t', track]
			or Cut[t, t', track, i, j]
			or Paste[t, t', track, i]
			or ZoomIn[t, t', track, i, j]
			or ZoomOut[t, t', track, i, j]
		or this/Undo[t, t'] 
		or this/Redo[t, t']
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

run { 
	#(BlockFile._samples) >= 2
} for 3 but 3 Time, 4 Int

check {
	all t : Time | Inv[t]
} for 3 but 2 Track, 2 Sample, 2 Window, 3 seq, 3 Time, 4 Int
