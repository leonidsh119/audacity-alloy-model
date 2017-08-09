module AbstractAudacity

open CommonAudacity
open util/ordering[Time]

////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Time {}

abstract sig Action {
	_action : set Time
}

one sig InitAction, ImportAction, CutNoMoveAction, CutMoveAction, CutZoomInAction, PasteAction, ZoomInAction , ZoomOutAction, UndoAction, RedoAction, SkipAction extends Action {}

abstract sig SamplesContainer {
	_id : ID,
	_samples : (seq Sample) -> Time
}

one sig Clipboard extends SamplesContainer {

}

sig Track extends SamplesContainer {
	_tracks : set Time,
	_window : Window
}

sig Window {
	_start : Int -> Time,
	_end : Int -> Time,
	_winsamples : (seq Sample) -> Time
}

one sig History {
	_history : (seq Time) -> Time,
	_present : Int -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Equiv[t1 : Time, t2 : Time] {
	all cont : SamplesContainer | readAllSamples[cont, t1] = readAllSamples[cont, t2]
	_tracks.t1 = _tracks.t2
	_start.t1 = _start.t2
	_end.t1 = _end.t2
	_winsamples.t1 = _winsamples.t2
}

pred ChangeHistory[t, t' : Time] {
	History._history.t' = ((History._history.t).subseq[0, History._present.t]).add[t']  
	History._present.t' = (History._present.t).add[1] 
}

pred Import[t, t' : Time, track : Track] {
	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	countAllSamples[track, t] > 1 // the new track is not empty. Asumming at least 2 samples for being able to define a window

	// Preserved
	all cont : SamplesContainer | readAllSamples[cont, t'] = readAllSamples[cont, t]

	// Updated
	_tracks.t' = _tracks.t + track
	_start.t' = _start.t ++ track._window -> 0 // Maximum zoom out
	_end.t' = _end.t ++ track._window -> lastContSampleIdx[track, t] // Maximum zoom out
    _winsamples.t' = _winsamples.t ++ track._window -> readAllSamples[track, t] // Maximum zoom out
	_action.t' = ImportAction
	ChangeHistory[t, t']
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	from <= to // there are at least one sample selected to cut
	track._window._start.t <= from // the first sample to cut is in the visible window
	track._window._end.t >= to // the last sample to cut is in the visible window

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]

	// Updated
	readSamples[track, 0, from.sub[1], t'] = readSamples[track, 0, from.sub[1], t]
	readAllSamples[Clipboard, t'] = readSamples[track, from, to, t]
	readSamples[track, from, lastContSampleIdx[track, t'], t'] = readSamples[track, to.add[1], lastContSampleIdx[track, t], t]
	CutNoMove[t, t', track, from, to] or CutMove[t, t', track, from, to] or CutZoomIn[t, t', track, from, to]
	ChangeHistory[t, t']
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] <= #readSamples[track, to.add[1], countAllSamples[track, t], t] // number for cut samples is SMALLER than number of sequences from the left of the visible winfow

	// Preserved
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, track._window._start.t', track._window._end.t', t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t = CutNoMoveAction
}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > #readSamples[track, to.add[1], countAllSamples[track, t], t] // number for cut samples is LARGER than number of sequences from the left of the visible winfow, but...
	to.sub[from.add[1]] <= #readSamples[track, to.add[1], countAllSamples[track, t], t].add[#readSamples[track, 0, from.sub[1], t]] // number for cut samples is SMALLER than number of sequences from the left AND from the right of the visible winfow, but...

	// Preserved
	_end.t' = _end.t // visible vindow is moved to the end of the track

	// Updated
	_start.t' = _start.t ++ track._window -> track._window._end.t'.sub[track._window._end.t.sub[track._window._start.t]] // moved visible window size is preserved
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, track._window._start.t', track._window._end.t', t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t = CutMoveAction
}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > #readSamples[track, to.add[1], countAllSamples[track, t], t].add[#readSamples[track, 0, from.sub[1], t]] // number for cut samples is LARGER than number of sequences from the left AND from the right of the visible winfow

	// Updated
	_start.t' = _start.t ++ track._window -> 0 // the visible window shrinking to display all the remaining samples
	_end.t' = _end.t ++ track._window -> countAllSamples[track, t'] // the visible window shrinking to display all the remaining samples
	_winsamples.t' = _winsamples.t ++ track._window -> readAllSamples[track, t']
	_action.t = CutZoomInAction
}

pred Paste[t, t' : Time, track : Track, into : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	track._window._start.t <= into // the paste location is in the visible window (start)
	track._window._end.t >= into // the paste location is in the visible window (end)

	// Preserved
	_tracks.t' = _tracks.t
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]

	// Updated
	readSamples[track, 0, into.sub[1], t'] = readSamples[track, 0, into.sub[1], t]
	readSamples[track, into, into.add[countAllSamples[Clipboard, t]].sub[1], t'] = readAllSamples[Clipboard, t]
	readSamples[track, into.add[countAllSamples[Clipboard, t]], lastContSampleIdx[track, t'], t'] = readSamples[track, into, lastContSampleIdx[track, t], t]
    _winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, track._window._start.t, track._window._end.t, t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t' = PasteAction
	ChangeHistory[t, t']
}

pred ZoomIn[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	#(track._window._winsamples.t) > 2 // the window can shrink
	newEnd.sub[newStart] < (track._window._end.t).sub[track._window._start.t] // new window is smaller than the old one
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newStart >= track._window._start.t // new window boundaries are inside old one's (start)
	newEnd <= track._window._end.t // new window boundaries are inside old one's (end)
	newEnd.sub[newStart] > 1 // new window will have the minimum required size
	
	// Preserved
	_tracks.t' = _tracks.t
	all cont : SamplesContainer | readAllSamples[cont, t'] = readAllSamples[cont, t]

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
    _winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, newStart, newEnd, t]
	_action.t' = ZoomInAction
	ChangeHistory[t, t']
}

pred ZoomOut[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	(#(track._window._winsamples.t)).sub[countAllSamples[track, t]]  > 0  // the window can grow
	newEnd.sub[newStart] > (track._window._end.t).sub[track._window._start.t] // new window is larger than the old one
	newStart <= track._window._start.t // new window boundaries are outside old one's (start)
	newEnd >= track._window._end.t // new window boundaries are outside old one's (end)
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newEnd < countAllSamples[track, t] // new window boundaries are inside the track's samples (end)
	newStart < newEnd // new window is a positive range

	// Preserved
	_tracks.t' = _tracks.t
	all cont : SamplesContainer | readAllSamples[cont, t'] = readAllSamples[cont, t]

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, newStart, newEnd, t]
	_action.t' = ZoomOutAction
	ChangeHistory[t, t']
}

pred Undo[t, t' : Time] {
	// Precondition
	History._present.t > 0

	// Preserved
	History._history.t' = History._history.t

	// Updated
	History._present.t' = (History._present.t).sub[1]
	Equiv[t', current[t']]
	_action.t' = UndoAction
}

pred Redo[t, t' : Time] {
	// Precondition
	History._present.t < (#(History._history.t)).sub[1]

	// Preserved
	History._history.t' = History._history.t

	// Updated
	History._present.t' = (History._present.t).add[1]
	Equiv[t', current[t']]
	_action.t' = RedoAction
}

// Represents a state preservation betweent to times
pred Skip[t, t' : Time] {
	all cont : SamplesContainer | readAllSamples[cont, t] = readAllSamples[cont, t']
	_tracks.t' = _tracks.t
	_start.t' = _start.t
	_end.t' = _end.t
	_winsamples.t' = _winsamples.t
	_history.t' = _history.t
	_present.t' = _present.t
	_action.t' = SkipAction
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                         Invariant Predicates                                     //
////////////////////////////////////////////////////////////////////////////////////////////

pred Init[t : Time] {
	no _tracks.t
	countAllSamples[Clipboard, t] = 0
	History._history.t = 0 -> t
	History._present.t = 0	
	_action.t = InitAction
}

pred Inv[t : Time] {
    // Track has at least 2 samples
	all track : _tracks.t | countAllSamples[track, t] > 1

	// Window's indices are in boundaries of tracks samples sequence and has at least 2 visible samples
	all track : _tracks.t |  #(track._window._winsamples.t) > 1 &&
								track._window._start.t >= 0 && 
								track._window._end.t > track._window._start.t &&
								(track._window._end.t).sub[track._window._start.t].add[1] = #(track._window._winsamples.t)

	// Window's start index is smaller than window's end index and their difference equals to the amount of visible samples
	all track : _tracks.t | track._window._end.t < countAllSamples[track, t]

	// All samples in window are from samples of track in the window's range
	all track : _tracks.t | track._window._winsamples.t = readSamples[track, track._window._start.t, track._window._end.t, t]

	// Validate history 
	Equiv[t, current[t]]
}

pred SystemOperation[t, t' : Time] {
		some track : Track, i, j : Int |
			Import[t, t', track]
			or Cut[t, t', track, i, j]
			or Paste[t, t', track, i]
			or ZoomIn[t, t', track, i, j]
			or ZoomOut[t, t', track, i, j]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun readAllSamples[cont : SamplesContainer, t : Time] : seq Sample {
	cont._samples.t
}

fun readSamples[cont : SamplesContainer, from, to : Int, t : Time] : seq Sample {
	subseq[cont._samples.t, from, to]
}

fun lastContSampleIdx[cont : SamplesContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

fun countAllSamples[cont : SamplesContainer, t : Time] : Int {
	#(cont._samples.t)
}

fun countSamples[cont : SamplesContainer, from, to : Int, t : Time] : Int {
	#subseq[cont._samples.t, from, to]
}

fun current[t : Time] : Time {
	(History._history.t)[History._present.t]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	_window in Track one -> Window // different tracks have different windows
	_id in SamplesContainer lone -> ID // id is unique identifier of SamplesContainer.
}

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		(SystemOperation[t, t'] and ChangeHistory[t, t']) 
		or Undo[t, t'] 
		or Redo[t, t']
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

run { 
} for 3 but 5 Time

check {
	all t : Time | Inv[t]
} for 3 but 2 Track, 2 Sample, 2 Window, 5 seq, 5 Time
// for 3 but 4 Int, 4 Time, 4 Sample, 4 Track, 4 Window, 4 Action
