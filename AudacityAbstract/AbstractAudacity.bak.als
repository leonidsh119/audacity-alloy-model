open util/ordering[Time]

sig Time {}

abstract sig Action {
	_action : set Time
}

one sig InitAction, ImportAction, CutNoMoveAction, CutMoveAction, CutZoomInAction, PasteAction, ZoomInAction , ZoomOutAction extends Action {}

sig Sample { }

sig SamplesContainer {
	_samples : (seq Sample) -> Time
}

one sig Clipboard in SamplesContainer {

}

sig Track in SamplesContainer {
	_tracks : set Time,
	_window : Window
}

sig Window {
	_start : Int -> Time,
	_end : Int -> Time,
	_winsamples : (seq Sample) -> Time
}

fact {
	_window in Track one -> Window // different tracks have different windows
}

pred Always[t , t': Time, track : Track] {
	track !in Clipboard
	Clipboard !in Track
}

pred Init[t : Time] {
	no _tracks.t
	_action.t = InitAction
}

pred Import[t, t' : Time, track : Track] {
	// Precondition
	Always[t, t', track]
	track !in _tracks.t // this is a new track
	some track._samples.t // the new track is not empty
	#(track._samples.t) > 1 // minimum samples for window

	// Preserved
	_samples.t' = _samples.t

	// Updated
	_tracks.t' = _tracks.t + track
	_start.t' = _start.t ++ track._window -> 0 // Maximum zoom out
	_end.t' = _end.t ++ track._window -> (#(track._samples.t)).sub[1] // Maximum zoom out
    _winsamples.t' = _winsamples.t ++ track._window -> track._samples.t // Maximum zoom out
	_action.t' = ImportAction
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	Always[t, t', track]
	from <= to // there are at least one sample selected to cut
	track._window._start.t <= from // the first sample to cut is in the visible window
	track._window._end.t >= to // the last sample to cut is in the visible window

	// Preserved
	_tracks.t' = _tracks.t

	// Updated
	_samples.t' = _samples.t ++ (track -> cut[track._samples.t, from, to] + Clipboard -> subseq[track._samples.t, from, to])
	CutNoMove[t, t', track, from, to] or CutMove[t, t', track, from, to] or CutZoomIn[t, t', track, from, to]
}

fun cut[s : seq univ, from, to : Int] : seq univ {
	append[subseq[s, 0, from.sub[1]], subseq[s, to.add[1], (#s).sub[1]]]
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] <= #((track._samples.t).subseq[to.add[1], #(track._samples.t)]) // number for cut samples is SMALLER than number of sequences from the left of the visible winfow

	// Preserved
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	_winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t').subseq[track._window._start.t', track._window._end.t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t = CutNoMoveAction
}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > #((track._samples.t).subseq[to.add[1], #(track._samples.t)]) // number for cut samples is LARGER than number of sequences from the left of the visible winfow, but...
	to.sub[from.add[1]] <= #((track._samples.t).subseq[to.add[1], #(track._samples.t)]).add[#((track._samples.t).subseq[0, from.sub[1]])] // number for cut samples is SMALLER than number of sequences from the left AND from the right of the visible winfow, but...

	// Preserved
	_end.t' = _end.t // visible vindow is moved to the end of the track

	// Updated
	_start.t' = _start.t ++ track._window -> track._window._end.t'.sub[track._window._end.t.sub[track._window._start.t]] // moved visible window size is preserved
	_winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t').subseq[track._window._start.t', track._window._end.t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t = CutMoveAction
}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > #((track._samples.t).subseq[to.add[1], #(track._samples.t)]).add[#((track._samples.t).subseq[0, from.sub[1]])] // number for cut samples is LARGER than number of sequences from the left AND from the right of the visible winfow

	// Updated
	_start.t' = _start.t ++ track._window -> 0 // the visible window shrinking to display all the remaining samples
	_end.t' = _end.t ++ track._window -> (#(track._samples.t')) // the visible window shrinking to display all the remaining samples
	_winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t')
	_action.t = CutZoomInAction
}

pred Paste[t, t' : Time, track : Track, into : Int] {
	// Precondition
	Always[t, t', track]
	track._window._start.t <= into // the paste location is in the visible window (start)
	track._window._end.t >= into // the paste location is in the visible window (end)

	// Preserved
	_tracks.t' = _tracks.t
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	_samples.t' = _samples.t ++ (track -> paste[Clipboard._samples.t, track._samples.t, into])
    _winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t').subseq[track._window._start.t, track._window._end.t] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
	_action.t' = PasteAction
}

fun paste[origin : seq univ, dest : seq univ, pos : Int ] : seq univ 
{
	append[append[subseq[dest, 0, pos.sub[1]], origin], subseq[dest, pos, #dest]]
}

pred ZoomIn[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	Always[t, t', track]
	#(track._window._winsamples.t) > 2 // the window can shrink
	newEnd.sub[newStart] < (track._window._end.t).sub[track._window._start.t] // new window is smaller than the old one
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newStart >= track._window._start.t // new window boundaries are inside old one's (start)
	newEnd <= track._window._end.t // new window boundaries are inside old one's (end)
	newEnd.sub[newStart] > 1 // new window will have the minimum required size
	
	// Preserved
	_tracks.t' = _tracks.t
	_samples.t' = _samples.t

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
    _winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t).subseq[newStart, newEnd]
	_action.t' = ZoomInAction
}

pred ZoomOut[t , t' : Time, track : Track, newStart, newEnd : Int] {
	// Precondition
	Always[t, t', track]
	(#(track._window._winsamples.t)).sub[#(track._samples.t)]  > 0  // the window can grow
	newEnd.sub[newStart] > (track._window._end.t).sub[track._window._start.t] // new window is larger than the old one
	newStart <= track._window._start.t // new window boundaries are outside old one's (start)
	newEnd >= track._window._end.t // new window boundaries are outside old one's (end)
	newStart >= 0 // new window boundaries are inside the track's samples (start)
	newEnd < #(track._samples.t) // new window boundaries are inside the track's samples (end)
	newStart < newEnd // new window is a positive range

	// Preserved
	_tracks.t' = _tracks.t
	_samples.t' = _samples.t

	// Updated
	_start.t' = _start.t ++ track._window -> newStart
	_end.t' = _end.t ++ track._window -> newEnd
	_winsamples.t' = _winsamples.t ++ track._window -> (track._samples.t).subseq[newStart, newEnd]
	_action.t' = ZoomOutAction
}

pred Inv[t : Time] {
    // Track has at least 2 samples
	all track : _tracks.t | #(track._samples.t) > 1

	// Window's indices are in boundaries of tracks samples sequence and has at least 2 visible samples
	all track : _tracks.t |  #(track._window._winsamples.t) > 1 &&
								track._window._start.t >= 0 && 
								track._window._end.t > track._window._start.t &&
								(track._window._end.t).sub[track._window._start.t].add[1] = #(track._window._winsamples.t)

	// Window's start index is smaller than window's end index and their difference equals to the amount of visible samples
	all track : _tracks.t | track._window._end.t < #(track._samples.t)

	// All samples in window are from samples of track in the window's range
	all track : _tracks.t | track._window._winsamples.t = (track._samples.t).subseq[track._window._start.t, track._window._end.t]
}

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		some track : Track, i, j : Int |
			Import[t, t', track]
			or Cut[t, t', track, i, j]
			or Paste[t, t', track, i]
			or ZoomIn[t, t', track, i, j]
			or ZoomOut[t, t', track, i, j]
}

run { 
} for 3 but 5 Time

check {
	all t : Time | Inv[t]
} for 4
// for 3 but 4 Int, 4 Time, 4 Sample, 4 Track, 4 Window, 4 Action
