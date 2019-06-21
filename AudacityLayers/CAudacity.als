module ConcreteAudacity

open Time
open History
open BFContainer


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Window extends BFContainer {
	_start : Int -> Time,
	_end : Int -> Time
}

sig Track extends BFContainer {
	_tracks : set Time,
	_window : Window
}

fact {
	_window in Track one -> Window // TODO: Add to sig Track
}

one sig Clipboard extends BFContainer {}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[t : Time] {
    // Track has at least 2 samples
	all track : _tracks.t | countAllSamples[track, t] > 1

	// Window's indices are in boundaries of tracks samples sequence and has at least 2 visible samples
	all track : _tracks.t |  track._window._start.t >= 0 && 
								 track._window._end.t < countAllSamples[track, t] &&
								track._window._end.t > track._window._start.t &&
								(track._window._end.t).sub[track._window._start.t].add[1] = countAllSamples[track._window, t]

	// All samples in window are from samples of track in the window's range
	all track : _tracks.t | readAllSamples[track._window, t] = readSamples[track, track._window._start.t, track._window._end.t, t]
}

pred Init[t : Time] {
	no _tracks.t
	countAllSamples[Clipboard, t] = 0
	no Clipboard._blocks.t
	_action.t = InitAction
}

pred Import[t, t' : Time, track : Track] {
	// Concrete Precondition
	all block : BlockFile | block in Int.(track._blocks.t) => some block._samples

	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	countAllSamples[track, t] > 1 // the new track is not empty. Asumming at least 2 samples for being able to define a window

	// Preserved
	all cont : _id.ID - track._window | readAllSamples[cont, t'] = readAllSamples[cont, t]

	// Updated
	_tracks.t' = _tracks.t + track
	_start.t' = _start.t ++ track._window -> 0 // Maximum zoom out
	_end.t' = _end.t ++ track._window -> lastContSampleIdx[track, t] // Maximum zoom out
	readAllSamples[track._window, t'] = readAllSamples[track, t] // Maximum zoom out
	_action.t' = ImportAction
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
	// Concrete Precondition
	let firstCutBlockIndex = blockIndexForSampleIndex[track, from, t],  lastCutBlockIndex = blockIndexForSampleIndex[track, to, t] | {
		all block : track._blocks.t[Int] | #(block._samples) > 0
		sampleIndexInBlockForSampleIndex[track, from, t] = 0 // "from" is the first sample in its block
		sampleIndexInBlockForSampleIndex[track, to, t] = sub[#(blockForBlockIndex[track, lastCutBlockIndex, t]._samples), 1] // "to" is the last sample in its block
		countAllBlocks[Clipboard, t] = sub[lastCutBlockIndex, firstCutBlockIndex] // required number of blocks in clipboard. what skip action achieves that?
	}

	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	from >= 0
	to >= from // there are at least one sample selected to cut
	to <= countAllSamples[track, t]
	track._window._start.t <= from // the first sample to cut is in the visible window
	track._window._end.t >= to // the last sample to cut is in the visible window
	to.sub[from].add[1] <= countAllSamples[track, t].sub[2] // don't leave the track without at least 2 samples

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack._window, t'] = readAllSamples[otherTrack._window, t]

	// Handle different cases
	CutNoMove[t, t', track, from, to] or CutMove[t, t', track, from, to] or CutZoomIn[t, t', track, from, to]

	// Updated
	readSamples[track, 0, from.sub[1], t'] = readSamples[track, 0, from.sub[1], t]
	readAllSamples[Clipboard, t'] = readSamples[track, from, to, t]
	readSamples[track, from, lastContSampleIdx[track, t'], t'] = readSamples[track, to.add[1], lastContSampleIdx[track, t], t]
	readAllSamples[track._window, t'] = readSamples[track, track._window._start.t', track._window._end.t', t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] <= countSamples[track, track._window._end.t, countAllSamples[track, t].sub[1], t].sub[1] // number for cut samples is SMALLER than number of samples from the left of the visible winfow

	// Preserved
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	_action.t' = CutNoMoveAction
}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] > countSamples[track, track._window._end.t, countAllSamples[track, t].sub[1], t].sub[1] // number for cut samples is LARGER than number of samples from the left of the visible winfow, but...
	to.sub[from].add[1] <= countSamples[track, track._window._end.t, countAllSamples[track, t].sub[1], t].sub[1].add[countSamples[track, 0, track._window._start.t, t]].sub[1] // number for cut samples is SMALLER than number of sequences from the left AND from the right of the visible winfow, but...

	// Updated
	_start.t' = _start.t ++ track._window -> track._window._end.t'.sub[track._window._end.t.sub[track._window._start.t]] // moved visible window size is preserved
	_end.t' = _end.t ++ track._window -> countAllSamples[track, t'].sub[1] // visible vindow is moved to the end of the track
	_action.t' = CutMoveAction
}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from].add[1] > countSamples[track, track._window._end.t, countAllSamples[track, t], t].sub[1].add[countSamples[track, 0, track._window._start.t, t]].sub[1] // number for cut samples is LARGER than number of sequences from the left AND from the right of the visible winfow

	// Updated
	_start.t' = _start.t ++ track._window -> 0 // the visible window shrinking to display all the remaining samples
	_end.t' = _end.t ++ track._window -> countAllSamples[track, t'].sub[1] // the visible window shrinking to display all the remaining samples
	_action.t' = CutZoomInAction
}

pred Paste[t, t' : Time, track : Track, into : Int] {
	// Concrete Precondition
	let firstEmptyBlockIndex = add[blockIndexForSampleIndex[track, sub[into, 1], t], 1],  lastEmptyBlockIndex = add[firstEmptyBlockIndex, countAllBlocks[Clipboard, t]] | {
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) = 0
		all i : range[0, countAllBlocks[track, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) > 0
	}

	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	track._window._start.t <= into // the paste location is in the visible window (start)
	track._window._end.t >= into // the paste location is in the visible window (end)

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack._window, t'] = readAllSamples[otherTrack._window, t]
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	readSamples[track, 0, into.sub[1], t'] = readSamples[track, 0, into.sub[1], t]
	readSamples[track, into, into.add[countAllSamples[Clipboard, t]].sub[1], t'] = readAllSamples[Clipboard, t]
	readSamples[track, into.add[countAllSamples[Clipboard, t]], lastContSampleIdx[track, t'], t'] = readSamples[track, into, lastContSampleIdx[track, t], t]
	readAllSamples[track._window, t'] = readSamples[track, track._window._start.t, track._window._end.t, t'] // Refresh displayed samples according to the remaining window start and end
	_action.t' = PasteAction
}

pred Split[cont : BFContainer, blockIdx : Int, head, tail : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	(#(head._samples)).add[#(tail._samples)] > 1

	let block = blockForBlockIndex[cont, blockIdx, t] | {
		// Precondition
		block._samples = append[head._samples, tail._samples]

		// Preserved
		all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
		_tracks.t' = _tracks.t

		// Updated
		_blocks.t' = _blocks.t ++ cont -> insert[insert[cont._blocks.t, blockIdx, tail], blockIdx, head]
	}
	_action.t = SplitAction
}

pred Insert[cont : BFContainer, blockIdx : Int, emptyBlock : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(emptyBlock._samples) = 0

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> insert[cont._blocks.t, blockIdx, emptyBlock]
	_action.t = InsertAction
}

pred Delete[cont : BFContainer, blockIdx : Int, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(blockForBlockIndex[cont, blockIdx, t]._samples) = 0

	// Preserved
	all bfc : BFContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> delete[cont._blocks.t, blockIdx]
	_action.t = DeleteAction
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		some track : Track, i, j : Int |
			Import[t, t', track]
			or Cut[t, t', track, i, j]
			or Paste[t, t', track, i]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

run { 
	#(BlockFile._samples) >= 2
} for 3 but 3 Time, 4 Int

check {
	all t : Time | Inv[t]
} for 3 but 2 Track, 2 Sample, 2 Window, 5 seq, 5 Time, 4 Int
