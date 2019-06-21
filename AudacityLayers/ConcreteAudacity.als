module ConcreteAudacity

open Common
open Time
open History

let MAX_BLOCK_SIZE = 4


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig BlockFile {
	_samples : seq Sample
} { #_samples <= MAX_BLOCK_SIZE }

abstract sig BlockFileContainer {
	_id : ID,
	_blocks : (seq BlockFile) -> Time
}

sig Track extends BlockFileContainer {
	_tracks : set Time,
	_window : Window
}

sig Window extends BlockFileContainer {
	_start : Int -> Time,
	_end : Int -> Time
}

one sig Clipboard extends BlockFileContainer {}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

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

pred Split[cont : BlockFileContainer, blockIdx : Int, head, tail : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	(#(head._samples)).add[#(tail._samples)] > 1

	let block = blockForBlockIndex[cont, blockIdx, t] | {
		// Precondition
		block._samples = append[head._samples, tail._samples]

		// Preserved
		all bfc : BlockFileContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
		_tracks.t' = _tracks.t

		// Updated
		_blocks.t' = _blocks.t ++ cont -> insert[insert[cont._blocks.t, blockIdx, tail], blockIdx, head]
	}
	_action.t = SplitAction
}

pred Insert[cont : BlockFileContainer, blockIdx : Int, emptyBlock : BlockFile, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(emptyBlock._samples) = 0

	// Preserved
	all bfc : BlockFileContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> insert[cont._blocks.t, blockIdx, emptyBlock]
	_action.t = InsertAction
}

pred Delete[cont : BlockFileContainer, blockIdx : Int, t, t' : Time] {
	// Precondition
	countAllBlocks[cont, t] > 1
	blockIdx >= 0
	blockIdx < countAllBlocks[cont, t]
	#(blockForBlockIndex[cont, blockIdx, t]._samples) = 0

	// Preserved
	all bfc : BlockFileContainer | readAllSamples[bfc, t'] = readAllSamples[bfc, t]
	_tracks.t' = _tracks.t

	// Updated
	_blocks.t' = _blocks.t ++ cont -> delete[cont._blocks.t, blockIdx]
	_action.t = DeleteAction
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                         Invariant Predicates                                     //
////////////////////////////////////////////////////////////////////////////////////////////

pred Init[t : Time] {
	no _tracks.t
	countAllSamples[Clipboard, t] = 0
	no Clipboard._blocks.t
	_action.t = InitAction
}

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

////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun lastBlockIndex[cont : BlockFileContainer, t : Time] : Int {
	countAllBlocks[cont, t].sub[1]
}

fun countBlocks[cont : BlockFileContainer, from, to : Int, t : Time] : Int {
	#readBlocks[cont, from, to, t]
}

fun readBlocks[cont : BlockFileContainer, from, to : Int, t : Time] : seq BlockFile {
	subseq[readAllBlocks[cont, t], from, to]
}

fun countAllBlocks[cont : BlockFileContainer, t : Time] : Int {
	#readAllBlocks[cont, t]
}

fun readAllBlocks[cont : BlockFileContainer, t : Time] : seq BlockFile {
	cont._blocks.t
}

fun lastContSampleIdx[cont : BlockFileContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

fun countAllSamples[cont : BlockFileContainer, t : Time] : Int {
	#readAllSamples[cont, t]
}

fun readAllSamples[cont : BlockFileContainer, t : Time] : seq Sample {
	let blocksCount = #(cont._blocks.t), lastSampleIndex = prec[cont, blocksCount, t] |
		readSamples[cont, 0, lastSampleIndex, t]
}

fun countSamples[cont : BlockFileContainer, from, to : Int, t : Time] : Int {
	#readSamples[cont, from, to, t]
}

// NOTE: This method is the refinement of AbstractAudacityLayers model
fun readSamples[cont : BlockFileContainer, from, to : Int, t : Time] : seq Sample {
	// add/sub are needd to align indices from [from, to] range into zero-starting range
	{ i : range[0, to.sub[from].add[1]], sample : readSample[cont, i.add[from], t] }
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun readSample[cont : BlockFileContainer, sampleIdx : Int, t : Time] : Sample {
	blockForSampleIndex[cont, sampleIdx, t]._samples[sampleIndexInBlockForSampleIndex[cont, sampleIdx, t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun sampleIndexInBlockForSampleIndex[cont : BlockFileContainer, sampleIdx : Int, t : Time] : Int {
	sampleIdx.sub[prec[cont, blockIndexForSampleIndex[cont, sampleIdx, t], t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun blockForSampleIndex[cont : BlockFileContainer, sampleIdx : Int, t : Time] : BlockFile {
	let blockIdx = blockIndexForSampleIndex[cont, sampleIdx, t] |
		blockForBlockIndex[cont, blockIdx, t]
}

fun blockForBlockIndex[cont : BlockFileContainer, blockIdx : Int, t : Time] : BlockFile {
		(cont._blocks.t)[blockIdx]
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun blockIndexForSampleIndex[cont : BlockFileContainer, sampleIdx : Int, t : Time] : Int {
	// (cont._blocks.t).BlockFile - the indices list of the blocks in sequence
	max[ { j : (cont._blocks.t).BlockFile | prec[cont, j, t] <= sampleIdx } ] // Calculates the highest index of blocks where the sample can appear 
}

// Count the number of samples in block subsequence from start upto blockIdx (not including).
// This is actually the index of the first sample in the block j
fun prec[cont : BlockFileContainer, blockIdx : Int, t : Time] : Int {
	sum k : range[0, blockIdx] | #((cont._blocks.t)[k]._samples)
}

// Creates a list of integers in range [from, to)
fun range[from, upto : Int] : set Int {
	{ n : Int | from <= n && n < upto } // This is the technique to create an iteration: create a list of integers representing the interation indices
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                                   Facts                                                   //
////////////////////////////////////////////////////////////////////////////////////////////

fact {
	_window in Track one -> Window // different tracks have different windows
	_id in BlockFileContainer lone -> ID // id is unique identifier of BlockFileContainer.
}

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
