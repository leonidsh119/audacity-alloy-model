module ConcreteAudacity

open CommonAudacity
open util/ordering[Time]

let MAX_BLOCK_SIZE = 4

////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Time {}

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

sig Window {
	_start : Int -> Time,
	_end : Int -> Time,
	_winsamples : (seq BlockFile) -> Time
}

one sig Clipboard extends BlockFileContainer {}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Import[t, t' : Time, track : Track] {
	// Precondition
	track !in _tracks.t // this is a new track that doesn't belongs to the prject's tracks list
	some track._blocks.t // the new track is not empty
	all block : BlockFile | block in Int.(track._blocks.t) => some block._samples

	// Preserved
	_blocks.t' = _blocks.t

	// Updated
	_tracks.t' = _tracks.t + track
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
// Abstract Model
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	from <= to // there are at least one sample selected to cut
	from >= 0
	to <= countAllSamples[track, t]

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]

// Concrete Model
	let firstCutBlockIndex = blockIndexForSampleIndex[track, from, t],  lastCutBlockIndex = blockIndexForSampleIndex[track, to, t] | {
		// Precondition
		all block : track._blocks.t | #(block._samples) > 0
		sampleIndexInBlockForSampleIndex[track, from, t] = 0 // "from" is the first sample in its block
		sampleIndexInBlockForSampleIndex[track, to, t] = sub[#(blockForBlockIndex[track, lastCutBlockIndex, t]._samples), 1] // "to" is the last sample in its block
		countAllBlocks[Clipboard, t] = sub[lastCutBlockIndex, firstCutBlockIndex] // required number of blocks in clipboard. what skip action achieves that?

		// Preserved
		_blocks.t' = _blocks.t
		all otherTrack : _tracks.t' - track, block : otherTrack._blocks | block.t'._samples = block.t._samples
		all i : range[0, countAllBlocks[track, t]] - range[firstCutBlockIndex, lastCutBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[track, i, t]._samples

		// Updated
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | no blockForBlockIndex[track, i, t']._samples
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | blockForBlockIndex[Clipboard, sub[i, firstCutBlockIndex], t']._samples = blockForBlockIndex[track, i, t]._samples
	}
}

pred CutNoMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] <= countSamples[track, to.add[1], countAllSamples[track, t], t] // number for cut samples is SMALLER than number of sequences from the left of the visible winfow

	// Preserved
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

	// Updated
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, track._window._start.t', track._window._end.t', t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
}

pred CutMove[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > countSamples[track, to.add[1], countAllSamples[track, t], t] // number for cut samples is LARGER than number of sequences from the left of the visible winfow, but...
	to.sub[from.add[1]] <= countSamples[track, to.add[1], countAllSamples[track, t], t].add[countSamples[track, 0, from.sub[1], t]] // number for cut samples is SMALLER than number of sequences from the left AND from the right of the visible winfow, but...

	// Preserved
	_end.t' = _end.t // visible vindow is moved to the end of the track

	// Updated
	_start.t' = _start.t ++ track._window -> track._window._end.t'.sub[track._window._end.t.sub[track._window._start.t]] // moved visible window size is preserved
	_winsamples.t' = _winsamples.t ++ track._window -> readSamples[track, track._window._start.t', track._window._end.t', t'] // Refresh displayed samples according to the remaining window start and end, but with the new track samples sequence
}

pred CutZoomIn[t, t' : Time, track : Track, from, to : Int] {
	// Precondition
	to.sub[from.add[1]] > countSamples[track, to.add[1], countAllSamples[track, t], t].add[countSamples[track, 0, from.sub[1], t]] // number for cut samples is LARGER than number of sequences from the left AND from the right of the visible winfow

	// Updated
	_start.t' = _start.t ++ track._window -> 0 // the visible window shrinking to display all the remaining samples
	_end.t' = _end.t ++ track._window -> countAllSamples[track, t'] // the visible window shrinking to display all the remaining samples
	_winsamples.t' = _winsamples.t ++ track._window -> readAllSamples[track, t']
}

// NOTE: this operation has stronger precondition than in abstract model to ensure that all the required effects of Skip functions is done.
// However the Update part is the same.
pred Paste[t, t' : Time, track : Track, into : Int] {
// Abstract Model
	// Precondition
	track in _tracks.t // the track belongs to the project's tracks list
	track._window._start.t <= into // the paste location is in the visible window (start)
	track._window._end.t >= into // the paste location is in the visible window (end)

	// Preserved
	_tracks.t' = _tracks.t
	all otherTrack : _tracks.t' - track | readAllSamples[otherTrack, t'] = readAllSamples[otherTrack, t]
	_start.t' = _start.t // use the same window size and location in track
	_end.t' = _end.t // use the same window size and location in track

// Concrete Model
	let firstEmptyBlockIndex = add[blockIndexForSampleIndex[track, sub[into, 1], t], 1],  lastEmptyBlockIndex = add[firstEmptyBlockIndex, countAllBlocks[Clipboard, t]] | {
		// Precondition
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) = 0
		all i : range[0, countAllBlocks[track, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | #(blockForBlockIndex[track, i, t]._samples) > 0

		// Preserved
		_blocks.t' = _blocks.t
		all otherTrack : _tracks.t' - track, block : otherTrack._blocks | block.t'._samples = block.t._samples
		all block : Clipboard._blocks | block.t'._samples = block.t._samples
		all i : range[0, countAllBlocks[track, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[track, i, t]._samples

		// Updated
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | blockForBlockIndex[track, i, t']._samples = blockForBlockIndex[Clipboard, sub[i, firstEmptyBlockIndex], t]._samples
	}
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
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                         Invariant Predicates                                     //
////////////////////////////////////////////////////////////////////////////////////////////

pred Init[t : Time] {
	no _tracks.t
	no Clipboard._blocks.t
}

pred Inv[t : Time] {
	// all the blocks in DirManager are the blocks from Tracks and Clipboard
	// Others?
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
	_id in BlockFileContainer lone -> ID // id is unique identifier of BlockFileContainer.
}

fact {
	Init[first]
	all t, t' : Time | t -> t' in next => 
		some track : Track |
			Import[t, t', track]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

run { 
	#(BlockFile._samples) >= 2
} for 7 but 3 Time, 7 Int

check {
	all t : Time | Inv[t]
} for 5
