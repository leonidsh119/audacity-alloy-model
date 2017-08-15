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
	_tracks : set Time
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

////////////////////////////////////////////////////////////////////////////////////////////
//                                         Invariant Predicates                                     //
////////////////////////////////////////////////////////////////////////////////////////////

pred Init[t : Time] {
	no _tracks.t
	no Clipboard._blocks.t
}

pred Inv[t : Time] {
	// all the blocks in DirManager are the blocks from Tracks and Clipboard
}

pred Cut[t, t' : Time, track : Track, from, to : Int] {
	// TODO: Implement
}

pred Paste[t, t' : Time, track : Track, into : Int] {
	// TODO: Implement
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

fun readAllSamples[cont : BlockFileContainer, t : Time] : seq Sample {
	let blocksCount = #(cont._blocks.t), lastSampleIndex = prec[cont, blocksCount, t] |
		readSamples[cont, 0, lastSampleIndex, t]
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
