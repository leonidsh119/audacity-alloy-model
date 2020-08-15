module BFContainer

open Time
open BlockFile


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

abstract sig BFContainer extends Container {
	_blocks : (seq BlockFile) -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[cont : BFContainer, t : Time] {
	some cont._blocks.t // Has some blocks
	all block : cont._blocks.t[Int] | BlockFile/Inv[block] // No Empty blocks
	countAllSamples[cont, t] > 1 // Not empty. Asumming at least 2 samples for being able to define a window
}

pred Init[cont : BFContainer, t : Time] {
	this/Empty[cont, t]
}

pred Equiv[cont : BFContainer, t, t' : Time] {
	cont._blocks.t' = cont._blocks.t
	all block0, block1 : BlockFile, idx : Int | (block0 in cont._blocks.t[idx] && block1 in cont._blocks.t'[idx]) implies BlockFile/Equals[block0, block1]
	readAllSamples[cont, t] = readAllSamples[cont, t']
}

pred Empty[cont : BFContainer, t : Time] {
	no cont._blocks.t
	countAllSamples[cont, t] = 0
}

pred ExtractSamples[contSrc, contOut : BFContainer, from, to : Int, t, t' : Time] {
	let firstCutBlockIndex = blockIndexForSampleIndex[contSrc, from, t],  lastCutBlockIndex = blockIndexForSampleIndex[contSrc, to, t] | {
		// Precondition
		all block : contSrc._blocks.t[Int] | BlockFile/Inv[block]	
		sampleIndexInBlockForSampleIndex[contSrc, from, t] = 0 // "from" is the first sample in its block
		sampleIndexInBlockForSampleIndex[contSrc, to, t] = sub[BlockFile/countSamples[blockForBlockIndex[contSrc, lastCutBlockIndex, t]], 1] // "to" is the last sample in its block
		countAllBlocks[contOut, t] = sub[lastCutBlockIndex, firstCutBlockIndex] // required number of blocks in clipboard. what skip action achieves that?

		// Preserved
		contSrc._blocks.t' = contSrc._blocks.t
		all i : range[0, countAllBlocks[contSrc, t]] - range[firstCutBlockIndex, lastCutBlockIndex] | BlockFile/Equals[blockForBlockIndex[contSrc, i, t'], blockForBlockIndex[contSrc, i, t]]

		// Updated
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | BlockFile/Empty[blockForBlockIndex[contSrc, i, t']]
		all i : range[firstCutBlockIndex, lastCutBlockIndex] | BlockFile/Equals[blockForBlockIndex[contOut, sub[i, firstCutBlockIndex], t'], blockForBlockIndex[contSrc, i, t]]
	}
}

pred InsertSamples[cont1, cont2 : BFContainer, into : Int, t, t' : Time] {
	let firstEmptyBlockIndex = add[blockIndexForSampleIndex[cont1, sub[into, 1], t], 1],  lastEmptyBlockIndex = add[firstEmptyBlockIndex, countAllBlocks[cont2, t]] | {
		// Precondition
//		all block : cont1._blocks | block.t' = block.t // The assumption is that all needed blocks are already prepared and in this method only filled up with samples
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | BlockFile/Empty[blockForBlockIndex[cont1, i, t]]
		all i : range[0, countAllBlocks[cont1, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | !BlockFile/Empty[blockForBlockIndex[cont1, i, t]]

		// Preserved
		all i : range[0, countAllBlocks[cont1, t]] - range[firstEmptyBlockIndex, lastEmptyBlockIndex] | BlockFile/Equals[blockForBlockIndex[cont1, i, t'], blockForBlockIndex[cont1, i, t]]

		// Updated
		all i : range[firstEmptyBlockIndex, lastEmptyBlockIndex] | BlockFile/Equals[blockForBlockIndex[cont1, i, t'], blockForBlockIndex[cont2, sub[i, firstEmptyBlockIndex], t]]
	}
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun lastBlockIndex[cont : BFContainer, t : Time] : Int {
	countAllBlocks[cont, t].sub[1]
}

fun countBlocks[cont : BFContainer, from, to : Int, t : Time] : Int {
	#readBlocks[cont, from, to, t]
}

fun readBlocks[cont : BFContainer, from, to : Int, t : Time] : seq BlockFile {
	subseq[readAllBlocks[cont, t], from, to]
}

fun countAllBlocks[cont : BFContainer, t : Time] : Int {
	#readAllBlocks[cont, t]
}

fun readAllBlocks[cont : BFContainer, t : Time] : seq BlockFile {
	cont._blocks.t
}

fun lastContSampleIdx[cont : BFContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

fun countAllSamples[cont : BFContainer, t : Time] : Int {
	#readAllSamples[cont, t]
}

fun readAllSamples[cont : BFContainer, t : Time] : seq Sample {
	let blocksCount = #(cont._blocks.t), lastSampleIndex = prec[cont, blocksCount, t] |
		readSamples[cont, 0, lastSampleIndex, t]
}

fun countSamples[cont : BFContainer, from, to : Int, t : Time] : Int {
	#readSamples[cont, from, to, t]
}

// NOTE: This method is the refinement of AbstractAudacityLayers model
fun readSamples[cont : BFContainer, from, to : Int, t : Time] : seq Sample {
	// add/sub are needd to align indices from [from, to] range into zero-starting range
	{ i : range[0, to.sub[from].add[1]], sample : readSample[cont, i.add[from], t] }
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun readSample[cont : BFContainer, sampleIdx : Int, t : Time] : Sample {
	BlockFile/readSample[blockForSampleIndex[cont, sampleIdx, t], sampleIndexInBlockForSampleIndex[cont, sampleIdx, t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun sampleIndexInBlockForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : Int {
	sampleIdx.sub[prec[cont, blockIndexForSampleIndex[cont, sampleIdx, t], t]]
}

// For the given sample index in the entire track provides the block the sample belongs to
fun blockForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : BlockFile {
	let blockIdx = blockIndexForSampleIndex[cont, sampleIdx, t] |
		blockForBlockIndex[cont, blockIdx, t]
}

fun blockForBlockIndex[cont : BFContainer, blockIdx : Int, t : Time] : BlockFile {
		(cont._blocks.t)[blockIdx]
}

// For the given sample index in the entire track provides the block index the sample belongs to
fun blockIndexForSampleIndex[cont : BFContainer, sampleIdx : Int, t : Time] : Int {
	// (cont._blocks.t).BlockFile - the indices list of the blocks in sequence
	max[ { j : (cont._blocks.t).BlockFile | prec[cont, j, t] <= sampleIdx } ] // Calculates the highest index of blocks where the sample can appear 
}

// Count the number of samples in block subsequence from start upto blockIdx (not including).
// This is actually the index of the first sample in the block j
fun prec[cont : BFContainer, blockIdx : Int, t : Time] : Int {
	sum k : range[0, blockIdx] | BlockFile/countSamples[(cont._blocks.t)[k]]
}

// Creates a list of integers in range [from, to)
fun range[from, upto : Int] : set Int {
	{ n : Int | from <= n && n < upto } // This is the technique to create an iteration: create a list of integers representing the interation indices
}
