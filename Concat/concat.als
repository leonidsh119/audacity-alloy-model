
////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures
////////////////////////////////////////////////////////////////////////////////////////////

sig Block {
	samples : seq Sample
}

sig Sample {
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates
////////////////////////////////////////////////////////////////////////////////////////////

pred concat[blocks : seq Block, result : seq Sample] {

	#result = (sum i : blocks.Block | #blocks[i].samples)

	some offsets : seq Int | {
		monotonic[offsets]
		offsets.Int in result.Sample
		all i : blocks.Block | {
			result.subseq[offsets[i], #blocks[i].samples] = blocks[i].samples
		}
		all i : blocks.Block - 0 | {
			offsets[i].sub[offsets[i.sub[1]]] = #blocks[i].samples // offsets[i] - offsets[i-1] = # blocks[i].samples
		}
	}
}

pred monotonic[s : seq Int] {
	all i, j : s.Int | int[i] <= int[j] =>s[i] <= s[j]
}

pred read_the_same[blocks : seq Block, s : seq Sample] {
	#s = prec[blocks, #blocks]
	all i : s.Sample | read_samples[s, i] = read_samples_from_blocks[blocks, i]
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions
////////////////////////////////////////////////////////////////////////////////////////////

fun read_samples[s : seq Sample, i : Int] : Sample {
	s[i]
}

fun read_samples_from_blocks[blocks : seq Block, i : Int] : Sample {
	let j = blockIndex[blocks, i] |
		blocks[j].samples[i.sub[prec[blocks, j]]]
}

fun prec[blocks : seq Block, j : Int] : Int {
	sum k : range[0,j] | #samples[blocks[k]]
}

fun blockIndex[blocks : seq Block, i : Int] : Int {
	 max[ { j : blocks.Block | prec[blocks, j] <= i } ]
}

fun range[from, upto:Int] : set Int {
	{ n : Int | from <= n && n < upto }
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions
////////////////////////////////////////////////////////////////////////////////////////////

check {
	all blocks : seq Block, result : seq Sample | 
		concat[blocks, result] => read_the_same[blocks, result]
}

check {
	all blocks : seq Block, result : seq Sample | 
		read_the_same[blocks, result] => concat[blocks, result]
}

run { 
	some blocks : seq Block, result : seq Sample | concat[blocks, result] 
}
