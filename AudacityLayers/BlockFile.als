module BlockFile

open Sample

let MAX_BLOCK_SIZE = 4


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig BlockFile {
	_samples : seq Sample
} { #_samples <= MAX_BLOCK_SIZE }


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[block : BlockFile] {
	!this/Empty[block]
}

pred Empty[block : BlockFile] {
	countSamples[block] = 0
}

pred Equals[block0, block1 : BlockFile] {
	block0._samples = block1._samples
}

pred Merge[block, head, tail : BlockFile] {
	block._samples = append[head._samples, tail._samples]
}

////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun countSamples[block : BlockFile] : Int {
	#(block._samples)
}

fun readSample[block : BlockFile, sampleIdx : Int] : Sample {
	block._samples[sampleIdx]
}
