open CommonAudacity
open AbstractAudacity
open ConcreteAudacity 


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates
////////////////////////////////////////////////////////////////////////////////////////////

pred retrieve[at : AbstractAudacity/Time, ct : ConcreteAudacity/Time]
{
	all aCont : AbstractAudacity/SamplesContainer | 	{
		one cCont : ConcreteAudacity/BlockFileContainer |
			aCont._id = cCont._id and
			assertEqual[aCont, at, cCont, ct]
	}
}

pred assertEqual[aCont : AbstractAudacity/SamplesContainer, at : AbstractAudacity/Time, cCont : ConcreteAudacity/BlockFileContainer, ct : ConcreteAudacity/Time] {
	AbstractAudacity/readAllSamples[aCont, at] = ConcreteAudacity/readAllSamples[cCont, ct]
}

// Asserts for Sample-wise equality between sequence of Blocks and a sequence of Samples
pred assertEqual2[aCont : AbstractAudacity/SamplesContainer, at : AbstractAudacity/Time, cCont : ConcreteAudacity/BlockFileContainer, ct : ConcreteAudacity/Time] {
	#(aCont._samples.at) = (sum i : (cCont._blocks.ct).BlockFile | #(cCont._blocks.ct)[i]._samples) // compare total number of samples in both models
	some offsets : seq Int | {
		all i, j : offsets.Int | int[i] <= int[j] =>offsets[i] <= offsets[j] // Monotonic
		offsets.Int in (aCont._samples.at).Sample
		all i : (cCont._blocks.ct).BlockFile | {
			(aCont._samples.at).subseq[offsets[i], #(cCont._blocks.ct)[i]._samples] = (cCont._blocks.ct)[i]._samples
		}
		all i : (cCont._blocks.ct).BlockFile - 0 | {
			offsets[i].sub[offsets[i.sub[1]]] = #(cCont._blocks.ct)[i]._samples // offsets[i] - offsets[i-1] = # blocks[i]._samples
		}
	}
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions
////////////////////////////////////////////////////////////////////////////////////////////

check {
	all at, at' : AbstractAudacity/Time, aTrack : AbstractAudacity/Track, ct, ct' : ConcreteAudacity/Time, cTrack : ConcreteAudacity/Track, from, to : Int | 
		(retrieve[at, ct] and retrieve[at', ct']) => (AbstractAudacity/Cut[at, at', aTrack, from, to] iff ConcreteAudacity/Cut[ct, ct', cTrack, from, to])
} 

check {
	all at, at' : AbstractAudacity/Time, ct, ct' : ConcreteAudacity/Time | 
		(retrieve[at, ct] and retrieve[at', ct']) => (all cont : BlockFileContainer,  blockIdx : Int, head, tail : BlockFile | ConcreteAudacity/Split[cont, blockIdx, head, tail, ct, ct'] => AbstractAudacity/Skip[at, at'])
} 

check {
	all at, at' : AbstractAudacity/Time, ct, ct' : ConcreteAudacity/Time | 
		(retrieve[at, ct] and retrieve[at', ct']) => (all cont : BlockFileContainer,  blockIdx : Int, emptyBlock : BlockFile | ConcreteAudacity/Insert[cont, blockIdx, emptyBlock, ct, ct'] => AbstractAudacity/Skip[at, at'])
} 

check {
	all at, at' : AbstractAudacity/Time, ct, ct' : ConcreteAudacity/Time | 
		(retrieve[at, ct] and retrieve[at', ct']) => (all cont : BlockFileContainer,  blockIdx : Int | ConcreteAudacity/Delete[cont, blockIdx, ct, ct'] => AbstractAudacity/Skip[at, at'])
}
