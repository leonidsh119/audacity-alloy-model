
open Sample
open AContainer
open AAudacity
open BFContainer
open BFAudacity


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates
////////////////////////////////////////////////////////////////////////////////////////////

pred retrieve[t : Time]
{
	all aCont : AContainer | 	{
		one cCont : BFContainer |
			assertEqual[aCont, cCont, t]
	}
}

pred assertEqual[aCont : AContainer, cCont : BFContainer, t : Time] {
	Sample/Equals[aCont, cCont]
	AContainer/readAllSamples[aCont, t] = BFContainer/readAllSamples[cCont, t]
}

// Asserts for Sample-wise equality between sequence of Blocks and a sequence of Samples
// This assertion may be stronger because it doesn't rely on readAllSamples implementaiton in both AContainer and BFContainer 
// Otherwise we actually find ourselves prroving the formal model soecification by using the specification itself.
pred assertEqual2[aCont : AContainer, cCont : BFContainer, t : Time] {
	#(aCont._samples.t) = (sum i : (cCont._blocks.t).BlockFile | #(cCont._blocks.t)[i]._samples) // compare total number of samples in both models
	some offsets : seq Int | {
		all i, j : offsets.Int | int[i] <= int[j] implies offsets[i] <= offsets[j] // Monotonic
		offsets.Int in (aCont._samples.t).Sample
		all i : (cCont._blocks.t).BlockFile | {
			(aCont._samples.t).subseq[offsets[i], #(cCont._blocks.t)[i]._samples] = (cCont._blocks.t)[i]._samples
		}
		all i : (cCont._blocks.t).BlockFile - 0 | {
			offsets[i].sub[offsets[i.sub[1]]] = #(cCont._blocks.t)[i]._samples // offsets[i] - offsets[i-1] = # blocks[i]._samples
		}
	}
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                              Assertions
////////////////////////////////////////////////////////////////////////////////////////////

check {
	all t, t' : Time, aTrack : AAudacity/Track, cTrack : BFAudacity/Track, from, to : Int | 
		(retrieve[t] and retrieve[t']) implies (AAudacity/Cut[t, t', aTrack, from, to] iff BFAudacity/Cut[t, t', cTrack, from, to])
} 

check {
	all t, t' : Time | 
		(retrieve[t] and retrieve[t']) implies (all cont : BFContainer,  blockIdx : Int, head, tail : BlockFile | BFAudacity/Split[cont, blockIdx, head, tail, t, t'] implies AAudacity/Preserve[t, t'])
} 

check {
	all t, t' : Time | 
		(retrieve[t] and retrieve[t']) implies (all cont : BFContainer,  blockIdx : Int, emptyBlock : BlockFile | BFAudacity/Insert[cont, blockIdx, emptyBlock, t, t'] implies AAudacity/Preserve[t, t'])
} 

check {
	all t, t' : Time | 
		(retrieve[t] and retrieve[t']) implies (all cont : BFContainer,  blockIdx : Int | BFAudacity/Delete[cont, blockIdx, t, t'] implies AAudacity/Preserve[t, t'])
}
