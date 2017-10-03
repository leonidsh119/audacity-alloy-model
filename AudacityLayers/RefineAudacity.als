open CommonAudacity
open AbstractAudacity
open ConcreteAudacity 

// We can try defining a retrieve in terms of concatination of a sequence of sequences of Samples.
// There is a limitation to do it in Alloy, but logically it is possible.
// If we will succeed doing it, we will be able to remove the circularity: operations->retriev->read->...
pred retrieve[at : AbstractAudacity/Time, ct : ConcreteAudacity/Time]
{
	all aCont : AbstractAudacity/SamplesContainer | 
		{ one cCont : ConcreteAudacity/BlockFileContainer |
			aCont._id = cCont._id and
			AbstractAudacity/readAllSamples[aCont, at] = ConcreteAudacity/readAllSamples[cCont, ct] }
}

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
