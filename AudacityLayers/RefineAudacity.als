open CommonAudacity
open AbstractAudacity
open ConcreteAudacity 

pred retrieve[at : AbstractAudacity/Time, ct : ConcreteAudacity/Time]
{
	all aCont : AbstractAudacity/SamplesContainer | 
		{ one cCont : ConcreteAudacity/BlockFileContainer |
			aCont._id = cCont._id and
			AbstractAudacity/readAllSamples[aCont, at] = ConcreteAudacity/readAllSamples[cCont, ct] }
}

check {
	all at, at' : AbstractAudacity/Time, ct, ct' : ConcreteAudacity/Time, from, to : Int | 
		(retrieve[at, ct] and retrieve[at', ct']) => (AbstractAudacity/Cut[at, at', from, to] iff ConcreteAudacity/Cut[ct, ct', from, to])
} 
