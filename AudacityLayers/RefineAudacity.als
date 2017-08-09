open CommonAudacity
open AbstractAudacity
open ConcreteAudacity 

pred retrieve[at : AbstractAudacity/Time, ct : ConcreteAudacity/Time]
{
	all aCont : AbstractAudacity/SamplesContainer | one cCont : ConcreteAudacity/BlockFileContainer =>
		(AbstractAudacity/readAllSamples[aCont, at] = ConcreteAudacityudacity/readAllSamples[ConcreteAudacity/cCont, ct])
}

check {
	all at, at' : AbstractAudacity/Time, ct, ct' : ConcreteAudacity/Time, from, to : Int | 
		(retrieve[at, ct] and retrieve[at', ct']) => (AbstractAudacity/cut[c, c', from, to] iff ConcreteAudacity/cut[a, a', from,to])
} 
