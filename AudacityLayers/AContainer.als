module AContainer

open Time
open Sample


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

abstract sig AContainer extends Container {
	_samples : (seq Sample) -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred EmptyContainer[cont : AContainer, t : Time] {
	countAllSamples[cont, t] = 0
}

pred ValidateContainer[cont : AContainer, t : Time] {
	countAllSamples[cont, t] > 1 // Not empty. Asumming at least 2 samples for being able to define a window
}

pred PreserveContainer[cont : AContainer, t, t' : Time] {
	readAllSamples[cont, t] = readAllSamples[cont, t']
}

pred ExtractSamples[contSrc, contOut : AContainer, from, to : Int, t, t' : Time] {
	readSamples[contSrc, 0, from.sub[1], t'] = readSamples[contSrc, 0, from.sub[1], t]
	readAllSamples[contOut, t'] = readSamples[contSrc, from, to, t]
	readSamples[contSrc, from, lastContSampleIdx[contSrc, t'], t'] = readSamples[contSrc, to.add[1], lastContSampleIdx[contSrc, t], t]
}

pred InsertSamples[cont1, cont2 : AContainer, into : Int, t, t' : Time] {
	readSamples[cont1, 0, into.sub[1], t'] = readSamples[cont1, 0, into.sub[1], t]
	readSamples[cont1, into, into.add[countAllSamples[cont2, t]].sub[1], t'] = readAllSamples[cont2, t]
	readSamples[cont1, into.add[countAllSamples[cont2, t]], lastContSampleIdx[cont1, t'], t'] = readSamples[cont1, into, lastContSampleIdx[cont1, t], t]
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun readAllSamples[cont : AContainer, t : Time] : seq Sample {
	cont._samples.t
}

fun readSamples[cont : AContainer, from, to : Int, t : Time] : seq Sample {
	subseq[cont._samples.t, from, to]
}

fun lastContSampleIdx[cont : AContainer, t : Time] : Int {
	countAllSamples[cont, t].sub[1]
}

fun countAllSamples[cont : AContainer, t : Time] : Int {
	#readAllSamples[cont, t]
}

fun countSamples[cont : AContainer, from, to : Int, t : Time] : Int {
	#readSamples[cont, from, to, t]
}
