module AWindow

open Time
open AContainer


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Window extends AContainer {
	_start : Int -> Time,
	_end : Int -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred ValidateWindow[window : Window, t : Time] {
	ValidateContainer[window, t]
	window._start.t >= 0
	window._end.t > window._start.t
}

pred PreserveWindow[window : Window, t, t' : Time] {
	PreserveContainer[window, t, t']
	window._start.t' = window._start.t
	window._end.t' = window._end.t
}

pred SetWindow[window : Window, start, end : Int, winsamples : seq Sample, t : Time] {
	// Precondition
	start >= 0
	end >= start
	ValidateContainer[window, t]
	end.sub[start].add[1] = countAllSamples[window, t]

	// Updated
	window._start.t = start
	window._end.t = end
	readAllSamples[window, t] = winsamples
}

pred IsRangeDisplayed[window : Window, from, to : Int, t : Time] {
	window._start.t <= from
	window._end.t >= to
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                                Functions                                               //
////////////////////////////////////////////////////////////////////////////////////////////

fun getStart[window : Window, t : Time] : Int {
	window._start.t
}

fun getEnd[window : Window, t : Time] : Int {
	window._end.t
}
