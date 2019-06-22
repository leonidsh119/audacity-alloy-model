module BFWindow

open Time
open BFContainer


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Signatures                                                //
////////////////////////////////////////////////////////////////////////////////////////////

sig Window extends BFContainer {
	_start : Int -> Time,
	_end : Int -> Time
}


////////////////////////////////////////////////////////////////////////////////////////////
//                                             Predicates                                                //
////////////////////////////////////////////////////////////////////////////////////////////

pred Inv[t : Time] {
	// Window's indices are in boundaries of tracks samples sequence and has at least 2 visible samples
	all window : Window |  
		Validate[window, t] &&
		window._start.t >= 0 && 
		window._end.t > window._start.t &&
		(window._end.t).sub[window._start.t].add[1] = countAllSamples[window, t]
}

pred PreserveWindow[window : Window, t, t' : Time] {
	Preserve[window, t, t']
	window._start.t' = window._start.t
	window._end.t' = window._end.t
}

pred SetWindow[window : Window, start, end : Int, winsamples : seq Sample, t : Time] {
	// Precondition
	start >= 0
	end >= start
	Validate[window, t]
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
