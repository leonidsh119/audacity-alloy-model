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

pred Inv[window : Window, t : Time] {
	AContainer/Inv[window, t]
	window._start.t >= 0
	window._end.t > window._start.t
}

pred Equiv[window : Window, t, t' : Time] {
	AContainer/Equiv[window, t, t']
	window._start.t' = window._start.t
	window._end.t' = window._end.t
}

pred SetWindow[window : Window, start, end : Int, winsamples : seq Sample, t : Time] {
	// Precondition
	start >= 0
	end >= start
	AContainer/Inv[window, t]
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

pred CanZoomIn[window : Window, newStart, newEnd : Int, t : Time] {
	countAllSamples[window, t] > 2 // the window has space to shrink
	newEnd.sub[newStart] < (window._end.t).sub[window._start.t] // new window is smaller than the old one
	newStart >= window._start.t // new window boundaries are inside old one's (start)
	newEnd <= window._end.t // new window boundaries are inside old one's (end)
}

pred CanZoomOut[window : Window, newStart, newEnd : Int, t : Time] {
	newEnd.sub[newStart] > (window._end.t).sub[window._start.t] // new window is larger than the old one
	newStart <= window._start.t // new window boundaries are outside old one's (start)
	newEnd >= window._end.t // new window boundaries are outside old one's (end)
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
