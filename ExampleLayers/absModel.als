
module absModel

sig Sample {}

sig State {
	samples : seq Sample
}

pred cut[s,s':State, from, to : Int] {

	from in s.samples.Sample
	to in s.samples.Sample

	from <= to

	#s'.samples = (to.sub[from]).add[1]
	 all i : (s'.samples).Sample | s'.samples[i] = s.samples[i.add[from]]
}

run { some s,s' : State, from, to : Int | from < to and cut[s,s', from, to] } for 3 but 2 State, 5 Int
