
sig Sample {}

sig State {
	samples : seq Sample
}

fun size[s:State] : Int {
	#(s.samples)
}

fun read[s:State, addr:Int] : Sample {
	s.samples[addr]
}

pred write[s,s':State, addr : Int, value : Sample] {
	addr in s.samples.Sample
	s'.samples = s.samples ++ addr -> value
}

pred cut[s,s':State, from, to : Int] {

	0 <= from and from < size[s]
	0 <= to and to < size[s]

	from <= to

	size[s'] = (to.sub[from]).add[1]
	all i : Int | 0 <= i and i < size[s'] => 
		read[s',i] = read[s,i.add[from]]
}

run { some s,s' : State, from, to : Int | from < to and cut[s,s', from, to] } for 3 but 2 State, 5 Int

/*

The refinement calculus version of write:

	write(i, value) def 
		(i in samples.Sample, all j : Int - i | samples' = samples ++ i -> value)

A PT that refines cut:

	i := from ;
	do i < to -> 
		write(i-from, read(i)) ; i := i + 1
	od

*/
