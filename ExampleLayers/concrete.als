
open absModel 

sig Page {
	samples : seq Sample -> this/State
}

sig State {
	pages : seq Page
}

fact {
	all s : this/State | ! hasDups[s.pages]
}

fact {
	all s : this/State, p : elems[s.pages] - last[s.pages] | #samples[p].s = 3

	all s : this/State | #samples[last[s.pages]].s <= 3
}

fun size[s:this/State] : Int {
	sum p : elems[s.pages] | #(samples[p].s)
}

fun addrInPage[addr:Int] : Int {
	addr.rem[3]
}

fun pageOf[addr:Int] : Int {
	addr.div[3]
}

pred cut[s,s':this/State, from, to : Int] {

	0 <= from and from <= to
	to < size[s]

	size[s'] = (to.sub[from]).add[1]
	all i : Int | 0 <= i and i < size[s'] => 
		let j = i.add[from] | 
			s'.pages[pageOf[i]].samples.s'[addrInPage[i]] = s.pages[pageOf[j]].samples.s[addrInPage[j]]
}

run { some s,s' : this/State, from, to : Int | from < to and cut[s,s', from, to] } for 3 but 2 this/State, 5 Int

pred retrieve[c : this/State, a:absModel/State]
{
	size[c] = #a.samples
	all i : Int | 0 <= i and i < size[c] => 
		a.samples[i] = c.pages[pageOf[i]].samples.c[addrInPage[i]]
}

check {
	all c,c': this/State, a,a':absModel/State, from, to : Int | 
		(retrieve[c,a] and retrieve[c',a']) => (this/cut[c,c',from,to] iff absModel/cut[a,a',from,to])
} 
