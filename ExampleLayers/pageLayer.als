
module pageLayer

open abstractLayer 

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
	all s :  this/State, p : elems[s.pages] - last[s.pages] | #samples[p].s = 3

	all s :  this/State | #samples[last[s.pages]].s <= 3
}

fun addrInPage[addr:Int] : Int {
	addr.rem[3]
}

fun pageOf[addr:Int] : Int {
	addr.div[3]
}

fun size[s: this/State] : Int {
	sum p : elems[s.pages] | #(samples[p].s)
}

fun read[s: this/State, addr:Int] : Sample {
	(samples[s.pages[pageOf[addr]]].s)[addrInPage[addr]]
}

pred write[s,s':this/State, addr : Int, value : Sample] {
	pageOf[addr] in s.pages.Page
	addrInPage[addr] in (samples[s.pages[pageOf[addr]]].s).Sample

	samples[s.pages[pageOf[addr]]].s' = samples[s.pages[pageOf[addr]]].s ++ addrInPage[addr] -> value
	all p : Page - s.pages[pageOf[addr]] | samples[p].s' = samples[p].s
	s'.pages = s.pages
} 

pred retrieve[c : this/State, a:abstractLayer/State]
{
	this/size[c] = abstractLayer/size[a]
	all i : Int | 0 <= i and i < size[c] => 
		this/read[c, i] = abstractLayer/read[a, i]
}

check {
	all c,c': this/State, a,a':abstractLayer/State, addr : Int, value : Sample | 
		(retrieve[c,a] and retrieve[c',a'] and this/write[c,c',addr, value]) => 
			abstractLayer/write[a,a',addr,value]
} for 3 but 2 this/State, 2 abstractLayer/State


/* these tests are not necessary because they are trivially implied by the
retrieve relation...

check { 
	all c : this/State, a : abstractLayer/State | retrieve[c,a] =>
		this/size[c] = abstractLayer/size[a]
}

check { 
	all c : this/State, a : abstractLayer/State | retrieve[c,a] => {
		all i : Int | 0 <= i and i < size[c] => 
			this/read[c, i] = abstractLayer/read[a, i]
	}
}
*/

pred cut[s,s': this/State, from, to : Int] {

	0 <= from and from < this/size[s]
	0 <= to and to < this/size[s]

	from <= to

	this/size[s'] = (to.sub[from]).add[1]
	all i : Int | 0 <= i and i < this/size[s'] => 
		this/read[s',i] = this/read[s,i.add[from]]

}

run { 
	some s,s' :  this/State, from, to : Int | 
		from < to and cut[s,s', from, to] 
} for 3 but 5 Int, 2 this/State


run {} for 3 but 5 Int, 1 this/State

check {
	all c,c': this/State, a,a':abstractLayer/State, from, to : Int | 
		(retrieve[c,a] and retrieve[c',a']) => 
			(this/cut[c,c',from,to] iff abstractLayer/cut[a,a',from,to])
} 


