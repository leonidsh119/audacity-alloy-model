
module cacheLayer

open pageLayer

sig Page {
	samples : seq Sample -> this/State,
	cache : this/Page lone -> this/State
}

sig State {
	pages : seq this/Page
}

fact {
	all s : this/State, p : this/Page |
		p.samples.s in (seq Sample)
}

fact {
	all s : this/State | ! hasDups[s.pages]
}

fact {
	all s :  this/State, p : elems[s.pages] - last[s.pages] | 
		#samples[p].s = 3

	all s :  this/State | #samples[last[s.pages]].s <= 3
}

fact {
	all s : this/State | no Page.cache.s & elems[s.pages]
}

pred equalContent[p,q:this/Page, s:this/State] {
	#p.samples.s = #(q).samples.s 
	all i : Int | (0 <= i and i < #p.samples.s) => 
		p.samples.s[i] = (q).samples.s[i]
}

fact {
	all s : this/State, p : this/Page |
		some p.cache.s => equalContent[p, p.cache.s, s]
}

fact {
	all s : this/State |
		all p : Page.cache.s | no p.cache.s
}

fact {
	all s : this/State |
		all p, q : elems[s.pages] | (some p.cache.s and p.cache.s = q.cache.s) =>
			p = q 
}

fun size[s: this/State] : Int {
	sum p : elems[s.pages] | #(samples[p].s)
}

fun read[s: this/State, addr:Int] : Sample {
	let p = s.pages[pageOf[addr]] |
		some p.cache.s => readPage[s, p.cache.s, addrInPage[addr]]
		else readPage[s, p, addrInPage[addr]]
}

fun readPage[s: this/State, p:this/Page, addr:Int] : Sample {
	samples[p].s[addr]
}

pred loadCache[s,s':this/State, p, cachedp:this/Page] {
	p in elems[s.pages] 
	no p.cache.s
	equalContent[cachedp, p, s]

	cache.s' = cache.s + (p -> cachedp)
	samples.s' = samples.s
	s'.pages = s.pages
}

pred removeCache[s,s':this/State, p:this/Page] {
	p in elems[s.pages]
	some p.cache.s

	cache.s' = cache.s - (p -> p.cache.s)
	samples.s' = samples.s
	s'.pages = s.pages
}

pred retrieve[c : this/State, a:pageLayer/State]
{
	this/size[c] = pageLayer/size[a]
	all i : Int | 0 <= i and i < this/size[c] => 
		this/read[c, i] = pageLayer/read[a, i]
}

check {
	all c,c': this/State, a:pageLayer/State, p,x:this/Page| 
		(retrieve[c,a] and loadCache[c,c',p,x]) => retrieve[c', a]
} for 3 but 2 this/State

check {
	all c,c': this/State, a:pageLayer/State, p:this/Page| 
		(retrieve[c,a] and removeCache[c,c',p]) => retrieve[c', a]
} for 3 but 2 this/State

pred cut[s,s': this/State, from, to : Int] {

	0 <= from and from < this/size[s]
	0 <= to and to < this/size[s]

	from <= to

	this/size[s'] = (to.sub[from]).add[1]
	all i : Int | 0 <= i and i < this/size[s'] => 
		this/read[s',i] = this/read[s,i.add[from]]
}

check {
	all c,c': this/State, a,a':pageLayer/State, from, to : Int | 
		(retrieve[c,a] and retrieve[c',a']) => 
			(this/cut[c,c',from,to] iff pageLayer/cut[a,a',from,to])
} for 3 but 2 this/State

run { some p, p2 : this/Page, s : this/State | {
				p != p2 
				some p.cache.s
				some p2.cache.s 
				p + p2 in elems[s.pages] 
		}
} for 4 but 1 this/State
