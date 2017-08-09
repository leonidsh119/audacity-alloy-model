open util/ordering[Time]

sig Time {}

sig Clip {
	blocks : (seq Block) -> Time,
	nextClip : Clip lone -> Time
}

sig Block {
	samples : (seq Sample) -> Time
}

sig Sample {
}

pred inv[t : Time] {

	all b1, b2 : Block, s : Sample | s in b1.samples.t.elems & b2.samples.t.elems => b1 = b2

	all c1, c2 : Clip, b : Block | b in c1.blocks.t.elems & c2.blocks.t.elems => c1 = c2

	all c : Clip | all b1, b2 : c.blocks.t.Block | c.blocks.t[b1] = c.blocks.t[b2] => b1 = b2

	all b : Block | all s1, s2 : b.samples.t.Sample | b.samples.t[s1] = b.samples.t[s2] => s1 = s2

	no ^(nextClip.t) & iden
} 


pred init[t:Time] {
	no nextClip.t
	no blocks.t
	no samples.t
}

pred import[t, t' : Time, newClip : Clip, newBlock : Block] {
// Preconditions
	no newClip.nextClip.t // newClip has no successors (since it is not an element in any sequence of clips)
	no clip : Clip | newBlock in elems[clip.blocks.t]	
	no newBlock.samples.t

// Postconditions
//	blocks.t' = newClip -> add[newClip.blocks.t, newBlock]
	blocks.t' = blocks.t + newClip -> add[newClip.blocks.t, newBlock]

// Invariant
	nextClip.t' = nextClip.t // newClip's nextClip remains the old one
//	blocks.t' = blocks.t // the newClip's blocks sequence remains the old one
	samples.t' = samples.t // newBlock's samples sequence remains the old one
}

check {
	all t : Time | inv[t]
}

fact {
	init[first]	
	all t, t' : Time | t->t' in next => some newClip: Clip, newBlock : Block | import[t , t', newClip, newBlock]
}

run {} for 5 but 5 Time
