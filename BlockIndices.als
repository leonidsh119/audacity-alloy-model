
sig Sample {}

sig Block {
	s : seq Sample
} { #s <= 2 }

one sig Concrete {
	b : seq Block
} {
	b in Int lone -> Block 
}

// Creates a list of integers in range [from, to)
fun range[from, upto : Int] : set Int {
	{ n : Int | from <= n && n < upto } // This is the techniqur to create an iteration: create a list of integers representing the interation indices
}

// Count the number of samples in block subsequence from start upto j (not including).
// This is actually the index of the first sample in the block j
fun prec[j : Int] : Int {
	sum k : range[0, j] | #s[Concrete.b[k]]
}


fun blockIndex[i : Int] : Int {
	// Concrete.b.Block - the indices list of the blocks in sequence
	 max[ { j : Concrete.b.Block | prec[j] <= i } ] // Calculates the highest index of blocks where the sample can appear 
}

run { #b = 3 and all x : Block | #x.s > 0 }
