
open util/ordering[Time]

sig Time {}

one sig Project {
	_tracks : Track -> Time,
}

sig Track {
	_clips : Clip -> Time,
	_firstClip : Clip lone -> Time 
}

sig Clip {
	_blocks : (seq Block) -> Time,
	_nextClip : Clip lone -> Time
}

sig Block {
	_samples : (seq Sample) -> Time
}

sig Sample {
}

pred inv[t : Time] {

	_tracks.t in Project lone -> Track

	all project : Project | all x : project._tracks.t | #x._clips.t > 0

	all b1, b2 : Block, s : Sample | s in b1._samples.t.elems & b2._samples.t.elems => b1 = b2

	all c1, c2 : Clip, b : Block | b in c1._blocks.t.elems & c2._blocks.t.elems => c1 = c2

	all c : Clip | all b1, b2 : c._blocks.t.Block | c._blocks.t[b1] = c._blocks.t[b2] => b1 = b2

	all b : Block | all s1, s2 : b._samples.t.Sample | b._samples.t[s1] = b._samples.t[s2] => s1 = s2

	_clips.t in Track lone -> Clip

	_firstClip.t in _clips.t
	
	all x : Track | no c : x._clips.t | c._nextClip.t = x._firstClip.t

	no ^(_nextClip.t) & iden

	all x : Track | x._firstClip.t in x._clips.t 

	all x, y : Clip | x->y in _nextClip.t => (_clips.t).x = (_clips.t).y
} 

pred init[t:Time] {
	no _tracks.t
	no _clips.t
	no _firstClip.t
	no _nextClip.t
	no _blocks.t
	no _samples.t
}

pred import[t, t' : Time, newTrack : Track, newClip : Clip, newBlock : Block, project : Project] {
// Preconditions
	no project : Project | newTrack in project._tracks.t //  newTrack doesn't belong to any project
	no track : Track | newClip in track._clips.t // newClip doesn't belong to any track
	no newClip._nextClip.t // newClip has no successors (since it is not an element in any sequence of clips)
	no clip : Clip | newBlock in elems[clip._blocks.t]
	no newBlock._samples.t // no samples for the newBlock

// Invariant
	_nextClip.t' = _nextClip.t // newClip's nextClip remains the old one
	_samples.t' = _samples.t // newBlock's samples sequence remains the old one

// Effects
	_tracks.t' = _tracks.t + (project -> newTrack) // The project's tracks collection is the old one with addition of the newTrack
	_clips.t' = _clips.t + (newTrack -> newClip) // The newTrack's clips collection is the old one with addition of the newClip
	_firstClip.t' = _firstClip.t + (newTrack -> newClip) // newClip is now the newTrack's firstClip
	_blocks.t' = _blocks.t + newClip -> add[newClip._blocks.t, newBlock]
}

pred cut[t, t' : Time, fromBlock, toBlock : Block,  track : Track, project : Project] {
// Preconditions
	track in project._tracks.t
	
// Invariant
	_tracks.t' = _tracks.t
	_samples.t' = _samples.t

// Effects
	// 1. One or more subsequent clips can be removed

	
	
	
	// 2. Possibly in preceeding clip to the removed sequence, the last block's samples list is trimmed from the end
	// 3. Possibly in succeeding clip to the removed sequence, the first block's samples list is trimmed from the start
}

check {
	all t : Time | inv[t]
}

fact {
	init[first]	
	all t, t' : Time | t->t' in next => some newTrack : Track, newClip: Clip, newBlock : Block | import[t , t', newTrack, newClip, newBlock, Project]
}

run {} for 5 but 6 Time
