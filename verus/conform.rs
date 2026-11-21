// Conformance of the real Automerge sync code (rust/automerge/src/sync.rs, sync/state.rs) to the protocol model
// (model.rs = proto_fix_live2.rs: Gen / Recv / Timeout steps).
//
// Layout: Part A trusted interface (external_body types and functions, each with a spec);
//         Part B code copied from the original with labelled changes ("CHANGE [Cn]" comments);
//         Part C abstraction function and conformance statements (as ensures of the copied functions).
// `verus/check_diff.py` diffs every copied function against the original source; the diff must equal
// `verus/expected_diff.txt`, so every change is visible.
use vstd::prelude::*;
use std::collections::BTreeSet;
use crate::model as M;
use crate::model::vset;

verus! {

// =====================================================================================
// Part A: trusted interface
// =====================================================================================

// CHANGE [C1]: ChangeHash (a 32-byte hash) is u64. The model's changes are ints with deps(c) < c; here the
// hash value is that int. Hash order = int order.
pub type ChangeHash = u64;

// ---- Bloom filter: opaque; bloom_set(b) = the hashes b reports as members (false positives allowed).
#[verifier::external_body]
pub struct BloomFilter { _p: () }
pub uninterp spec fn bloom_set(b: BloomFilter) -> ISet<int>;
impl BloomFilter {
    // TRUSTED [T1]: from_hashes has no false negatives.
    #[verifier::external_body]
    pub fn from_hashes(hashes: &Vec<ChangeHash>) -> (r: BloomFilter)
        ensures vset(hashes@).subset_of(bloom_set(r)),
    { unimplemented!() }
    // TRUSTED [T2]: the default filter (num_entries == 0) contains nothing (bloom.rs `contains_hash`).
    #[verifier::external_body]
    pub fn default() -> (r: BloomFilter) ensures bloom_set(r) == ISet::<int>::empty(),
    { unimplemented!() }
}

// ---- Have
pub struct Have { pub last_sync: Vec<ChangeHash>, pub bloom: BloomFilter }
impl Have {
    pub fn default() -> (r: Have)
        ensures r.last_sync@.len() == 0, bloom_set(r.bloom) == ISet::<int>::empty(),
    { Have { last_sync: Vec::new(), bloom: BloomFilter::default() } }
}
pub open spec fn abs_have(h: Have) -> M::Have { M::Have { last_sync: vset(h.last_sync@), bloom: bloom_set(h.bloom) } }
pub open spec fn abs_haves(v: Seq<Have>) -> Seq<M::Have> { Seq::new(v.len(), |i: int| abs_have(v[i])) }

// ---- Change, ChunkList, PatchLog, errors
#[verifier::external_body]
pub struct Change { _p: () }
pub uninterp spec fn chg_hash(c: Change) -> int;
pub open spec fn chgs_set(v: Seq<Change>) -> ISet<int> { ISet::new(|x: int| exists|i: int| 0 <= i < v.len() && chg_hash(v[i]) == x) }

#[verifier::external_body]
pub struct ChunkList { _p: () }
// the set of change hashes encoded in the chunks
pub uninterp spec fn chunk_set(c: ChunkList) -> ISet<int>;
pub uninterp spec fn bytes_set(b: Seq<u8>) -> ISet<int>;
impl ChunkList {
    // TRUSTED [T3]: an empty chunk list encodes no change.
    #[verifier::external_body]
    pub fn empty() -> (r: ChunkList) ensures chunk_set(r) == ISet::<int>::empty(),
    { unimplemented!() }
    // TRUSTED [T3]: is_empty (no chunks) holds exactly when the encoded change set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (r: bool) ensures r == (chunk_set(*self) == ISet::<int>::empty()),
    { unimplemented!() }
    // TRUSTED [T3]: join concatenates the chunks; the same changes are encoded.
    #[verifier::external_body]
    pub fn join(&self) -> (r: Vec<u8>) ensures bytes_set(r@) == chunk_set(*self),
    { unimplemented!() }
}

#[verifier::external_body]
pub struct PatchLog { _p: () }
impl PatchLog {
    #[verifier::external_body]
    pub fn inactive() -> (r: PatchLog) { unimplemented!() }
}
#[verifier::external_body]
#[derive(Debug)]
pub struct AutomergeError { _p: () }

// ---- the document. CHANGE [C2]: Automerge is reduced to its change graph; the change queue (`staged`) and
// the dependency function are part of the abstract graph.
#[verifier::external_body]
pub struct ChangeGraph { _p: () }
pub uninterp spec fn cg_doc(g: ChangeGraph) -> ISet<int>;     // applied changes
pub uninterp spec fn cg_queue(g: ChangeGraph) -> ISet<int>;   // queued (not yet applicable) changes
pub uninterp spec fn cg_deps(g: ChangeGraph) -> M::Deps;
pub uninterp spec fn cg_n(g: ChangeGraph) -> int;             // all hashes are < n

pub struct Automerge { pub change_graph: ChangeGraph }
pub open spec fn a_doc(a: Automerge) -> ISet<int> { cg_doc(a.change_graph) }
pub open spec fn a_queue(a: Automerge) -> ISet<int> { cg_queue(a.change_graph) }
pub open spec fn a_deps(a: Automerge) -> M::Deps { cg_deps(a.change_graph) }
pub open spec fn a_n(a: Automerge) -> int { cg_n(a.change_graph) }
// document invariant (assumed on entry, ensured by load_incremental)
pub open spec fn a_wf(a: Automerge) -> bool {
    M::wf(a_deps(a), a_n(a)) && M::closed(a_deps(a), a_doc(a)) && M::bounded(a_doc(a), a_n(a)) && M::bounded(a_queue(a), a_n(a))
    && a_queue(a).intersect(a_doc(a)) == ISet::<int>::empty()
    && (forall|c: int| #[trigger] a_queue(a).contains(c) ==> !a_deps(a)(c).subset_of(a_doc(a)))
}

pub open spec fn sorted_strict(v: Seq<u64>) -> bool { forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j] }

impl ChangeGraph {
    // TRUSTED [T4]: get_hashes(h) = all applied changes that are not ancestors-or-self of h.
    // (h must be applied changes: the real code's behaviour on unknown hashes is not examined.)
    // get_hashes(&[]) returns every applied change (`Cow::Borrowed(&self.hashes)`); it is the model's closure(empty) = empty case.
    // CHANGE [C3]: returns Vec instead of Cow<[ChangeHash]>.
    #[verifier::external_body]
    pub fn get_hashes(&self, have_deps: &Vec<ChangeHash>) -> (r: Vec<ChangeHash>)
        requires vset(have_deps@).subset_of(cg_doc(*self)),
        ensures vset(r@) == cg_doc(*self).difference(M::closure(cg_deps(*self), cg_n(*self), vset(have_deps@))),
    { unimplemented!() }
    #[verifier::external_body]
    pub fn len(&self) -> (r: usize) { unimplemented!() }
}

// ---- message flags (copied; the bit constants are literals) -------------------------------------
// CHANGE [C4]: derive attributes dropped; constants written as literals instead of `1 << n`.
#[derive(Clone, Copy)]
pub struct MessageFlags(pub u8);
impl MessageFlags {
    pub const SYNC_RESET: u8 = 1;
    pub const READ_ONLY: u8 = 2;
    pub const SUPPORTS_SYNC_RESET: u8 = 4;
    pub fn new() -> (r: Self) ensures r.0 == 0u8 { Self(0) }
    pub fn contains(self, flag: u8) -> (r: bool) ensures r == (self.0 & flag != 0) { self.0 & flag != 0 }
    pub fn set(&mut self, flag: u8) ensures final(self).0 == (old(self).0 | flag) { self.0 |= flag; }
}

pub enum MessageVersion { V1, V2 }
pub enum Capability { MessageV1, MessageV2, SyncReset }

// ---- Message
pub struct Message {
    pub heads: Vec<ChangeHash>,
    pub need: Vec<ChangeHash>,
    pub have: Vec<Have>,
    pub changes: ChunkList,
    pub flags: Option<MessageFlags>,
    pub version: MessageVersion,
}

// ---- State (copied; BTreeSet kept)
pub struct State {
    pub shared_heads: Vec<ChangeHash>,
    pub last_sent_heads: Vec<ChangeHash>,
    pub their_heads: Option<Vec<ChangeHash>>,
    pub their_need: Option<Vec<ChangeHash>>,
    pub their_have: Option<Vec<Have>>,
    pub sent_hashes: BTreeSet<ChangeHash>,
    pub in_flight: bool,
    pub have_responded: bool,
    pub their_capabilities: Option<Vec<Capability>>,
    pub read_only: bool,
    pub peer_read_only: bool,
    pub needs_reset: bool,
}

// ---- message builder (opaque). CHANGE [C5]: real MessageBuilder holds a Cow of hashes; here opaque with specs.
#[verifier::external_body]
pub struct MessageBuilder { _p: () }
pub uninterp spec fn mb_hashes(b: MessageBuilder) -> Seq<ChangeHash>;
pub uninterp spec fn mb_cset(b: MessageBuilder) -> ISet<int>;   // hashes of the encoded changes
pub uninterp spec fn mb_heads(b: MessageBuilder) -> Seq<ChangeHash>;
pub uninterp spec fn mb_need(b: MessageBuilder) -> Seq<ChangeHash>;
pub uninterp spec fn mb_have(b: MessageBuilder) -> Seq<Have>;
pub uninterp spec fn mb_flags(b: MessageBuilder) -> Option<MessageFlags>;

impl MessageBuilder {
    // TRUSTED [T5]: the builder for a list of changes records exactly their hashes, and encodes them.
    #[verifier::external_body]
    pub fn new(changes: Vec<Change>, sync_state: &State) -> (r: MessageBuilder)
        ensures vset(mb_hashes(r)) == chgs_set(changes@), mb_cset(r) == chgs_set(changes@),
            mb_heads(r).len() == 0, mb_need(r).len() == 0, mb_have(r).len() == 0, mb_flags(r) is None,
    { unimplemented!() }
    // TRUSTED [T14]: the V2 builder records the given hashes and encodes the changes in `data` (the saved document);
    // no heads, need, have, flags. (Real code: empty `data` gives `new_empty_v2`, with no hashes either way.)
    #[verifier::external_body]
    pub fn new_v2(data: Vec<u8>, hashes: Vec<ChangeHash>) -> (r: MessageBuilder)
        ensures vset(mb_hashes(r)) == vset(hashes@), mb_cset(r) == bytes_set(data@),
            mb_heads(r).len() == 0, mb_need(r).len() == 0, mb_have(r).len() == 0, mb_flags(r) is None,
    { unimplemented!() }
    #[verifier::external_body]
    pub fn is_empty(&self) -> (r: bool) ensures r == (mb_hashes(*self).len() == 0), { unimplemented!() }
    // CHANGE [C6]: returns &Vec<ChangeHash> instead of an iterator.
    #[verifier::external_body]
    pub fn hashes(&self) -> (r: &Vec<ChangeHash>) ensures r@ == mb_hashes(*self), { unimplemented!() }
    #[verifier::external_body]
    pub fn heads(self, h: Vec<ChangeHash>) -> (r: MessageBuilder)
        ensures mb_heads(r) == h@, mb_need(r) == mb_need(self), mb_have(r) == mb_have(self), mb_flags(r) == mb_flags(self),
            mb_cset(r) == mb_cset(self), mb_hashes(r) == mb_hashes(self),
    { unimplemented!() }
    #[verifier::external_body]
    pub fn have(self, h: Vec<Have>) -> (r: MessageBuilder)
        ensures mb_have(r) == h@, mb_need(r) == mb_need(self), mb_heads(r) == mb_heads(self), mb_flags(r) == mb_flags(self),
            mb_cset(r) == mb_cset(self), mb_hashes(r) == mb_hashes(self),
    { unimplemented!() }
    #[verifier::external_body]
    pub fn need(self, h: Vec<ChangeHash>) -> (r: MessageBuilder)
        ensures mb_need(r) == h@, mb_have(r) == mb_have(self), mb_heads(r) == mb_heads(self), mb_flags(r) == mb_flags(self),
            mb_cset(r) == mb_cset(self), mb_hashes(r) == mb_hashes(self),
    { unimplemented!() }
    #[verifier::external_body]
    pub fn flags(self, f: Option<MessageFlags>) -> (r: MessageBuilder)
        ensures mb_flags(r) == f, mb_need(r) == mb_need(self), mb_have(r) == mb_have(self), mb_heads(r) == mb_heads(self),
            mb_cset(r) == mb_cset(self), mb_hashes(r) == mb_hashes(self),
    { unimplemented!() }
    // TRUSTED [T5]: build puts the recorded fields in the message.
    #[verifier::external_body]
    pub fn build(self) -> (r: Message)
        ensures r.heads@ == mb_heads(self), r.need@ == mb_need(self), r.have@ == mb_have(self),
            r.flags == mb_flags(self), chunk_set(r.changes) == mb_cset(self),
    { unimplemented!() }
}

// ---- document operations (all trusted) -----------------------------------------------------------
impl Automerge {
    // TRUSTED [T6]: heads of the applied changes, as a strictly sorted vector.
    #[verifier::external_body]
    pub fn get_heads(&self) -> (r: Vec<ChangeHash>)
        ensures vset(r@) == M::heads(a_deps(*self), a_doc(*self)), sorted_strict(r@),
    { unimplemented!() }
    // TRUSTED [T6]
    #[verifier::external_body]
    pub fn has_change(&self, hash: &ChangeHash) -> (r: bool) ensures r == a_doc(*self).contains(*hash as int),
    { unimplemented!() }
    // TRUSTED [T7]: = model `missing` (the first hash on each path from `start` that is neither applied nor queued,
    // going through the deps of queued changes). CHANGE [C7]: takes the Option<Vec> directly instead of an iterator.
    #[verifier::external_body]
    pub fn missing_deps_from(&self, start: &Option<Vec<ChangeHash>>) -> (r: Vec<ChangeHash>)
        ensures vset(r@) == M::missing(a_deps(*self), a_n(*self), a_doc(*self), a_queue(*self), abs_opt_set(*start)),
    { unimplemented!() }
    // TRUSTED [T8]: = model `hashes_to_send` (hn1.rs in vlm42_amproto proves a copy of the body against a graph spec;
    // that proof is NOT linked to this one).
    #[verifier::external_body]
    pub fn get_hashes_to_send(&self, have: &[Have], need: &[ChangeHash]) -> (r: Result<Vec<ChangeHash>, AutomergeError>)
        ensures r is Ok,
            r is Ok ==> vset(r->Ok_0@) == M::hashes_to_send(a_deps(*self), a_n(*self), a_doc(*self), abs_haves(have@), vset(need@)),
    { unimplemented!() }
    // TRUSTED [T9]: the changes for a set of applied hashes
    #[verifier::external_body]
    pub fn get_changes_by_hashes(&self, hashes: &Vec<ChangeHash>) -> (r: Result<Vec<Change>, AutomergeError>)
        requires vset(hashes@).subset_of(a_doc(*self)),
        ensures r is Ok, r is Ok ==> chgs_set(r->Ok_0@) == vset(hashes@),
    { unimplemented!() }
    // TRUSTED [T14]: the saved document encodes exactly the applied changes.
    #[verifier::external_body]
    pub fn save(&self) -> (r: Vec<u8>) ensures bytes_set(r@) == a_doc(*self), { unimplemented!() }
    // TRUSTED [T10]: apply the changes encoded in `data`: the new doc is a maximal dependency-closed extension of the
    // old doc using the queue plus the new changes (= model drain_ok); the new queue is the rest.
    // On Err nothing is said about the document.
    #[verifier::external_body]
    pub fn load_incremental_log_patches(&mut self, data: &Vec<u8>, patch_log: &mut PatchLog) -> (r: Result<usize, AutomergeError>)
        requires a_wf(*old(self)), M::bounded(bytes_set(data@), a_n(*old(self))),
        ensures
            a_deps(*final(self)) == a_deps(*old(self)), a_n(*final(self)) == a_n(*old(self)),
            r is Ok ==> (M::drain_ok(a_deps(*old(self)), a_doc(*old(self)), a_queue(*old(self)).union(bytes_set(data@)), a_doc(*final(self)))
                && a_queue(*final(self)) == a_queue(*old(self)).union(bytes_set(data@)).difference(a_doc(*final(self)))
                && a_wf(*final(self))),
    { unimplemented!() }
    // TRUSTED [T11]: removes from `changes` the ancestors-or-self of those `heads` that are applied.
    #[verifier::external_body]
    pub fn filter_changes(&self, heads: &[ChangeHash], changes: &mut BTreeSet<ChangeHash>) -> (r: Result<(), AutomergeError>)
        ensures r is Ok,
            bset(*final(changes)) == bset(*old(changes)).difference(
                M::closure(a_deps(*self), a_n(*self), vset(heads@).intersect(a_doc(*self)))),
    { unimplemented!() }
}

// TRUSTED [T12]: advance_heads. CHANGE [C8]: takes Vec<ChangeHash> instead of HashSets (no HashSet in verified code).
// result = (new \ old) union (shared intersect new), sorted without duplicates.
#[verifier::external_body]
pub fn advance_heads(my_old_heads: &Vec<ChangeHash>, my_new_heads: &Vec<ChangeHash>, our_old_shared_heads: &Vec<ChangeHash>) -> (r: Vec<ChangeHash>)
    ensures vset(r@) == vset(my_new_heads@).difference(vset(my_old_heads@)).union(vset(our_old_shared_heads@).intersect(vset(my_new_heads@))),
{ unimplemented!() }

// TRUSTED [T13]: replaces `shared_heads.iter().chain(known_heads).copied().unique().sorted().collect()` (itertools).
// CHANGE [C9]
#[verifier::external_body]
pub fn union_sorted(a: &Vec<ChangeHash>, b: &Vec<ChangeHash>) -> (r: Vec<ChangeHash>)
    ensures vset(r@) == vset(a@).union(vset(b@)),
{ unimplemented!() }

// view of a BTreeSet as a set of ints
pub open spec fn bset(s: BTreeSet<ChangeHash>) -> ISet<int> { ISet::new(|x: int| exists|k: u64| s@.contains(k) && k as int == x) }
pub open spec fn abs_opt_set(o: Option<Vec<ChangeHash>>) -> ISet<int> { match o { Some(v) => vset(v@), None => ISet::empty() } }

// =====================================================================================
// Part B/C: copied code with conformance specs
// =====================================================================================

// ---- helpers introduced by CHANGE (verified, not trusted) -------------------------------------------
// CHANGE [C25]: `a == b` on Vec<ChangeHash> replaced by `vec_eq` (Verus has no spec for Vec's PartialEq).
pub fn vec_eq(a: &Vec<ChangeHash>, b: &Vec<ChangeHash>) -> (r: bool) ensures r == (a@ == b@),
{
    if a.len() != b.len() { return false; }
    let mut i = 0;
    while i < a.len()
        invariant 0 <= i <= a.len(), a.len() == b.len(), forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] { return false; }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

// CHANGE [C10]: replaces `our_need.iter().all(|hash| their_heads_set.contains(hash))`
pub fn all_in_opt(need: &Vec<ChangeHash>, their: &Option<Vec<ChangeHash>>) -> (r: bool)
    ensures r == vset(need@).subset_of(abs_opt_set(*their)),
{
    let mut i = 0;
    while i < need.len()
        invariant 0 <= i <= need.len(), forall|j: int| 0 <= j < i ==> abs_opt_set(*their).contains(need@[j] as int),
        decreases need.len() - i,
    {
        let ok = match their { Some(t) => t.contains(&need[i]), None => false };
        if !ok {
            assert(!vset(need@).subset_of(abs_opt_set(*their))) by {
                assert(vset(need@).contains(need@[i as int] as int));
                if let Some(t) = their { assert(!t@.contains(need@[i as int])); assert(!vset(t@).contains(need@[i as int] as int)) by {
                    if vset(t@).contains(need@[i as int] as int) { let k = choose|k: int| 0 <= k < t@.len() && t@[k] as int == need@[i as int] as int; assert(t@[k] == need@[i as int]); }
                } }
            }
            return false;
        }
        i += 1;
    }
    assert(vset(need@).subset_of(abs_opt_set(*their))) by {
        assert forall|x: int| vset(need@).contains(x) implies abs_opt_set(*their).contains(x) by {
            let k = choose|k: int| 0 <= k < need@.len() && need@[k] as int == x;
            assert(abs_opt_set(*their).contains(need@[k] as int));
        }
    }
    true
}

impl Automerge {
    // CHANGE [C11]: replaces `v.iter().all(|hash| self.has_change(hash))`
    pub fn has_all(&self, v: &Vec<ChangeHash>) -> (r: bool)
        ensures r == vset(v@).subset_of(a_doc(*self)),
    {
        let mut i = 0;
        while i < v.len()
            invariant 0 <= i <= v.len(), forall|j: int| 0 <= j < i ==> a_doc(*self).contains(v@[j] as int),
            decreases v.len() - i,
        {
            if !self.has_change(&v[i]) {
                assert(vset(v@).contains(v@[i as int] as int));
                return false;
            }
            i += 1;
        }
        assert forall|x: int| vset(v@).contains(x) implies a_doc(*self).contains(x) by {
            let k = choose|k: int| 0 <= k < v@.len() && v@[k] as int == x;
            assert(a_doc(*self).contains(v@[k] as int));
        }
        true
    }

    // CHANGE [C12]: replaces `heads.iter().filter(|head| self.has_change(head)).collect::<Vec<_>>()`
    // The length test `known_heads.len() == message_heads.len()` then means "all heads are known".
    pub fn known_heads(&self, heads: &Vec<ChangeHash>) -> (r: Vec<ChangeHash>)
        ensures vset(r@) == vset(heads@).intersect(a_doc(*self)),
            (r@.len() == heads@.len()) == vset(heads@).subset_of(a_doc(*self)),
    {
        let mut r: Vec<ChangeHash> = Vec::new();
        let mut i = 0;
        while i < heads.len()
            invariant 0 <= i <= heads.len(),
                forall|x: int| vset(r@).contains(x) <==> (exists|j: int| 0 <= j < i && heads@[j] as int == x && a_doc(*self).contains(x)),
                r@.len() <= i,
                (r@.len() == i) <==> (forall|j: int| 0 <= j < i ==> a_doc(*self).contains(heads@[j] as int)),
            decreases heads.len() - i,
        {
            if self.has_change(&heads[i]) {
                let ghost r0 = r@;
                r.push(heads[i]);
                assert forall|x: int| vset(r@).contains(x) <==> (exists|j: int| 0 <= j < i + 1 && heads@[j] as int == x && a_doc(*self).contains(x)) by {
                    if vset(r@).contains(x) {
                        let k = choose|k: int| 0 <= k < r@.len() && r@[k] as int == x;
                        if k < r0.len() { assert(vset(r0).contains(x)); } else { assert(heads@[i as int] as int == x); }
                    }
                    if exists|j: int| 0 <= j < i + 1 && heads@[j] as int == x && a_doc(*self).contains(x) {
                        let j = choose|j: int| 0 <= j < i + 1 && heads@[j] as int == x && a_doc(*self).contains(x);
                        if j < i { assert(vset(r0).contains(x)); let k = choose|k: int| 0 <= k < r0.len() && r0[k] as int == x; assert(r@[k] == r0[k]); }
                        else { assert(r@[r0.len() as int] as int == x); }
                    }
                }
            }
            i += 1;
        }
        assert forall|x: int| vset(r@).contains(x) <==> (vset(heads@).contains(x) && a_doc(*self).contains(x)) by {
            if vset(r@).contains(x) { let j = choose|j: int| 0 <= j < i && heads@[j] as int == x && a_doc(*self).contains(x); assert(heads@[j] == heads@[j]); }
            if vset(heads@).contains(x) && a_doc(*self).contains(x) { let j = choose|j: int| 0 <= j < heads@.len() && heads@[j] as int == x; }
        }
        assert(vset(r@) =~= vset(heads@).intersect(a_doc(*self)));
        assert((r@.len() == heads@.len()) == vset(heads@).subset_of(a_doc(*self))) by {
            if vset(heads@).subset_of(a_doc(*self)) {
                assert forall|j: int| 0 <= j < heads@.len() implies a_doc(*self).contains(heads@[j] as int) by { assert(vset(heads@).contains(heads@[j] as int)); }
            } else {
                let x = choose|x: int| vset(heads@).contains(x) && !a_doc(*self).contains(x);
                let j = choose|j: int| 0 <= j < heads@.len() && heads@[j] as int == x;
                assert(!a_doc(*self).contains(heads@[j] as int));
            }
        }
        r
    }
}

// CHANGE [C13]: replaces `all_hashes.into_iter().filter(|hash| !sent.contains(hash)).collect()`
pub fn filter_unsent(all_hashes: Vec<ChangeHash>, sent: &BTreeSet<ChangeHash>) -> (r: Vec<ChangeHash>)
    ensures vset(r@) == vset(all_hashes@).difference(bset(*sent)),
{
    let mut r: Vec<ChangeHash> = Vec::new();
    let mut i = 0;
    while i < all_hashes.len()
        invariant 0 <= i <= all_hashes.len(),
            forall|x: int| vset(r@).contains(x) <==> (exists|j: int| 0 <= j < i && all_hashes@[j] as int == x && !bset(*sent).contains(x)),
        decreases all_hashes.len() - i,
    {
        let h = all_hashes[i];
        if !sent.contains(&h) {
            let ghost r0 = r@;
            r.push(h);
            assert forall|x: int| vset(r@).contains(x) <==> (exists|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x)) by {
                if vset(r@).contains(x) {
                    let k = choose|k: int| 0 <= k < r@.len() && r@[k] as int == x;
                    if k < r0.len() { assert(vset(r0).contains(x)); } else { assert(h as int == x); }
                }
                if exists|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x) {
                    let j = choose|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x);
                    if j < i { assert(vset(r0).contains(x)); let k = choose|k: int| 0 <= k < r0.len() && r0[k] as int == x; assert(r@[k] == r0[k]); }
                    else { assert(r@[r0.len() as int] as int == x); }
                }
            }
        } else {
            assert forall|x: int| vset(r@).contains(x) <==> (exists|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x)) by {
                if exists|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x) {
                    let j = choose|j: int| 0 <= j < i + 1 && all_hashes@[j] as int == x && !bset(*sent).contains(x);
                    if j == i { assert(bset(*sent).contains(h as int)); }
                }
            }
        }
        i += 1;
    }
    assert(vset(r@) =~= vset(all_hashes@).difference(bset(*sent))) by {
        assert forall|x: int| vset(r@).contains(x) <==> (vset(all_hashes@).contains(x) && !bset(*sent).contains(x)) by {
            if vset(all_hashes@).contains(x) && !bset(*sent).contains(x) { let j = choose|j: int| 0 <= j < all_hashes@.len() && all_hashes@[j] as int == x; }
        }
    }
    r
}

// CHANGE [C14]: replaces `sync_state.sent_hashes.extend(message_builder.hashes())` (BTreeSet::extend has no vstd spec).
pub fn extend_hashes(set: &mut BTreeSet<ChangeHash>, hashes: &Vec<ChangeHash>)
    ensures bset(*final(set)) == bset(*old(set)).union(vset(hashes@)),
{
    let mut i = 0;
    while i < hashes.len()
        invariant 0 <= i <= hashes.len(),
            bset(*set) == bset(*old(set)).union(ISet::new(|x: int| exists|j: int| 0 <= j < i && hashes@[j] as int == x)),
        decreases hashes.len() - i,
    {
        let ghost s0 = *set;
        set.insert(hashes[i]);
        assert(bset(*set) =~= bset(*old(set)).union(ISet::new(|x: int| exists|j: int| 0 <= j < i + 1 && hashes@[j] as int == x))) by {
            assert(set@ == s0@.insert(hashes@[i as int]));
            assert forall|x: int| bset(*set).contains(x) <==> (bset(*old(set)).contains(x) || exists|j: int| 0 <= j < i + 1 && hashes@[j] as int == x) by {
                if bset(*set).contains(x) {
                    let k = choose|k: u64| set@.contains(k) && k as int == x;
                    if k != hashes@[i as int] { assert(s0@.contains(k)); assert(bset(s0).contains(x)); } else { assert(hashes@[i as int] as int == x); }
                }
                if bset(*old(set)).contains(x) { assert(bset(s0).contains(x)); let k = choose|k: u64| s0@.contains(k) && k as int == x; assert(set@.contains(k)); }
                if exists|j: int| 0 <= j < i + 1 && hashes@[j] as int == x {
                    let j = choose|j: int| 0 <= j < i + 1 && hashes@[j] as int == x;
                    if j < i { assert(bset(s0).contains(x)); let k = choose|k: u64| s0@.contains(k) && k as int == x; assert(set@.contains(k)); }
                    else { assert(set@.contains(hashes@[i as int])); }
                }
            }
        }
        i += 1;
    }
    assert(bset(*set) =~= bset(*old(set)).union(vset(hashes@))) by {
        assert(ISet::new(|x: int| exists|j: int| 0 <= j < hashes@.len() && hashes@[j] as int == x) =~= vset(hashes@));
    }
}

// =====================================================================================
// State methods (copied)
// =====================================================================================
impl State {
    // CHANGE [C15]: `.as_ref().map(|caps| caps.contains(&Capability::X)).unwrap_or(false)` written as a match + loop helper.
    pub fn supports_v2_messages(&self) -> (r: bool) ensures r == st_v2(*self),
    {
        match &self.their_capabilities {
            Some(caps) => has_cap(caps, 1),
            None => false,
        }
    }
    pub(crate) fn peer_supports_sync_reset(&self) -> (r: bool) ensures r == st_sr(*self),
    {
        match &self.their_capabilities {
            Some(caps) => has_cap(caps, 2),
            None => false,
        }
    }
    pub fn is_peer_read_only(&self) -> (r: bool) ensures r == self.peer_read_only,
    {
        self.peer_read_only
    }
    // CHANGE [C16]: `self.their_heads == Some(vec![])` kept; vec![] is `Vec::new()`.
    pub(crate) fn send_doc(&self) -> (r: bool) ensures r ==> st_v2(*self),
    {
        let empty = match &self.their_heads { Some(h) => h.len() == 0, None => false };
        empty && self.supports_v2_messages()
    }
    // CHANGE [C17]: `?` replaced by match; slices from Vec::as_slice.
    pub(crate) fn their(&self) -> (r: Option<(&[Have], &[ChangeHash])>)
        ensures (self.their_have is Some && self.their_need is Some) == (r is Some),
            r is Some ==> (r->Some_0.0@ == self.their_have->Some_0@ && r->Some_0.1@ == self.their_need->Some_0@),
    {
        let have = match self.their_have.as_ref() { Some(h) => h, None => return None };
        let need = match self.their_need.as_ref() { Some(n) => n, None => return None };
        Some((have.as_slice(), need.as_slice()))
    }

    /// Tell the state that a reply from the peer is overdue, so a message may have been lost.
    /// (This is the proposed fix; the model's Timeout step.)
    pub fn on_timeout(&mut self)
        ensures
            abs_state(*final(self)) == M::tmo(abs_state(*old(self))),
            final(self).read_only == old(self).read_only, final(self).peer_read_only == old(self).peer_read_only,
            forall|a: Automerge| st_wf(*final(self), a) == st_wf(*old(self), a),
    {
        self.sent_hashes.clear();
        self.in_flight = false;
        proof { assert(bset(self.sent_hashes) =~= ISet::<int>::empty()); assert(abs_state(*self) =~= M::tmo(abs_state(*old(self)))); }
    }
}

// capability test helper for [C15]; which: 1 = MessageV2, 2 = SyncReset
pub open spec fn cap_is(c: Capability, which: int) -> bool {
    match c { Capability::MessageV2 => which == 1, Capability::SyncReset => which == 2, Capability::MessageV1 => false }
}
pub open spec fn st_v2(s: State) -> bool { match s.their_capabilities { Some(c) => exists|i: int| 0 <= i < c@.len() && cap_is(c@[i], 1), None => false } }
pub open spec fn st_sr(s: State) -> bool { match s.their_capabilities { Some(c) => exists|i: int| 0 <= i < c@.len() && cap_is(c@[i], 2), None => false } }
pub fn has_cap(caps: &Vec<Capability>, which: u8) -> (r: bool)
    requires which == 1 || which == 2,
    ensures r == (exists|i: int| 0 <= i < caps@.len() && cap_is(caps@[i], which as int)),
{
    let mut i = 0;
    while i < caps.len()
        invariant 0 <= i <= caps.len(), forall|j: int| 0 <= j < i ==> !cap_is(caps@[j], which as int),
        decreases caps.len() - i,
    {
        let hit = match &caps[i] { Capability::MessageV2 => which == 1, Capability::SyncReset => which == 2, Capability::MessageV1 => false };
        if hit { return true; }
        i += 1;
    }
    false
}

// =====================================================================================
// Message::reset (copied)
// =====================================================================================
impl Message {
    pub(crate) fn reset(our_heads: Vec<ChangeHash>) -> (r: Message)
        ensures r.heads@ == our_heads@, r.need@.len() == 0, r.have@.len() == 1, r.have@[0].last_sync@.len() == 0,
            bloom_set(r.have@[0].bloom) == ISet::<int>::empty(), chunk_set(r.changes) == ISet::<int>::empty(),
            r.flags is Some && r.flags->Some_0.0 == 4u8,
    {
        Message {
            heads: our_heads,
            need: Vec::new(),
            have: vec![Have::default()],
            changes: ChunkList::empty(),
            flags: {
                let mut f = MessageFlags::new();
                f.set(MessageFlags::SUPPORTS_SYNC_RESET);
                assert((0u8 | 4u8) == 4u8) by (bit_vector);
                Some(f)
            },
            version: MessageVersion::V1,
        }
    }
}

// =====================================================================================
// Part C: abstraction function and invariants
// =====================================================================================
pub open spec fn abs_vec_opt(o: Option<Vec<ChangeHash>>) -> Option<ISet<int>> { match o { Some(v) => Some(vset(v@)), None => None } }
// The part of the abstraction that does not need the document.
pub open spec fn abs_state(s: State) -> M::Peer {
    M::Peer {
        doc: ISet::empty(), queue: ISet::empty(),
        shared_heads: vset(s.shared_heads@), last_sent_heads: vset(s.last_sent_heads@),
        their_heads: abs_vec_opt(s.their_heads), their_need: abs_vec_opt(s.their_need),
        their_have: match s.their_have { Some(v) => Some(abs_haves(v@)), None => None },
        sent_hashes: bset(s.sent_hashes), in_flight: s.in_flight, have_responded: s.have_responded, needs_reset: s.needs_reset,
    }
}
pub open spec fn abs_peer(a: Automerge, s: State) -> M::Peer {
    M::Peer { doc: a_doc(a), queue: a_queue(a), ..abs_state(s) }
}
pub open spec fn abs_msg(m: Message) -> M::Msg {
    M::Msg { heads: vset(m.heads@), need: vset(m.need@), have: abs_haves(m.have@), changes: chunk_set(m.changes) }
}
// State invariant (assumed on entry, preserved):
// - last_sent_heads and their_heads are strictly sorted (so Vec equality is set equality)
// - shared_heads are applied changes (so get_hashes is only asked about known hashes)
// - at most one `have` (all of them are used by get_hashes_to_send, only the first is checked by the reset test)
pub open spec fn st_wf(s: State, a: Automerge) -> bool {
    sorted_strict(s.last_sent_heads@)
    && (match s.their_heads { Some(h) => sorted_strict(h@), None => true })
    && vset(s.shared_heads@).subset_of(a_doc(a))
    && (match s.their_have { Some(h) => h@.len() <= 1, None => true })
}
// Messages the model can describe: heads sorted, at most one have, change hashes below n; flags (if present) do not
// carry SYNC_RESET or READ_ONLY (these two are not modelled).
pub open spec fn msg_wf(m: Message, a: Automerge) -> bool {
    sorted_strict(m.heads@) && m.have@.len() <= 1 && M::bounded(chunk_set(m.changes), a_n(a))
    && (match m.flags { Some(f) => f.0 & 1 == 0 && f.0 & 2 == 0, None => true })
}
// What a generated message must satisfy so that the peer may call receive_sync_message on it (see msg_wf): the
// heads are sorted and the flags carry neither SYNC_RESET nor READ_ONLY. (bounded changes and <= 1 have follow from gen_post.)
pub open spec fn out_wf(r: Option<Message>) -> bool {
    match r { None => true, Some(m) => sorted_strict(m.heads@) && (match m.flags { Some(f) => f.0 & 1 == 0 && f.0 & 2 == 0, None => true }) }
}
// Fragment of generate_sync_message that the model describes: no read-only mode (either side). Peer capabilities
// (MessageV2, SyncReset) are unrestricted: whole-document sends are the model's GenDoc step.
// the model's `fake` flag: the peer is not known to support SYNC_RESET
pub open spec fn fake_of(s: State) -> bool { !st_sr(s) }
pub open spec fn gen_frag(s: State) -> bool { !s.read_only && !s.peer_read_only }

pub open spec fn opt_set_eq(o: Option<Vec<ChangeHash>>) -> bool { M::opt_set(abs_vec_opt(o)) == abs_opt_set(o) }
pub open spec fn gen_msg_ok(p: M::Peer, r: Option<Message>, om: Option<M::Msg>) -> bool {
    match (r, om) {
        (None, None) => true,
        (Some(m), Some(mm)) => abs_msg(m) == mm,   // [M1 closed] the model's reset message has the code's one empty Have
        _ => false,
    }
}

// =====================================================================================
// lemmas
// =====================================================================================
// Strictly sorted vectors with the same elements are equal (so Vec == is set ==).
pub proof fn lemma_sorted_eq(a: Seq<u64>, b: Seq<u64>)
    requires sorted_strict(a), sorted_strict(b), vset(a) == vset(b),
    ensures a == b,
    decreases a.len(),
{
    if a.len() == 0 {
        if b.len() > 0 { assert(vset(b).contains(b[0] as int)); assert(vset(a).contains(b[0] as int)); }
        assert(b.len() == 0);
    } else {
        assert(vset(a).contains(a.last() as int));
        assert(vset(b).contains(a.last() as int));
        assert(b.len() > 0) by { if b.len() == 0 { } }
        assert(vset(b).contains(b.last() as int));
        assert(vset(a).contains(b.last() as int));
        let kb = choose|k: int| 0 <= k < b.len() && b[k] as int == a.last() as int;
        let ka = choose|k: int| 0 <= k < a.len() && a[k] as int == b.last() as int;
        assert(a[ka] <= a.last()); assert(b[kb] <= b.last());
        assert(a.last() == b.last());
        let a2 = a.drop_last(); let b2 = b.drop_last();
        assert(sorted_strict(a2)); assert(sorted_strict(b2));
        assert(vset(a2) =~= vset(b2)) by {
            assert forall|x: int| vset(a2).contains(x) <==> vset(b2).contains(x) by {
                if vset(a2).contains(x) {
                    let i = choose|i: int| 0 <= i < a2.len() && a2[i] as int == x;
                    assert(vset(a).contains(x)); let j = choose|j: int| 0 <= j < b.len() && b[j] as int == x;
                    if j == b.len() - 1 { assert(a[i] < a[a.len() - 1]); assert(false); }
                    assert(b2[j] == b[j]);
                }
                if vset(b2).contains(x) {
                    let i = choose|i: int| 0 <= i < b2.len() && b2[i] as int == x;
                    assert(vset(b).contains(x)); let j = choose|j: int| 0 <= j < a.len() && a[j] as int == x;
                    if j == a.len() - 1 { assert(b[i] < b[b.len() - 1]); assert(false); }
                    assert(a2[j] == a[j]);
                }
            }
        }
        lemma_sorted_eq(a2, b2);
        assert(a =~= a2.push(a.last())); assert(b =~= b2.push(b.last()));
        assert(a =~= b);
    }
}
pub proof fn lemma_reach_empty(d: M::Deps, k: nat)
    ensures M::reach(d, ISet::<int>::empty(), k) == ISet::<int>::empty(),
    decreases k,
{
    if k == 0 { } else {
        lemma_reach_empty(d, (k - 1) as nat);
        assert(M::reach(d, ISet::<int>::empty(), k) =~= ISet::<int>::empty());
    }
}
pub proof fn lemma_hts_subset(d: M::Deps, n: int, s: ISet<int>, have: Seq<M::Have>, need: ISet<int>)
    ensures M::hashes_to_send(d, n, s, have, need).subset_of(s),
{
    let hts = M::hashes_to_send(d, n, s, have, need);
    assert forall|x: int| hts.contains(x) implies s.contains(x) by {}
}


// the contract of receiving a message: on Ok, the effect is the model's Recv step (with s2 = the new document);
// on Err, only in_flight was cleared in the modelled state (the document is unspecified).
pub open spec fn recv_post(a0: Automerge, s0: State, msg: Message, a1: Automerge, s1: State, r: Result<(), AutomergeError>) -> bool {
    let d = a_deps(a0); let n = a_n(a0);
    let p = abs_peer(a0, s0); let m = abs_msg(msg); let s2 = a_doc(a1);
    match r {
        Ok(_) => {
            a_wf(a1) && st_wf(s1, a1) && a_deps(a1) == d && a_n(a1) == n
            && M::bounded(p.queue.union(m.changes), n)
            && M::drain_ok(d, p.doc, p.queue.union(m.changes), s2)
            && (m.changes == ISet::<int>::empty() ==> s2 == p.doc)
            && abs_peer(a1, s1) == M::recv(d, n, p, m, s2)
            && s1.read_only == s0.read_only && (!s0.peer_read_only ==> !s1.peer_read_only)
        }
        Err(_) => abs_state(s1) == M::Peer { in_flight: false, ..abs_state(s0) },
    }
}

// The contract of generate_sync_message: the step is the model's Gen (send = send_set) or GenDoc (send = whole
// document); `fake` = peer not known to support SYNC_RESET.
pub open spec fn gen_post(a: Automerge, s0: State, s1: State, r: Option<Message>) -> bool {
    st_wf(s1, a) && s1.read_only == s0.read_only && s1.peer_read_only == s0.peer_read_only
    && exists|bloom: ISet<int>, send: ISet<int>| {
        &&& a_doc(a).difference(M::closure(a_deps(a), a_n(a), vset(s0.shared_heads@))).subset_of(bloom)
        &&& (send == M::send_set(a_deps(a), a_n(a), abs_peer(a, s0)) || send == a_doc(a))
        &&& abs_peer(a, s1) == (#[trigger] M::gen_s(a_deps(a), a_n(a), abs_peer(a, s0), bloom, fake_of(s0), send)).0
        &&& gen_msg_ok(abs_peer(a, s0), r, M::gen_s(a_deps(a), a_n(a), abs_peer(a, s0), bloom, fake_of(s0), send).1)
    }
}

// =====================================================================================
// generate_sync_message and helpers (copied)
// =====================================================================================
impl Automerge {
    // CHANGE [C18]: `hashes.iter()` -> `&hashes`.
    fn make_bloom_filter(&self, last_sync: Vec<ChangeHash>) -> (r: Have)
        requires vset(last_sync@).subset_of(a_doc(*self)),
        ensures r.last_sync@ == last_sync@,
            a_doc(*self).difference(M::closure(a_deps(*self), a_n(*self), vset(last_sync@))).subset_of(bloom_set(r.bloom)),
    {
        let hashes = self.change_graph.get_hashes(&last_sync);
        Have {
            bloom: BloomFilter::from_hashes(&hashes),
            last_sync,
        }
    }

    pub fn generate_sync_message(&self, sync_state: &mut State) -> (r: Option<Message>)
        requires a_wf(*self), st_wf(*old(sync_state), *self), gen_frag(*old(sync_state)),
        ensures gen_post(*self, *old(sync_state), *final(sync_state), r),
            // the flag SYNC_RESET is set only when needs_reset and the peer supports it
            (!old(sync_state).needs_reset || !st_sr(*old(sync_state))) ==> out_wf(r),
    {
        let ghost s0 = *sync_state;
        let ghost d = a_deps(*self);
        let ghost n = a_n(*self);
        let ghost p = abs_peer(*self, s0);
        let ghost fake = fake_of(s0);
        let our_heads = self.get_heads();

        // CHANGE [C19]: `vec![]` needs a type; `missing_deps_from(sync_state.their_heads.iter().flatten().copied())`
        // is `missing_deps_from(&sync_state.their_heads)` (see C7).
        let our_need = if sync_state.read_only {
            let v: Vec<ChangeHash> = Vec::new();
            v
        } else {
            self.missing_deps_from(&sync_state.their_heads)
        };

        // CHANGE [C10]: the HashSet `their_heads_set` and `.all(..)` replaced by `all_in_opt`.
        let our_have = if all_in_opt(&our_need, &sync_state.their_heads) {
            vec![self.make_bloom_filter(sync_state.shared_heads.clone())]
        } else {
            Vec::new()
        };
        let ghost bloom = if our_have@.len() > 0 { bloom_set(our_have@[0].bloom) } else { ISet::new(|x: int| true) };
        assert(a_doc(*self).difference(M::closure(d, n, vset(s0.shared_heads@))).subset_of(bloom));
        assert(vset(our_need@) == M::missing(d, n, a_doc(*self), a_queue(*self), abs_opt_set(s0.their_heads)));
        assert(abs_haves(our_have@) =~= (if vset(our_need@).subset_of(abs_opt_set(s0.their_heads)) {
            seq![M::Have { last_sync: vset(s0.shared_heads@), bloom: bloom }] } else { Seq::empty() }));

        // CHANGE [C24]: `if let Some(first_have) = their_have.first().as_ref()` -> length test and index 0;
        // `.all(|hash| self.has_change(hash))` -> `has_all` (C11).
        if let Some(their_have) = &sync_state.their_have {
            if their_have.len() > 0 {
                if !self.has_all(&their_have[0].last_sync) {
                    assert(M::must_reset(p));
                    let ghost oh = M::heads(d, a_doc(*self));
                    let ghost our_heads_s = our_heads@;
                    let rm = Message::reset(our_heads);
                    assert(vset(rm.need@) == ISet::<int>::empty()) by { assert(vset(rm.need@) =~= ISet::<int>::empty()); }
                    assert(vset(rm.have@[0].last_sync@) == ISet::<int>::empty()) by { assert(vset(rm.have@[0].last_sync@) =~= ISet::<int>::empty()); }
                    assert(abs_haves(rm.have@) =~= seq![M::Have { last_sync: ISet::empty(), bloom: ISet::empty() }]);
                    assert(vset(rm.heads@) == oh);
                    let r = Some(rm);
                    let ghost send0 = M::send_set(d, n, p);
                    proof { M::lemma_reset_msg(oh); }
                    assert(abs_peer(*self, *sync_state) == M::gen_s(d, n, p, bloom, fake, send0).0);
                    assert(abs_msg(rm) =~= M::reset_msg(oh));
                    assert(gen_msg_ok(p, r, M::gen_s(d, n, p, bloom, fake, send0).1));
                    assert(st_wf(*sync_state, *self));
                    assert((4u8 & 1u8) == 0u8 && (4u8 & 2u8) == 0u8) by (bit_vector);
                    assert(sorted_strict(our_heads_s));
                    assert(out_wf(r));
                    return r;
                }
            }
        }
        assert(!M::must_reset(p)) by {
            if let Some(h) = p.their_have { if h.len() > 0 { assert(h[0].last_sync == vset(s0.their_have->Some_0@[0].last_sync@)); } }
        }

        let message_builder = if sync_state.is_peer_read_only() {
            MessageBuilder::new(Vec::new(), sync_state)
        } else if let Some((their_have, their_need)) = sync_state.their() {
            if sync_state.send_doc() {
                let hashes = self.change_graph.get_hashes(&Vec::new());
                proof { lemma_reach_empty(d, n as nat); assert(vset(Seq::<u64>::empty()) =~= ISet::<int>::empty()); assert(vset(hashes@) =~= a_doc(*self)); }
                MessageBuilder::new_v2(self.save(), hashes)
            } else {
                let all_hashes = self
                    .get_hashes_to_send(their_have, their_need)
                    .expect("Should have only used hashes that are in the document");
                proof { lemma_hts_subset(d, n, a_doc(*self), abs_haves(their_have@), vset(their_need@)); }
                // CHANGE [C13]: filter/collect replaced by `filter_unsent`.
                let hashes: Vec<_> = filter_unsent(all_hashes, &sync_state.sent_hashes);
                if hashes.len() > self.change_graph.len() / 3 && sync_state.supports_v2_messages() {
                    let all_hashes = self.change_graph.get_hashes(&Vec::new());
                    proof { lemma_reach_empty(d, n as nat); assert(vset(Seq::<u64>::empty()) =~= ISet::<int>::empty()); assert(vset(all_hashes@) =~= a_doc(*self)); }
                    MessageBuilder::new_v2(self.save(), all_hashes)
                } else {
                    // CHANGE [C20]: `.ok()?` -> match (the Err arm is excluded by T9).
                    let changes = match self.get_changes_by_hashes(&hashes) { Ok(c) => c, Err(_) => return None };
                    MessageBuilder::new(changes, sync_state)
                }
            }
        } else {
            MessageBuilder::new(Vec::new(), sync_state)
        };
        // Path by path: the builder holds send_set (ordinary branch) or the whole document (send_doc / one-third rule).
        let ghost send = mb_cset(message_builder);
        proof { lemma_reach_empty(d, n as nat); }
        assert((send == M::send_set(d, n, p) || send == a_doc(*self)) && vset(mb_hashes(message_builder)) == send);

        let heads_unchanged = vec_eq(&sync_state.last_sent_heads, &our_heads);
        proof {
            if heads_unchanged { assert(vset(s0.last_sent_heads@) == vset(our_heads@)); }
            else if vset(s0.last_sent_heads@) == vset(our_heads@) { lemma_sorted_eq(s0.last_sent_heads@, our_heads@); }
        }

        // CHANGE [C23]: `their_heads.as_ref() == Some(&our_heads)` -> match.
        let heads_equal = match &sync_state.their_heads { Some(h) => vec_eq(h, &our_heads), None => false };
        proof {
            if let Some(h) = s0.their_heads {
                if vset(h@) == vset(our_heads@) { lemma_sorted_eq(h@, our_heads@); }
                assert(heads_equal == (h@ == our_heads@));
                if h@ == our_heads@ { assert(vset(h@) == vset(our_heads@)); }
            }
            assert(heads_equal == (p.their_heads == Some(M::heads(d, a_doc(*self)))));
        }
        let ghost empty_b = (mb_hashes(message_builder).len() == 0);
        assert(empty_b == (send == ISet::<int>::empty())) by {
            if send == ISet::<int>::empty() {
                if mb_hashes(message_builder).len() > 0 { assert(vset(mb_hashes(message_builder)).contains(mb_hashes(message_builder)[0] as int)); }
            } else { if mb_hashes(message_builder).len() == 0 { assert(vset(mb_hashes(message_builder)) =~= ISet::<int>::empty()); } }
        }

        if heads_unchanged && sync_state.have_responded {
            if (heads_equal || sync_state.read_only) && message_builder.is_empty() {
                assert(M::gen_s(d, n, p, bloom, fake, send).1 is None);
                return None;
            }
            if sync_state.in_flight {
                assert(M::gen_s(d, n, p, bloom, fake, send).1 is None);
                return None;
            }
        }

        sync_state.have_responded = true;
        // CHANGE [C21]: `clone_from(&x)` -> `= x.clone()`.
        sync_state.last_sent_heads = our_heads.clone();
        extend_hashes(&mut sync_state.sent_hashes, message_builder.hashes());

        let mut flags = MessageFlags::new();
        flags.set(MessageFlags::SUPPORTS_SYNC_RESET);
        assert((0u8 | 4u8) == 4u8) by (bit_vector);
        if sync_state.read_only {
            flags.set(MessageFlags::READ_ONLY);
        }
        assert(flags.0 == 4u8);

        let heads_to_send = if sync_state.needs_reset {
            sync_state.needs_reset = false;
            if sync_state.peer_supports_sync_reset() {
                flags.set(MessageFlags::SYNC_RESET);
                our_heads.clone()
            } else {
                Vec::new()
            }
        } else {
            our_heads.clone()
        };
        assert((4u8 & 1u8) == 0u8 && (4u8 & 2u8) == 0u8) by (bit_vector);
        assert((!s0.needs_reset || !st_sr(s0)) ==> flags.0 == 4u8);
        assert(sorted_strict(heads_to_send@)) by { assert(sorted_strict(our_heads@)); assert(heads_to_send@.len() == 0 || heads_to_send@ == our_heads@); }

        let sync_message = message_builder
            .heads(heads_to_send)
            .have(our_have)
            .need(our_need)
            .flags(Some(flags))
            .build();

        sync_state.in_flight = true;
        assert(opt_set_eq(s0.their_heads));
        assert(vset(Seq::<u64>::empty()) =~= ISet::<int>::empty());
        assert(abs_peer(*self, *sync_state) =~= M::gen_s(d, n, p, bloom, fake, send).0);
        assert(abs_msg(sync_message) =~= M::gen_s(d, n, p, bloom, fake, send).1->Some_0);
        assert(sorted_strict(sync_message.heads@));
        assert((!s0.needs_reset || !st_sr(s0)) ==> out_wf(Some(sync_message)));
        Some(sync_message)
    }

}


// =====================================================================================
// receive_sync_message (copied)
// =====================================================================================
impl Automerge {
    pub fn receive_sync_message(
        &mut self,
        sync_state: &mut State,
        message: Message,
    ) -> (r: Result<(), AutomergeError>)
        requires a_wf(*old(self)), st_wf(*old(sync_state), *old(self)), msg_wf(message, *old(self)), !old(sync_state).read_only,
        ensures recv_post(*old(self), *old(sync_state), message, *final(self), *final(sync_state), r),
    {
        let mut patch_log = PatchLog::inactive();
        self.receive_sync_message_inner(sync_state, message, &mut patch_log)
    }

    pub(crate) fn receive_sync_message_inner(
        &mut self,
        sync_state: &mut State,
        message: Message,
        patch_log: &mut PatchLog,
    ) -> (r: Result<(), AutomergeError>)
        requires a_wf(*old(self)), st_wf(*old(sync_state), *old(self)), msg_wf(message, *old(self)), !old(sync_state).read_only,
        ensures recv_post(*old(self), *old(sync_state), message, *final(self), *final(sync_state), r),
    {
        let ghost a0 = *self;
        let ghost s0 = *sync_state;
        let ghost msg0 = message;
        let ghost d = a_deps(a0);
        let ghost n = a_n(a0);
        sync_state.in_flight = false;
        let before_heads = self.get_heads();

        let Message {
            heads: message_heads,
            changes: message_changes,
            need: message_need,
            have: message_have,
            flags: message_flags,
            ..
        } = message;

        if let Some(flags) = message_flags {
            let mut caps = vec![Capability::MessageV2];
            if flags.contains(MessageFlags::SUPPORTS_SYNC_RESET) {
                caps.push(Capability::SyncReset);
            }
            sync_state.their_capabilities = Some(caps);

            if flags.contains(MessageFlags::SYNC_RESET) {
                sync_state.sent_hashes.clear();
            }
            sync_state.peer_read_only = flags.contains(MessageFlags::READ_ONLY);
        }
        proof { assert(abs_state(*sync_state) == M::Peer { in_flight: false, ..abs_state(s0) }); }

        let changes_is_empty = message_changes.is_empty();
        if !changes_is_empty && !sync_state.read_only {
            // CHANGE [C26]: `?` -> match.
            match self.load_incremental_log_patches(&message_changes.join(), patch_log) {
                Ok(_) => {}
                Err(e) => return Err(e),
            }
            // CHANGE [C8]: advance_heads takes Vecs.
            sync_state.shared_heads = advance_heads(
                &before_heads,
                &self.get_heads(),
                &sync_state.shared_heads,
            );
        }
        let ghost sent_before = sync_state.sent_hashes;
        let ghost sh_mid = sync_state.shared_heads;

        // CHANGE [C26]: `?` -> match; `&message_heads` -> `message_heads.as_slice()`.
        match self.filter_changes(message_heads.as_slice(), &mut sync_state.sent_hashes) {
            Ok(_) => {}
            Err(e) => return Err(e),
        }

        // CHANGE [C25]: `==` on Vec -> vec_eq. CHANGE [C21]: clone_from -> `= x.clone()`.
        if changes_is_empty && vec_eq(&message_heads, &before_heads) {
            sync_state.last_sent_heads = message_heads.clone();
        }

        // CHANGE [C12]: filter/collect replaced by `known_heads` (verified helper).
        let known_heads = self.known_heads(&message_heads);
        if known_heads.len() == message_heads.len() {
            sync_state.shared_heads = message_heads.clone();
            // If the remote peer has lost all its data, reset our state to perform a full resync
            if message_heads.is_empty() {
                // CHANGE [C27]: Default::default() -> Vec::new() / BTreeSet::new()
                sync_state.last_sent_heads = Vec::new();
                sync_state.sent_hashes = BTreeSet::new();
            }
        } else {
            // CHANGE [C9]: itertools chain/unique/sorted -> union_sorted (trusted T13).
            sync_state.shared_heads = union_sorted(&sync_state.shared_heads, &known_heads);
        }

        sync_state.their_have = Some(message_have);
        sync_state.their_heads = Some(message_heads);
        sync_state.their_need = Some(message_need);

        proof {
            let p = abs_peer(a0, s0);
            let m = abs_msg(msg0);
            let s2 = a_doc(*self);
            assert(changes_is_empty == (m.changes == ISet::<int>::empty()));
            assert(vset(before_heads@) == M::heads(d, p.doc));
            // the heads vectors are strictly sorted, so Vec equality is set equality
            if vset(msg0.heads@) == vset(before_heads@) { lemma_sorted_eq(msg0.heads@, before_heads@); }
            assert(vset(Seq::<u64>::empty()) =~= ISet::<int>::empty());
            let q = M::recv(d, n, p, m, s2); let o = abs_peer(*self, *sync_state);
            let known = m.heads.intersect(s2);
            assert(known == vset(known_heads@));
            let all_known = (known_heads@.len() == msg0.heads@.len());
            assert(all_known == (known == m.heads)) by {
                if known == m.heads { assert(m.heads.subset_of(s2)) by { assert forall|x: int| m.heads.contains(x) implies s2.contains(x) by { assert(known.contains(x)); } } }
                if m.heads.subset_of(s2) { assert(known =~= m.heads); }
            }
            assert((msg0.heads@.len() == 0) == (m.heads == ISet::<int>::empty())) by {
                if msg0.heads@.len() > 0 { assert(m.heads.contains(msg0.heads@[0] as int)); }
                if m.heads == ISet::<int>::empty() && msg0.heads@.len() > 0 { assert(false); }
                if msg0.heads@.len() == 0 { assert(m.heads =~= ISet::<int>::empty()); }
            }
            if all_known { assert(o.shared_heads == q.shared_heads); }
            else { assert(o.shared_heads == q.shared_heads); }
            assert(o.doc == q.doc);
            assert(o.queue == q.queue);
            assert(o.their_heads == q.their_heads);
            assert(o.their_have =~= q.their_have);
            assert(o.their_need == q.their_need);
            assert(o.in_flight == q.in_flight);
            assert(o.have_responded == q.have_responded);
            assert(o.needs_reset == q.needs_reset);
            assert(o.sent_hashes == q.sent_hashes);
            assert(o.last_sent_heads == q.last_sent_heads);
            assert(o.shared_heads == q.shared_heads);
            assert(o =~= q);
        }
        Ok(())
    }
}


// =====================================================================================
// Part D: composition. A run of the real code (two Automerge documents, two sync States, a ghost network of
// abstract messages) is a run of the model, so the model's theorems apply to it.
// What is assumed (not proved): `step_edit` (a local edit conforms to the model's Edit step: no code for it here),
// that every delivered message satisfies msg_wf, that receive returns Ok, and that read-only mode is off.
// =====================================================================================
pub struct Cfg { pub a: Seq<Automerge>, pub s: Seq<State>, pub net: Seq<ISet<M::Msg>> }

pub open spec fn abs_cfg(c: Cfg) -> M::World {
    M::World { peers: Seq::new(2, |i: int| abs_peer(c.a[i], c.s[i])), net: c.net }
}
pub open spec fn cfg_peer_ok(c: Cfg, i: int) -> bool {
    a_wf(c.a[i]) && st_wf(c.s[i], c.a[i]) && !c.s[i].read_only && !c.s[i].peer_read_only && !c.s[i].needs_reset
    && a_deps(c.a[i]) == a_deps(c.a[0]) && a_n(c.a[i]) == a_n(c.a[0])
}
pub open spec fn cfg_wf(c: Cfg) -> bool {
    c.a.len() == 2 && c.s.len() == 2 && c.net.len() == 2 && cfg_peer_ok(c, 0) && cfg_peer_ok(c, 1)
}
pub open spec fn cfg_d(c: Cfg) -> M::Deps { a_deps(c.a[0]) }
pub open spec fn cfg_n(c: Cfg) -> int { a_n(c.a[0]) }

pub open spec fn gen_rel(c: Cfg, c2: Cfg, who: int, s1: State, r: Option<Message>) -> bool {
    gen_post(c.a[who], c.s[who], s1, r)
    && c2.a == c.a && c2.s == c.s.update(who, s1)
    && c2.net == (match r { Some(m) => c.net.update(who, c.net[who].insert(abs_msg(m))), None => c.net })
}
pub open spec fn step_gen(c: Cfg, c2: Cfg, who: int) -> bool { exists|s1: State, r: Option<Message>| gen_rel(c, c2, who, s1, r) }
pub open spec fn recv_core(c: Cfg, c2: Cfg, who: int, keep: bool, msg: Message, a1: Automerge, s1: State) -> bool {
    c.net[1 - who].contains(abs_msg(msg))
    && recv_post(c.a[who], c.s[who], msg, a1, s1, Result::<(), AutomergeError>::Ok(()))
    && c2.a == c.a.update(who, a1) && c2.s == c.s.update(who, s1)
    && c2.net == (if keep { c.net } else { c.net.update(1 - who, c.net[1 - who].remove(abs_msg(msg))) })
}
// `msg_wf` is the precondition of receive_sync_message; here it is a hypothesis of the step (proved for generated
// messages in lemma_gen_model, used by Part E).
pub open spec fn recv_rel(c: Cfg, c2: Cfg, who: int, keep: bool, msg: Message, a1: Automerge, s1: State) -> bool {
    msg_wf(msg, c.a[who]) && recv_core(c, c2, who, keep, msg, a1, s1)
}
pub open spec fn step_recv(c: Cfg, c2: Cfg, who: int, keep: bool) -> bool {
    exists|msg: Message, a1: Automerge, s1: State| recv_rel(c, c2, who, keep, msg, a1, s1)
}
pub open spec fn tmo_rel(c: Cfg, c2: Cfg, who: int, s1: State) -> bool {
    abs_state(s1) == M::tmo(abs_state(c.s[who]))
    && s1.read_only == c.s[who].read_only && s1.peer_read_only == c.s[who].peer_read_only
    && (forall|a: Automerge| st_wf(s1, a) == st_wf(c.s[who], a))
    && c2.a == c.a && c2.s == c.s.update(who, s1) && c2.net == c.net
}
pub open spec fn step_tmo(c: Cfg, c2: Cfg, who: int) -> bool { exists|s1: State| tmo_rel(c, c2, who, s1) }
pub open spec fn drop_rel(c: Cfg, c2: Cfg, who: int, m: M::Msg) -> bool {
    c.net[who].contains(m) && c2.a == c.a && c2.s == c.s && c2.net == c.net.update(who, c.net[who].remove(m))
}
pub open spec fn step_drop(c: Cfg, c2: Cfg, who: int) -> bool { exists|m: M::Msg| drop_rel(c, c2, who, m) }
// TRUSTED: a local edit adds one change `ch` to the document, as the model's Edit step does (no code is verified here).
pub open spec fn edit_rel(c: Cfg, c2: Cfg, who: int, a1: Automerge, ch: int) -> bool {
    M::guard(cfg_d(c), cfg_n(c), abs_cfg(c), M::Step::Edit { who, c: ch })
    && a_wf(a1) && a_deps(a1) == a_deps(c.a[who]) && a_n(a1) == a_n(c.a[who])
    && a_doc(a1) == a_doc(c.a[who]).insert(ch) && a_queue(a1) == a_queue(c.a[who])
    && c2.a == c.a.update(who, a1) && c2.s == c.s && c2.net == c.net
}
pub open spec fn step_edit(c: Cfg, c2: Cfg, who: int) -> bool { exists|a1: Automerge, ch: int| edit_rel(c, c2, who, a1, ch) }
pub open spec fn step_any(c: Cfg, c2: Cfg, who: int, keep: bool) -> bool {
    (who == 0 || who == 1) && (step_gen(c, c2, who) || step_recv(c, c2, who, keep) || step_tmo(c, c2, who)
        || step_drop(c, c2, who) || step_edit(c, c2, who))
}
pub open spec fn code_next(c: Cfg, c2: Cfg) -> bool { exists|who: int, keep: bool| step_any(c, c2, who, keep) }

// A code step is a model step (and keeps the code configuration well-formed).
pub proof fn lemma_code_step(c: Cfg, c2: Cfg)
    requires cfg_wf(c), code_next(c, c2),
    ensures cfg_wf(c2), exists|st: M::Step| M::next(cfg_d(c), cfg_n(c), abs_cfg(c), st, abs_cfg(c2)),
{
    let d = cfg_d(c); let n = cfg_n(c);
    let (who, keep0) = choose|who: int, keep: bool| step_any(c, c2, who, keep);
    let w = abs_cfg(c); let w2 = abs_cfg(c2);
    assert(w.peers.len() == 2);
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    if step_gen(c, c2, who) {
        let (s1, r) = choose|s1: State, r: Option<Message>| gen_rel(c, c2, who, s1, r);
        let a = c.a[who]; let p = abs_peer(a, c.s[who]);
        assert(a_deps(a) == d && a_n(a) == n);
        let (bloom, send) = choose|bloom: ISet<int>, send: ISet<int>| {
            &&& a_doc(a).difference(M::closure(a_deps(a), a_n(a), vset(c.s[who].shared_heads@))).subset_of(bloom)
            &&& (send == M::send_set(a_deps(a), a_n(a), p) || send == a_doc(a))
            &&& abs_peer(a, s1) == (#[trigger] M::gen_s(a_deps(a), a_n(a), p, bloom, fake_of(c.s[who]), send)).0
            &&& gen_msg_ok(p, r, M::gen_s(a_deps(a), a_n(a), p, bloom, fake_of(c.s[who]), send).1) };
        let fake = fake_of(c.s[who]);
        let st = if send == M::send_set(d, n, p) { M::Step::Gen { who, bloom, fake } } else { M::Step::GenDoc { who, bloom, fake } };
        assert(M::next(d, n, w, st, w2)) by {
            assert(p == w.peers[who]);
            if send == M::send_set(d, n, p) { assert(M::gen_s(d, n, p, bloom, fake, send) == M::gen(d, n, p, bloom, fake)); }
            let g = M::gen_s(d, n, p, bloom, fake, send);
            assert(w2.peers =~= w.peers.update(who, g.0));
            match r { Some(m) => { assert(g.1 == Some(abs_msg(m))); }, None => { assert(g.1 is None); } }
        }
        assert(cfg_wf(c2)) by { assert(c2.s.len() == 2 && c2.net.len() == 2); assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who)); }
    } else if step_recv(c, c2, who, keep0) {
        let keep = keep0;
        let (msg, a1, s1) = choose|msg: Message, a1: Automerge, s1: State| recv_rel(c, c2, who, keep, msg, a1, s1);
        let p = abs_peer(c.a[who], c.s[who]); let m = abs_msg(msg); let s2 = a_doc(a1);
        let st = M::Step::Recv { who, m, s2, keep };
        assert(M::next(d, n, w, st, w2)) by {
            assert(a_deps(c.a[who]) == d && a_n(c.a[who]) == n);
            assert(w2.peers =~= w.peers.update(who, M::recv(d, n, p, m, s2)));
        }
        assert(cfg_wf(c2)) by {
            assert(a_deps(a1) == d && a_n(a1) == n);
            assert(c2.s.len() == 2 && c2.a.len() == 2 && c2.net.len() == 2);
            assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
        }
    } else if step_tmo(c, c2, who) {
        let s1 = choose|s1: State| tmo_rel(c, c2, who, s1);
        let st = M::Step::Timeout { who };
        assert(M::next(d, n, w, st, w2)) by {
            assert(abs_peer(c.a[who], s1) == M::tmo(abs_peer(c.a[who], c.s[who])));
            assert(w2.peers =~= w.peers.update(who, M::tmo(w.peers[who])));
        }
        assert(cfg_wf(c2)) by { assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who)); }
    } else if step_drop(c, c2, who) {
        let m = choose|m: M::Msg| drop_rel(c, c2, who, m);
        let st = M::Step::Drop { who, m };
        assert(M::next(d, n, w, st, w2)) by { assert(w2.peers =~= w.peers); }
        assert(cfg_wf(c2));
    } else {
        let (a1, ch) = choose|a1: Automerge, ch: int| edit_rel(c, c2, who, a1, ch);
        let st = M::Step::Edit { who, c: ch };
        assert(M::next(d, n, w, st, w2)) by {
            let p = w.peers[who];
            assert(w2.peers =~= w.peers.update(who, M::Peer { doc: p.doc.insert(ch), ..p }));
        }
        assert(cfg_wf(c2)) by {
            assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
            assert(vset(c.s[who].shared_heads@).subset_of(a_doc(a1)));
        }
    }
}

// A run: cs(0), cs(1), ..., cs(k), each step a code step.
pub open spec fn code_run(cs: spec_fn(nat) -> Cfg, k: nat) -> bool {
    cfg_wf(cs(0)) && forall|i: nat| i < k ==> #[trigger] code_next(cs(i), cs(i + 1))
}
// The start of a session: nothing in flight and nothing known about the peer (so the model's `inv` holds by a_wf).
pub open spec fn session_start(c: Cfg) -> bool {
    cfg_wf(c) && c.net[0] == ISet::<M::Msg>::empty() && c.net[1] == ISet::<M::Msg>::empty()
    && c.s[0].their_heads is None && c.s[1].their_heads is None
}
pub proof fn lemma_session_inv(c: Cfg)
    requires session_start(c), ensures M::inv(cfg_d(c), cfg_n(c), abs_cfg(c)),
{
    let d = cfg_d(c); let n = cfg_n(c); let w = abs_cfg(c);
    assert(w.peers.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies M::peer_inv(d, n, w, i) by {
        assert(cfg_peer_ok(c, i));
        assert(a_deps(c.a[i]) == d);
        assert(w.peers[i].their_heads is None);
    }
}
// by induction: every configuration of a run satisfies cfg_wf and the model's safety invariant
pub proof fn lemma_run_inv(cs: spec_fn(nat) -> Cfg, k: nat)
    requires code_run(cs, k), session_start(cs(0)),
    ensures cfg_wf(cs(k)), M::inv(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k))), cfg_d(cs(k)) == cfg_d(cs(0)), cfg_n(cs(k)) == cfg_n(cs(0)),
    decreases k,
{
    if k == 0 { lemma_session_inv(cs(0)); } else {
        lemma_run_inv(cs, (k - 1) as nat);
        let c = cs((k - 1) as nat); let c2 = cs(k);
        let i = (k - 1) as nat;
        assert(code_next(cs(i), cs(i + 1)));
        assert(i + 1 == k);
        lemma_code_step(c, c2);
        let st = choose|st: M::Step| M::next(cfg_d(c), cfg_n(c), abs_cfg(c), st, abs_cfg(c2));
        assert(M::wf(cfg_d(c), cfg_n(c)));
        M::lemma_step(cfg_d(c), cfg_n(c), abs_cfg(c), st, abs_cfg(c2));
        assert(cfg_d(c2) == cfg_d(c) && cfg_n(c2) == cfg_n(c)) by {
            assert(a_deps(c2.a[0]) == a_deps(c2.a[0]));
        }
    }
}
// SAFETY OF THE CODE: in any run of the code from a session start, if at the end both peers are in the state in which
// generate_sync_message answers None through its heads_equal branch (model: report_in_sync), the documents are equal.
pub proof fn theorem_code_safety(cs: spec_fn(nat) -> Cfg, k: nat)
    requires code_run(cs, k), session_start(cs(0)),
        M::report_in_sync(cfg_d(cs(k)), cfg_n(cs(k)), abs_peer(cs(k).a[0], cs(k).s[0])),
        M::report_in_sync(cfg_d(cs(k)), cfg_n(cs(k)), abs_peer(cs(k).a[1], cs(k).s[1])),
    ensures a_doc(cs(k).a[0]) == a_doc(cs(k).a[1]),
{
    lemma_run_inv(cs, k);
    let c = cs(k);
    assert(M::wf(cfg_d(c), cfg_n(c)));
    M::theorem_safety_inv(cfg_d(c), cfg_n(c), abs_cfg(c));
}

// =====================================================================================
// Part E (vlm47_amcode#3): LIVENESS OF THE CODE.  A code run is a sequence of code ROUNDS; a round is the model's
// lock-step round (Timeout A, Timeout B, generate A, generate B, deliver or drop A's message, deliver or drop
// B's message) made of calls to the copied functions.  Each generate call may be the ordinary Gen or the
// whole-document GenDoc (gen_post allows both), chosen by the code, not by us.  Every message that is delivered is
// the message the other peer generated, and `msg_wf` of it is PROVED (lemma_gen_model), not assumed.
// =====================================================================================
pub struct CRound { pub c1: Cfg, pub c2: Cfg, pub c3: Cfg, pub c4: Cfg, pub c5: Cfg,
    pub ra: Option<Message>, pub rb: Option<Message>, pub lossa: bool, pub lossb: bool }

// generate_sync_message returned `r` (its ensures include out_wf(r), as needs_reset is false: cfg_peer_ok)
pub open spec fn gen_rel_r(c: Cfg, c2: Cfg, who: int, r: Option<Message>) -> bool {
    (exists|s1: State| gen_rel(c, c2, who, s1, r)) && out_wf(r)
}
// the message `r` generated by peer `from` is dropped (loss) or received (not kept) by the other peer
pub open spec fn deliver(c: Cfg, c2: Cfg, from: int, r: Option<Message>, loss: bool) -> bool {
    match r {
        None => c2 == c && !loss,
        Some(m) => if loss { drop_rel(c, c2, from, abs_msg(m)) }
                   else { exists|a1: Automerge, s1: State| #[trigger] recv_core(c, c2, 1 - from, false, m, a1, s1) },
    }
}
pub open spec fn cround_ok(c0: Cfg, c6: Cfg, cr: CRound) -> bool {
    step_tmo(c0, cr.c1, 0) && step_tmo(cr.c1, cr.c2, 1)
    && gen_rel_r(cr.c2, cr.c3, 0, cr.ra) && gen_rel_r(cr.c3, cr.c4, 1, cr.rb)
    && deliver(cr.c4, cr.c5, 0, cr.ra, cr.lossa) && deliver(cr.c5, c6, 1, cr.rb, cr.lossb)
}
pub open spec fn cr_good(cr: CRound) -> bool { !cr.lossa && !cr.lossb }

pub proof fn lemma_tmo_model(c: Cfg, c2: Cfg, who: int)
    requires cfg_wf(c), who == 0 || who == 1, step_tmo(c, c2, who),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
        M::next(cfg_d(c), cfg_n(c), abs_cfg(c), M::Step::Timeout { who }, abs_cfg(c2)),
{
    let d = cfg_d(c); let n = cfg_n(c); let w = abs_cfg(c); let w2 = abs_cfg(c2);
    let s1 = choose|s1: State| tmo_rel(c, c2, who, s1);
    assert(w.peers.len() == 2);
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    assert(abs_peer(c.a[who], s1) == M::tmo(abs_peer(c.a[who], c.s[who])));
    assert(w2.peers =~= w.peers.update(who, M::tmo(w.peers[who])));
    assert(M::next(d, n, w, M::Step::Timeout { who }, w2));
    assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
}

pub proof fn lemma_gen_model(c: Cfg, c2: Cfg, who: int, r: Option<Message>)
    requires cfg_wf(c), who == 0 || who == 1, gen_rel_r(c, c2, who, r),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
        exists|bloom: ISet<int>, isdoc: bool| {
            &&& M::next(cfg_d(c), cfg_n(c), abs_cfg(c), #[trigger] M::gstep(who, bloom, fake_of(c.s[who]), isdoc), abs_cfg(c2))
            &&& (match r {
                Some(m) => M::gen_x(cfg_d(c), cfg_n(c), abs_peer(c.a[who], c.s[who]), bloom, fake_of(c.s[who]), isdoc).1 == Some(abs_msg(m)),
                None => M::gen_x(cfg_d(c), cfg_n(c), abs_peer(c.a[who], c.s[who]), bloom, fake_of(c.s[who]), isdoc).1 is None,
            })
        },
        // PROVED (not assumed): a generated message is acceptable to receive_sync_message of the other peer
        (match r { Some(m) => forall|a: Automerge| a_n(a) == cfg_n(c) ==> msg_wf(m, a), None => true }),
{
    let d = cfg_d(c); let n = cfg_n(c);
    let s1 = choose|s1: State| gen_rel(c, c2, who, s1, r);
    let w = abs_cfg(c); let w2 = abs_cfg(c2);
    assert(w.peers.len() == 2);
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    let a = c.a[who]; let p = abs_peer(a, c.s[who]);
    assert(a_deps(a) == d && a_n(a) == n);
    assert(a_wf(a));
    let (bloom, send) = choose|bloom: ISet<int>, send: ISet<int>| {
        &&& a_doc(a).difference(M::closure(a_deps(a), a_n(a), vset(c.s[who].shared_heads@))).subset_of(bloom)
        &&& (send == M::send_set(a_deps(a), a_n(a), p) || send == a_doc(a))
        &&& abs_peer(a, s1) == (#[trigger] M::gen_s(a_deps(a), a_n(a), p, bloom, fake_of(c.s[who]), send)).0
        &&& gen_msg_ok(p, r, M::gen_s(a_deps(a), a_n(a), p, bloom, fake_of(c.s[who]), send).1) };
    let fake = fake_of(c.s[who]);
    let isdoc = !(send == M::send_set(d, n, p));
    assert(M::gen_x(d, n, p, bloom, fake, isdoc) == M::gen_s(d, n, p, bloom, fake, send)) by {
        if isdoc { assert(send == a_doc(a)); }
    }
    let g = M::gen_s(d, n, p, bloom, fake, send);
    assert(M::next(d, n, w, M::gstep(who, bloom, fake, isdoc), w2)) by {
        assert(p == w.peers[who]);
        assert(w2.peers =~= w.peers.update(who, g.0));
        match r { Some(m) => { assert(g.1 == Some(abs_msg(m))); }, None => { assert(g.1 is None); } }
    }
    assert(cfg_wf(c2)) by { assert(c2.s.len() == 2 && c2.net.len() == 2); assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who)); }
    match r {
        Some(m) => {
            M::lemma_gens_props(d, n, p, bloom, fake, send);
            assert(send.subset_of(a_doc(a)) || true);
            assert(g.1 == Some(abs_msg(m)));
            assert forall|a2: Automerge| a_n(a2) == n implies msg_wf(m, a2) by {
                assert(M::bounded(chunk_set(m.changes), a_n(a2)));
                assert(m.have@.len() <= 1);
            }
        }
        None => {}
    }
}

pub proof fn lemma_recv_model(c: Cfg, c2: Cfg, who: int, msg: Message, a1: Automerge, s1: State)
    requires cfg_wf(c), who == 0 || who == 1, recv_core(c, c2, who, false, msg, a1, s1),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
        M::next(cfg_d(c), cfg_n(c), abs_cfg(c), M::Step::Recv { who, m: abs_msg(msg), s2: a_doc(a1), keep: false }, abs_cfg(c2)),
{
    let d = cfg_d(c); let n = cfg_n(c); let w = abs_cfg(c); let w2 = abs_cfg(c2);
    assert(w.peers.len() == 2);
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    let p = abs_peer(c.a[who], c.s[who]); let m = abs_msg(msg); let s2 = a_doc(a1);
    assert(a_deps(c.a[who]) == d && a_n(c.a[who]) == n);
    assert(w2.peers =~= w.peers.update(who, M::recv(d, n, p, m, s2)));
    assert(M::next(d, n, w, M::Step::Recv { who, m, s2, keep: false }, w2));
    assert(a_deps(a1) == d && a_n(a1) == n);
    assert(c2.s.len() == 2 && c2.a.len() == 2 && c2.net.len() == 2);
    assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
}

pub proof fn lemma_drop_model(c: Cfg, c2: Cfg, who: int, m: M::Msg)
    requires cfg_wf(c), who == 0 || who == 1, drop_rel(c, c2, who, m),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
        M::next(cfg_d(c), cfg_n(c), abs_cfg(c), M::Step::Drop { who, m }, abs_cfg(c2)),
{
    let w = abs_cfg(c); let w2 = abs_cfg(c2);
    assert(w.peers.len() == 2);
    assert(w2.peers =~= w.peers);
    assert(w2 == M::apply(cfg_d(c), cfg_n(c), w, M::Step::Drop { who, m })) by { assert(w2.net =~= c.net.update(who, c.net[who].remove(m))); }
}

pub open spec fn s2_of(c: Cfg, c2: Cfg, who: int, m: Message) -> ISet<int> {
    a_doc((choose|a1s: (Automerge, State)| recv_core(c, c2, who, false, m, a1s.0, a1s.1)).0)
}
pub open spec fn rp_of_round(cr: CRound, c6: Cfg, ba: ISet<int>, fa: bool, da: bool, bb: ISet<int>, fb: bool, db: bool) -> M::RP {
    M::RP { ba, fa, da, bb, fb, db,
        s2a: match cr.rb { Some(m) => if cr.lossb { ISet::empty() } else { s2_of(cr.c5, c6, 0, m) }, None => ISet::empty() },
        s2b: match cr.ra { Some(m) => if cr.lossa { ISet::empty() } else { s2_of(cr.c4, cr.c5, 1, m) }, None => ISet::empty() },
        lossa: cr.lossa, lossb: cr.lossb }
}

// A code round is a model round (for some choice of Bloom filters, send modes and drain results).
pub proof fn lemma_round_code(c0: Cfg, c6: Cfg, cr: CRound)
    requires cfg_wf(c0), cround_ok(c0, c6, cr),
    ensures cfg_wf(c6), cfg_d(c6) == cfg_d(c0), cfg_n(c6) == cfg_n(c0),
        exists|rp: M::RP| M::rvalid(cfg_d(c0), cfg_n(c0), abs_cfg(c0), rp)
            && abs_cfg(c6) == M::rw6(cfg_d(c0), cfg_n(c0), abs_cfg(c0), rp) && (M::good(rp) <==> cr_good(cr)),
{
    let d = cfg_d(c0); let n = cfg_n(c0); let w0 = abs_cfg(c0);
    lemma_tmo_model(c0, cr.c1, 0);
    lemma_tmo_model(cr.c1, cr.c2, 1);
    lemma_gen_model(cr.c2, cr.c3, 0, cr.ra);
    lemma_gen_model(cr.c3, cr.c4, 1, cr.rb);
    let (ba, da) = choose|bloom: ISet<int>, isdoc: bool| {
        &&& M::next(cfg_d(cr.c2), cfg_n(cr.c2), abs_cfg(cr.c2), #[trigger] M::gstep(0, bloom, fake_of(cr.c2.s[0]), isdoc), abs_cfg(cr.c3))
        &&& (match cr.ra {
            Some(m) => M::gen_x(cfg_d(cr.c2), cfg_n(cr.c2), abs_peer(cr.c2.a[0], cr.c2.s[0]), bloom, fake_of(cr.c2.s[0]), isdoc).1 == Some(abs_msg(m)),
            None => M::gen_x(cfg_d(cr.c2), cfg_n(cr.c2), abs_peer(cr.c2.a[0], cr.c2.s[0]), bloom, fake_of(cr.c2.s[0]), isdoc).1 is None }) };
    let (bb, db) = choose|bloom: ISet<int>, isdoc: bool| {
        &&& M::next(cfg_d(cr.c3), cfg_n(cr.c3), abs_cfg(cr.c3), #[trigger] M::gstep(1, bloom, fake_of(cr.c3.s[1]), isdoc), abs_cfg(cr.c4))
        &&& (match cr.rb {
            Some(m) => M::gen_x(cfg_d(cr.c3), cfg_n(cr.c3), abs_peer(cr.c3.a[1], cr.c3.s[1]), bloom, fake_of(cr.c3.s[1]), isdoc).1 == Some(abs_msg(m)),
            None => M::gen_x(cfg_d(cr.c3), cfg_n(cr.c3), abs_peer(cr.c3.a[1], cr.c3.s[1]), bloom, fake_of(cr.c3.s[1]), isdoc).1 is None }) };
    let fa = fake_of(cr.c2.s[0]); let fb = fake_of(cr.c3.s[1]);
    let rp = rp_of_round(cr, c6, ba, fa, da, bb, fb, db);
    assert(cfg_d(cr.c1) == d && cfg_d(cr.c2) == d && cfg_d(cr.c3) == d && cfg_d(cr.c4) == d);
    assert(cfg_n(cr.c1) == n && cfg_n(cr.c2) == n && cfg_n(cr.c3) == n && cfg_n(cr.c4) == n);
    assert(abs_cfg(cr.c1) == M::rw1(d, n, w0));
    assert(abs_cfg(cr.c2) == M::rw2(d, n, w0));
    assert(abs_cfg(cr.c3) == M::rw3(d, n, w0, rp));
    assert(abs_cfg(cr.c4) == M::rw4(d, n, w0, rp));
    assert(abs_cfg(cr.c2).peers[0] == abs_peer(cr.c2.a[0], cr.c2.s[0]));
    assert(abs_cfg(cr.c3).peers[1] == abs_peer(cr.c3.a[1], cr.c3.s[1]));
    assert(M::msg_a(d, n, w0, rp) == M::gen_x(d, n, abs_cfg(cr.c2).peers[0], ba, fa, da).1);
    assert(M::msg_b(d, n, w0, rp) == M::gen_x(d, n, abs_cfg(cr.c3).peers[1], bb, fb, db).1);
    assert(cfg_wf(cr.c5) && cfg_d(cr.c5) == d && cfg_n(cr.c5) == n && abs_cfg(cr.c5) == M::rw5(d, n, w0, rp)
        && (match M::msg_a(d, n, w0, rp) { Some(m) => M::guard(d, n, abs_cfg(cr.c4), M::st5(rp, m)), None => true })) by {
        match cr.ra {
            Some(m) => {
                if cr.lossa { lemma_drop_model(cr.c4, cr.c5, 0, abs_msg(m)); }
                else {
                    let (a1, s1) = choose|a1: Automerge, s1: State| recv_core(cr.c4, cr.c5, 1, false, m, a1, s1);
                    lemma_recv_model(cr.c4, cr.c5, 1, m, a1, s1);
                    assert(rp.s2b == a_doc(a1));
                }
            }
            None => { assert(cr.c5 == cr.c4); }
        }
    }
    assert(cfg_wf(c6) && cfg_d(c6) == d && cfg_n(c6) == n && abs_cfg(c6) == M::rw6(d, n, w0, rp)
        && (match M::msg_b(d, n, w0, rp) { Some(m) => M::guard(d, n, abs_cfg(cr.c5), M::st6(rp, m)), None => true })) by {
        match cr.rb {
            Some(m) => {
                if cr.lossb { lemma_drop_model(cr.c5, c6, 1, abs_msg(m)); }
                else {
                    let (a1, s1) = choose|a1: Automerge, s1: State| recv_core(cr.c5, c6, 0, false, m, a1, s1);
                    lemma_recv_model(cr.c5, c6, 0, m, a1, s1);
                    assert(rp.s2a == a_doc(a1));
                }
            }
            None => { assert(c6 == cr.c5); }
        }
    }
    assert(M::rvalid(d, n, w0, rp)) by {
        assert(M::guard(d, n, w0, M::Step::Timeout { who: 0 }));
        assert(M::guard(d, n, M::rw1(d, n, w0), M::Step::Timeout { who: 1 }));
        assert(M::guard(d, n, M::rw2(d, n, w0), M::gstep(0, ba, fa, da)));
        assert(M::guard(d, n, M::rw3(d, n, w0, rp), M::gstep(1, bb, fb, db)));
    }
    assert(M::good(rp) == cr_good(cr));
}

// ---- the run, its fairness, and the theorem
pub open spec fn code_rounds(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound) -> bool {
    forall|k: nat| #![trigger crs(k)] cround_ok(cs(k), cs((k + 1) as nat), crs(k))
}
// same fairness as the model's `fair_lossy`: infinitely often, 4 consecutive rounds lose nothing
pub open spec fn code_win4(crs: spec_fn(nat) -> CRound, m: nat) -> bool {
    exists|k: nat| #![trigger crs(k)] k >= m && cr_good(crs(k)) && cr_good(crs((k + 1) as nat))
        && cr_good(crs((k + 2) as nat)) && cr_good(crs((k + 3) as nat))
}
pub open spec fn code_fair(crs: spec_fn(nat) -> CRound) -> bool { forall|m: nat| #[trigger] code_win4(crs, m) }

// Start of a live session: as session_start, plus what the model's extra invariant `xinv` needs. A fresh State
// (State::new) has these; a document may hold a queue only of changes the other peer has.
pub open spec fn live_start(c: Cfg) -> bool {
    session_start(c)
    && (forall|i: int| 0 <= i < 2 ==> #[trigger] c.s[i].shared_heads@.len() == 0 && c.s[i].their_have is None
        && a_queue(c.a[i]).subset_of(a_doc(c.a[1 - i])))
}
pub proof fn lemma_live_start_sinv(c: Cfg)
    requires live_start(c), ensures M::sinv(cfg_d(c), cfg_n(c), abs_cfg(c)),
{
    lemma_session_inv(c);
    let d = cfg_d(c); let n = cfg_n(c); let w = abs_cfg(c);
    assert(w.peers.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies M::xinv_p(d, n, w, i) by {
        assert(cfg_peer_ok(c, i));
        assert(a_wf(c.a[i]));
        assert(w.peers[i].their_have is None);
        assert(vset(c.s[i].shared_heads@) =~= ISet::<int>::empty());
        assert(w.peers[i].queue == a_queue(c.a[i]));
        assert(w.peers[1 - i].doc == a_doc(c.a[1 - i]));
        assert(M::bounded(w.peers[i].queue, n)) by { assert(a_n(c.a[i]) == n); }
    }
}

pub open spec fn rp_run(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, k: nat) -> M::RP {
    choose|rp: M::RP| M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp)
        && abs_cfg(cs((k + 1) as nat)) == M::rw6(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp) && (M::good(rp) <==> cr_good(crs(k)))
}
pub proof fn lemma_rounds_wf(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, k: nat)
    requires cfg_wf(cs(0)), code_rounds(cs, crs),
    ensures cfg_wf(cs(k)), cfg_d(cs(k)) == cfg_d(cs(0)), cfg_n(cs(k)) == cfg_n(cs(0)),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        lemma_rounds_wf(cs, crs, j);
        assert(cround_ok(cs(j), cs((j + 1) as nat), crs(j)));
        lemma_round_code(cs(j), cs(k), crs(j));
    }
}

// THEOREM (liveness of the code).  Take a live session start and any run made of code rounds (every call is to the
// copied generate_sync_message / receive_sync_message / on_timeout; each generate may send the whole document), in
// which infinitely often 4 consecutive rounds lose no message.  Then some configuration has equal documents.
// Assumed: receive returns Ok on the messages it gets (they are always the peer's own generated messages); read-only
// mode is off; a shared deps function and bound n; live_start.
pub proof fn theorem_code_liveness(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound)
    requires live_start(cs(0)), code_rounds(cs, crs), code_fair(crs),
    ensures exists|K: nat| #![trigger cs(K)] a_doc(cs(K).a[0]) == a_doc(cs(K).a[1]),
{
    let d = cfg_d(cs(0)); let n = cfg_n(cs(0));
    let ws = |k: nat| abs_cfg(cs(k));
    let rps = |k: nat| rp_run(cs, crs, k);
    lemma_live_start_sinv(cs(0));
    assert(M::wf(d, n)) by { assert(cfg_peer_ok(cs(0), 0)); assert(a_wf(cs(0).a[0])); }
    assert forall|k: nat| #![trigger rps(k)] M::rvalid(d, n, ws(k), rps(k)) && ws((k + 1) as nat) == M::rw6(d, n, ws(k), rps(k)) by {
        lemma_rounds_wf(cs, crs, k);
        assert(cround_ok(cs(k), cs((k + 1) as nat), crs(k)));
        lemma_round_code(cs(k), cs((k + 1) as nat), crs(k));
        let rp = rp_run(cs, crs, k);
        assert(M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp));
    }
    assert(M::run_ok(d, n, ws, rps));
    assert forall|m: nat| #[trigger] M::win4(rps, m) by {
        assert(code_win4(crs, m));
        let k = choose|k: nat| #![trigger crs(k)] k >= m && cr_good(crs(k)) && cr_good(crs((k + 1) as nat))
            && cr_good(crs((k + 2) as nat)) && cr_good(crs((k + 3) as nat));
        assert(M::good(rps(k)) && M::good(rps((k + 1) as nat)) && M::good(rps((k + 2) as nat)) && M::good(rps((k + 3) as nat))) by {
            let _ = rps(k); let _ = rps((k + 1) as nat); let _ = rps((k + 2) as nat); let _ = rps((k + 3) as nat);
            lemma_rounds_wf(cs, crs, k); lemma_rounds_wf(cs, crs, (k + 1) as nat);
            lemma_rounds_wf(cs, crs, (k + 2) as nat); lemma_rounds_wf(cs, crs, (k + 3) as nat);
            lemma_round_code(cs(k), cs((k + 1) as nat), crs(k));
            lemma_round_code(cs((k + 1) as nat), cs((k + 2) as nat), crs((k + 1) as nat));
            lemma_round_code(cs((k + 2) as nat), cs((k + 3) as nat), crs((k + 2) as nat));
            lemma_round_code(cs((k + 3) as nat), cs((k + 4) as nat), crs((k + 3) as nat));
        }
    }
    assert(M::fair_lossy(rps));
    M::theorem_liveness(d, n, ws, rps);
    let K = choose|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc;
    assert(a_doc(cs(K).a[0]) == a_doc(cs(K).a[1]));
}


// =====================================================================================
// Part F (vlm47_amcode edits): LIVENESS OF THE CODE WITH EDITS DURING THE RUN.  A block is a code round (Part E) or
// ONE code step (`code_next`: generate, receive, timeout, drop, or a local edit `step_edit`), in any order and number.
// Fairness counts only the round blocks: infinitely often, 4 consecutive blocks are loss-free rounds.
// The local edit is still the trusted `edit_rel` (no code for it); everything else is the copied code.
// =====================================================================================
pub open spec fn code_blk(c: Cfg, c2: Cfg, isr: bool, cr: CRound) -> bool {
    if isr { cround_ok(c, c2, cr) } else { code_next(c, c2) }
}
pub open spec fn code_blocks(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool) -> bool {
    forall|k: nat| #![trigger crs(k)] code_blk(cs(k), cs((k + 1) as nat), isr(k), crs(k))
}
pub open spec fn cgr(crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool, k: nat) -> bool { isr(k) && cr_good(crs(k)) }
pub open spec fn code_gwin4(crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool, m: nat) -> bool {
    exists|k: nat| #![trigger crs(k)] k >= m && cgr(crs, isr, k) && cgr(crs, isr, (k + 1) as nat)
        && cgr(crs, isr, (k + 2) as nat) && cgr(crs, isr, (k + 3) as nat)
}
pub open spec fn code_gfair(crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool) -> bool { forall|m: nat| #[trigger] code_gwin4(crs, isr, m) }
pub open spec fn cfg_eq_from(cs: spec_fn(nat) -> Cfg, K: nat) -> bool {
    forall|j: nat| j >= K ==> a_doc(#[trigger] cs(j).a[0]) == a_doc(cs(j).a[1])
}

// a code step keeps cfg_wf and the shared deps function and bound
pub proof fn lemma_code_step_dn(c: Cfg, c2: Cfg)
    requires cfg_wf(c), code_next(c, c2), ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
{
    lemma_code_step(c, c2);
    let (who, keep0) = choose|who: int, keep: bool| step_any(c, c2, who, keep);
    assert(cfg_peer_ok(c, who));
    if step_recv(c, c2, who, keep0) {
        let (msg, a1, s1) = choose|msg: Message, a1: Automerge, s1: State| recv_rel(c, c2, who, keep0, msg, a1, s1);
        assert(c2.a == c.a.update(who, a1));
        assert(a_deps(a1) == a_deps(c.a[who]) && a_n(a1) == a_n(c.a[who]));
        assert(c2.a[who] == a1);
    } else if step_edit(c, c2, who) && !step_gen(c, c2, who) && !step_tmo(c, c2, who) && !step_drop(c, c2, who) {
        let (a1, ch) = choose|a1: Automerge, ch: int| edit_rel(c, c2, who, a1, ch);
        assert(c2.a == c.a.update(who, a1));
        assert(c2.a[who] == a1);
    } else {
        if step_gen(c, c2, who) { let (s1, r) = choose|s1: State, r: Option<Message>| gen_rel(c, c2, who, s1, r); }
        if step_tmo(c, c2, who) { let s1 = choose|s1: State| tmo_rel(c, c2, who, s1); }
        if step_drop(c, c2, who) { let m = choose|m: M::Msg| drop_rel(c, c2, who, m); }
        assert(c2.a == c.a);
    }
    assert(cfg_d(c2) == cfg_d(c) && cfg_n(c2) == cfg_n(c)) by {
        assert(cfg_peer_ok(c, 0) && cfg_peer_ok(c, 1));
        assert(a_deps(c2.a[who]) == a_deps(c.a[who]) && a_n(c2.a[who]) == a_n(c.a[who]));
        if who != 0 { assert(c2.a[0] == c.a[0]); }
    }
}
pub proof fn lemma_blocks_wf(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool, k: nat)
    requires cfg_wf(cs(0)), code_blocks(cs, crs, isr),
    ensures cfg_wf(cs(k)), cfg_d(cs(k)) == cfg_d(cs(0)), cfg_n(cs(k)) == cfg_n(cs(0)),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        lemma_blocks_wf(cs, crs, isr, j);
        assert(code_blk(cs(j), cs((j + 1) as nat), isr(j), crs(j)));
        if isr(j) { lemma_round_code(cs(j), cs(k), crs(j)); } else { lemma_code_step_dn(cs(j), cs(k)); }
    }
}
pub open spec fn blk_rp(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, k: nat) -> M::RP {
    choose|rp: M::RP| M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp)
        && abs_cfg(cs((k + 1) as nat)) == M::rw6(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp) && (M::good(rp) <==> cr_good(crs(k)))
}
pub open spec fn blk_st(cs: spec_fn(nat) -> Cfg, k: nat) -> M::Step {
    choose|st: M::Step| #[trigger] M::next(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), st, abs_cfg(cs((k + 1) as nat)))
}
// each code block is a model block (round with the chosen RP, or the chosen single step)
proof fn lemma_blk_model(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool, k: nat)
    requires cfg_wf(cs(0)), code_blocks(cs, crs, isr),
    ensures M::eblk_ok(cfg_d(cs(0)), cfg_n(cs(0)), abs_cfg(cs(k)), isr(k), blk_rp(cs, crs, k), blk_st(cs, k), abs_cfg(cs((k + 1) as nat))),
        isr(k) ==> (M::good(blk_rp(cs, crs, k)) <==> cr_good(crs(k))),
{
    lemma_blocks_wf(cs, crs, isr, k);
    assert(code_blk(cs(k), cs((k + 1) as nat), isr(k), crs(k)));
    if isr(k) {
        lemma_round_code(cs(k), cs((k + 1) as nat), crs(k));
        let rp = blk_rp(cs, crs, k);
        assert(M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp));
    } else {
        lemma_code_step(cs(k), cs((k + 1) as nat));
        let st = blk_st(cs, k);
        assert(M::next(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), st, abs_cfg(cs((k + 1) as nat))));
    }
}
// THEOREM (liveness of the code with edits).  Start: live_start.  Run: any sequence of blocks, each a code round or
// one code step (a local edit among them), any number of edits at any time.  Fairness: infinitely often 4
// consecutive blocks are loss-free rounds.  Then there is K such that for all j >= K the documents are equal.
// Assumed as in Part E, plus: the local edit conforms to the model's Edit (`edit_rel`, trusted).
pub proof fn theorem_code_liveness_edits(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRound, isr: spec_fn(nat) -> bool)
    requires live_start(cs(0)), code_blocks(cs, crs, isr), code_gfair(crs, isr),
    ensures exists|K: nat| #[trigger] cfg_eq_from(cs, K),
{
    let d = cfg_d(cs(0)); let n = cfg_n(cs(0));
    let ws = |k: nat| abs_cfg(cs(k));
    let rps = |k: nat| blk_rp(cs, crs, k);
    let sts = |k: nat| blk_st(cs, k);
    lemma_live_start_sinv(cs(0));
    assert(M::wf(d, n)) by { assert(cfg_peer_ok(cs(0), 0)); assert(a_wf(cs(0).a[0])); }
    assert forall|k: nat| #![trigger rps(k)] M::eblk_ok(d, n, ws(k), isr(k), rps(k), sts(k), ws((k + 1) as nat)) by {
        lemma_blk_model(cs, crs, isr, k);
    }
    assert(M::egrun_ok(d, n, ws, isr, rps, sts));
    assert forall|m: nat| #[trigger] M::gwin4(isr, rps, m) by {
        assert(code_gwin4(crs, isr, m));
        let k = choose|k: nat| #![trigger crs(k)] k >= m && cgr(crs, isr, k) && cgr(crs, isr, (k + 1) as nat)
            && cgr(crs, isr, (k + 2) as nat) && cgr(crs, isr, (k + 3) as nat);
        lemma_blk_model(cs, crs, isr, k); lemma_blk_model(cs, crs, isr, (k + 1) as nat);
        lemma_blk_model(cs, crs, isr, (k + 2) as nat); lemma_blk_model(cs, crs, isr, (k + 3) as nat);
        let _ = rps(k); let _ = rps((k + 1) as nat); let _ = rps((k + 2) as nat); let _ = rps((k + 3) as nat);
        assert(M::gr(isr, rps, k) && M::gr(isr, rps, (k + 1) as nat) && M::gr(isr, rps, (k + 2) as nat) && M::gr(isr, rps, (k + 3) as nat));
    }
    assert(M::gfair(isr, rps));
    M::theorem_edits_liveness_sinv(d, n, ws, isr, rps, sts);
    let K = choose|K: nat| #[trigger] M::eq_from(ws, K);
    assert(cfg_eq_from(cs, K)) by {
        assert forall|j: nat| j >= K implies a_doc(#[trigger] cs(j).a[0]) == a_doc(cs(j).a[1]) by { assert(ws(j).peers[0].doc == ws(j).peers[1].doc); }
    }
}

} // verus!
