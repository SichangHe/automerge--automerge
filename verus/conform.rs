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
    // unreachable under the fragment's precondition (supports_v2_messages is false); spec is deliberately weak.
    #[verifier::external_body]
    pub fn new_v2(data: Vec<u8>, hashes: Vec<ChangeHash>) -> (r: MessageBuilder) { unimplemented!() }
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
    // unreachable under the precondition
    #[verifier::external_body]
    pub fn save(&self) -> (r: Vec<u8>) { unimplemented!() }
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
    {
        Message {
            heads: our_heads,
            need: Vec::new(),
            have: vec![Have::default()],
            changes: ChunkList::empty(),
            flags: {
                let mut f = MessageFlags::new();
                f.set(MessageFlags::SUPPORTS_SYNC_RESET);
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
// Fragment of generate_sync_message that the model describes: no read-only, peer not v2-capable.
pub open spec fn gen_frag(s: State) -> bool { !s.read_only && !s.peer_read_only && !st_v2(s) && !st_sr(s) }

pub open spec fn opt_set_eq(o: Option<Vec<ChangeHash>>) -> bool { M::opt_set(abs_vec_opt(o)) == abs_opt_set(o) }
pub open spec fn gen_msg_ok(p: M::Peer, r: Option<Message>, om: Option<M::Msg>) -> bool {
    match (r, om) {
        (None, None) => true,
        (Some(m), Some(mm)) => {
            if M::must_reset(p) {
                // MISMATCH [M1]: the real reset message carries one empty `Have`, the model's carries none.
                vset(m.heads@) == mm.heads && vset(m.need@) == mm.need && chunk_set(m.changes) == mm.changes
                && abs_haves(m.have@) == seq![M::Have { last_sync: ISet::empty(), bloom: ISet::empty() }]
            } else { abs_msg(m) == mm }
        }
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
        }
        Err(_) => abs_state(s1) == M::Peer { in_flight: false, ..abs_state(s0) },
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
        ensures
            st_wf(*final(sync_state), *self),
            exists|bloom: ISet<int>| {
                &&& a_doc(*self).difference(M::closure(a_deps(*self), a_n(*self), vset(old(sync_state).shared_heads@))).subset_of(bloom)
                &&& abs_peer(*self, *final(sync_state)) == M::gen(a_deps(*self), a_n(*self), abs_peer(*self, *old(sync_state)), bloom, true).0
                &&& gen_msg_ok(abs_peer(*self, *old(sync_state)), r, M::gen(a_deps(*self), a_n(*self), abs_peer(*self, *old(sync_state)), bloom, true).1)
            },
    {
        let ghost s0 = *sync_state;
        let ghost d = a_deps(*self);
        let ghost n = a_n(*self);
        let ghost p = abs_peer(*self, s0);
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
                    assert(abs_peer(*self, *sync_state) == M::gen(d, n, p, bloom, true).0);
                    assert(gen_msg_ok(p, r, M::gen(d, n, p, bloom, true).1));
                    assert(st_wf(*sync_state, *self));
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
        let ghost send = M::send_set(d, n, p);
        assert(mb_cset(message_builder) == send && vset(mb_hashes(message_builder)) == send) by {
            assert(abs_haves(s0.their_have->Some_0@) =~= abs_haves(s0.their_have->Some_0@));
        }

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
                assert(M::gen(d, n, p, bloom, true).1 is None);
                return None;
            }
            if sync_state.in_flight {
                assert(M::gen(d, n, p, bloom, true).1 is None);
                return None;
            }
        }

        sync_state.have_responded = true;
        // CHANGE [C21]: `clone_from(&x)` -> `= x.clone()`.
        sync_state.last_sent_heads = our_heads.clone();
        extend_hashes(&mut sync_state.sent_hashes, message_builder.hashes());

        let mut flags = MessageFlags::new();
        flags.set(MessageFlags::SUPPORTS_SYNC_RESET);
        if sync_state.read_only {
            flags.set(MessageFlags::READ_ONLY);
        }

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

        let sync_message = message_builder
            .heads(heads_to_send)
            .have(our_have)
            .need(our_need)
            .flags(Some(flags))
            .build();

        sync_state.in_flight = true;
        assert(opt_set_eq(s0.their_heads));
        assert(vset(Seq::<u64>::empty()) =~= ISet::<int>::empty());
        assert(abs_peer(*self, *sync_state) =~= M::gen(d, n, p, bloom, true).0);
        assert(abs_msg(sync_message) =~= M::gen(d, n, p, bloom, true).1->Some_0);
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

} // verus!
