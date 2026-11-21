// FIXED model: proto.rs (vlm42) + Timeout step (clears sent_hashes and in_flight) + Edit guard (no queued change depends on a fresh local change).
// Automerge sync (commit 40063d6) two-peer protocol model + safety proof.
// Changes are ints; deps(c) < c; docs are dependency-closed sets; network = per-sender set of pending
// messages (receive may keep the message = duplicate, any pending message may be delivered = reorder,
// Drop removes = loss). Bloom filter = arbitrary superset of the true set (false positives allowed).
use vstd::prelude::*;
verus! {

pub struct Have { pub last_sync: ISet<int>, pub bloom: ISet<int> }
pub struct Msg { pub heads: ISet<int>, pub need: ISet<int>, pub have: Seq<Have>, pub changes: ISet<int> }
pub struct Peer {
    pub doc: ISet<int>, pub queue: ISet<int>, pub shared_heads: ISet<int>, pub last_sent_heads: ISet<int>,
    pub their_heads: Option<ISet<int>>, pub their_have: Option<Seq<Have>>, pub their_need: Option<ISet<int>>,
    pub sent_hashes: ISet<int>, pub in_flight: bool, pub have_responded: bool, pub needs_reset: bool,
}
pub struct World { pub peers: Seq<Peer>, pub net: Seq<ISet<Msg>> }
pub type Deps = spec_fn(int) -> ISet<int>;

pub open spec fn wf(d: Deps, n: int) -> bool {
    n >= 0 && forall|c: int, x: int| #[trigger] d(c).contains(x) ==> 0 <= x && x < c
}
pub open spec fn closed(d: Deps, s: ISet<int>) -> bool {
    forall|c: int, x: int| s.contains(c) && #[trigger] d(c).contains(x) ==> s.contains(x)
}
pub open spec fn bounded(s: ISet<int>, n: int) -> bool {
    forall|c: int| #[trigger] s.contains(c) ==> 0 <= c && c < n
}
pub open spec fn heads(d: Deps, s: ISet<int>) -> ISet<int> {
    ISet::new(|c: int| s.contains(c) && !(exists|c2: int| s.contains(c2) && #[trigger] d(c2).contains(c)))
}
pub open spec fn reach(d: Deps, h: ISet<int>, k: nat) -> ISet<int> decreases k {
    if k == 0 { h } else {
        let r = reach(d, h, (k - 1) as nat);
        ISet::new(|x: int| r.contains(x) || exists|y: int| r.contains(y) && #[trigger] d(y).contains(x))
    }
}
pub open spec fn closure(d: Deps, n: int, h: ISet<int>) -> ISet<int> { reach(d, h, n as nat) }
pub open spec fn walk(d: Deps, s: ISet<int>, q: ISet<int>, start: ISet<int>, k: nat) -> ISet<int> decreases k {
    if k == 0 { start.difference(s) } else {
        let r = walk(d, s, q, start, (k - 1) as nat);
        ISet::new(|x: int| r.contains(x)
            || (exists|y: int| r.contains(y) && q.contains(y) && #[trigger] d(y).contains(x) && !s.contains(x)))
    }
}
// missing_deps_from
pub open spec fn missing(d: Deps, n: int, s: ISet<int>, q: ISet<int>, start: ISet<int>) -> ISet<int> {
    walk(d, s, q, start, n as nat).difference(q)
}
pub open spec fn opt_set(o: Option<ISet<int>>) -> ISet<int> { match o { Some(s) => s, None => ISet::empty() } }
pub open spec fn must_reset(p: Peer) -> bool {
    match p.their_have { Some(h) => h.len() > 0 && !h[0].last_sync.subset_of(p.doc), None => false }
}
pub open spec fn all_last_sync(h: Seq<Have>) -> ISet<int> {
    ISet::new(|x: int| exists|i: int| 0 <= i < h.len() && #[trigger] h[i].last_sync.contains(x))
}
// get_hashes_to_send (bloom hits are "peer has it"; bloom misses and all their dependents are sent; plus need we have)
pub open spec fn hashes_to_send(d: Deps, n: int, s: ISet<int>, have: Seq<Have>, need: ISet<int>) -> ISet<int> {
    let need2 = need.intersect(s);
    if have.len() == 0 { need2 } else {
        let hs = s.difference(closure(d, n, all_last_sync(have)));
        let miss = ISet::new(|h: int| hs.contains(h) && forall|i: int| 0 <= i < have.len() ==> !(#[trigger] have[i].bloom.contains(h)));
        let sent = ISet::new(|h: int| hs.contains(h) && exists|m: int| miss.contains(m) && closure(d, n, ISet::empty().insert(h)).contains(m));
        need2.union(sent)
    }
}
pub open spec fn send_set(d: Deps, n: int, p: Peer) -> ISet<int> {
    match (p.their_have, p.their_need) {
        (Some(h), Some(nd)) => hashes_to_send(d, n, p.doc, h, nd).difference(p.sent_hashes),
        _ => ISet::empty(),
    }
}
// generate_sync_message returns None via the heads_equal branch
pub open spec fn report_in_sync(d: Deps, n: int, p: Peer) -> bool {
    let oh = heads(d, p.doc);
    !must_reset(p) && p.last_sent_heads == oh && p.have_responded && p.their_heads == Some(oh)
        && send_set(d, n, p) == ISet::<int>::empty()
}
// [M1 closed] Message::reset: no changes, no need, ONE empty Have (empty last_sync, empty bloom), as in the code.
// Opaque so that the round proofs (which never reach this branch) are not slowed down.
#[verifier::opaque]
pub open spec fn reset_msg(oh: ISet<int>) -> Msg {
    Msg { heads: oh, need: ISet::empty(), have: seq![Have { last_sync: ISet::empty(), bloom: ISet::empty() }], changes: ISet::empty() }
}
pub proof fn lemma_reset_msg(oh: ISet<int>)
    ensures reset_msg(oh) == (Msg { heads: oh, need: ISet::empty(), have: seq![Have { last_sync: ISet::empty(), bloom: ISet::empty() }], changes: ISet::empty() }),
{ reveal(reset_msg); }
// [M2 closed] `send` = the changes put in the message: send_set (Gen), or the whole document (GenDoc).
pub open spec fn gen_s(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool, send: ISet<int>) -> (Peer, Option<Msg>) {
    let oh = heads(d, p.doc);
    let need = missing(d, n, p.doc, p.queue, opt_set(p.their_heads));
    let have = if need.subset_of(opt_set(p.their_heads)) { seq![Have { last_sync: p.shared_heads, bloom: bloom }] } else { Seq::empty() };
    if must_reset(p) {
        (p, Some(reset_msg(oh)))
    } else {
        if p.last_sent_heads == oh && p.have_responded
            && ((p.their_heads == Some(oh) && send == ISet::<int>::empty()) || p.in_flight) {
            (p, None)
        } else {
            let hts = if p.needs_reset && fake { ISet::empty() } else { oh };
            let p2 = Peer { last_sent_heads: oh, sent_hashes: p.sent_hashes.union(send), in_flight: true,
                            have_responded: true, needs_reset: false, ..p };
            (p2, Some(Msg { heads: hts, need: need, have: have, changes: send }))
        }
    }
}
pub open spec fn gen(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool) -> (Peer, Option<Msg>) {
    gen_s(d, n, p, bloom, fake, send_set(d, n, p))
}
// drain of the change queue: maximal dependency-closed extension using pool
pub open spec fn drain_ok(d: Deps, s: ISet<int>, pool: ISet<int>, s2: ISet<int>) -> bool {
    s.subset_of(s2) && s2.subset_of(s.union(pool)) && closed(d, s2)
        && forall|c: int| pool.contains(c) && !s2.contains(c) ==> !(d(c).subset_of(s2))
}
pub open spec fn recv(d: Deps, n: int, p: Peer, m: Msg, s2: ISet<int>) -> Peer {
    let before = heads(d, p.doc);
    let pool = p.queue.union(m.changes);
    let newheads = heads(d, s2);
    let sh1 = if m.changes != ISet::<int>::empty() { newheads.difference(before).union(p.shared_heads.intersect(newheads)) } else { p.shared_heads };
    let known = m.heads.intersect(s2);
    let sent1 = p.sent_hashes.difference(closure(d, n, known));
    let lsh1 = if m.changes == ISet::<int>::empty() && m.heads == before { m.heads } else { p.last_sent_heads };
    let all_known = known == m.heads;
    let sh2 = if all_known { m.heads } else { sh1.union(known) };
    let wipe = all_known && m.heads == ISet::<int>::empty();
    Peer { doc: s2, queue: pool.difference(s2), shared_heads: sh2,
           last_sent_heads: if wipe { ISet::empty() } else { lsh1 },
           their_heads: Some(m.heads), their_have: Some(m.have), their_need: Some(m.need),
           sent_hashes: if wipe { ISet::empty() } else { sent1 },
           in_flight: false, have_responded: p.have_responded, needs_reset: p.needs_reset }
}

pub enum Step {
    Edit { who: int, c: int },
    Gen { who: int, bloom: ISet<int>, fake: bool },
    // [M2] generate_sync_message sends the whole document (send_doc / more than a third of the changes)
    GenDoc { who: int, bloom: ISet<int>, fake: bool },
    Recv { who: int, m: Msg, s2: ISet<int>, keep: bool },
    Drop { who: int, m: Msg },
    SetReset { who: int },
    Timeout { who: int },
}
pub open spec fn guard(d: Deps, n: int, w: World, st: Step) -> bool {
    match st {
        Step::Edit { who, c } => {
            let p = w.peers[who];
            (who == 0 || who == 1) && 0 <= c && c < n && !p.doc.contains(c) && !p.queue.contains(c)
            && d(c).subset_of(p.doc)
            && (forall|y: int| #[trigger] p.queue.contains(y) ==> !d(y).contains(c))
        }
        Step::Gen { who, bloom, fake } | Step::GenDoc { who, bloom, fake } => {
            let p = w.peers[who];
            (who == 0 || who == 1)
            && p.doc.difference(closure(d, n, p.shared_heads)).subset_of(bloom)
        }
        Step::Recv { who, m, s2, keep } => {
            let p = w.peers[who];
            (who == 0 || who == 1) && w.net[1 - who].contains(m)
            && bounded(p.queue.union(m.changes), n) && drain_ok(d, p.doc, p.queue.union(m.changes), s2)
            && (m.changes == ISet::<int>::empty() ==> s2 == p.doc)
        }
        Step::Drop { who, m } => (who == 0 || who == 1) && w.net[who].contains(m),
        Step::SetReset { who } => who == 0 || who == 1,
        Step::Timeout { who } => who == 0 || who == 1,
    }
}
// THE FIX: on timeout, forget what we believe is in flight and what we believe was sent.
pub open spec fn tmo(p: Peer) -> Peer { Peer { sent_hashes: ISet::empty(), in_flight: false, ..p } }
pub open spec fn apply(d: Deps, n: int, w: World, st: Step) -> World {
    match st {
        Step::Edit { who, c } => {
            let p = w.peers[who];
            World { peers: w.peers.update(who, Peer { doc: p.doc.insert(c), ..p }), net: w.net }
        }
        Step::Gen { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen(d, n, p, bloom, fake);
            World { peers: w.peers.update(who, r.0),
                    net: match r.1 { Some(m) => w.net.update(who, w.net[who].insert(m)), None => w.net } }
        }
        Step::GenDoc { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen_s(d, n, p, bloom, fake, p.doc);
            World { peers: w.peers.update(who, r.0),
                    net: match r.1 { Some(m) => w.net.update(who, w.net[who].insert(m)), None => w.net } }
        }
        Step::Recv { who, m, s2, keep } => {
            let p = w.peers[who];
            World { peers: w.peers.update(who, recv(d, n, p, m, s2)),
                    net: if keep { w.net } else { w.net.update(1 - who, w.net[1 - who].remove(m)) } }
        }
        Step::Drop { who, m } => World { peers: w.peers, net: w.net.update(who, w.net[who].remove(m)) },
        Step::SetReset { who } => {
            let p = w.peers[who];
            World { peers: w.peers.update(who, Peer { needs_reset: true, ..p }), net: w.net }
        }
        Step::Timeout { who } => {
            let p = w.peers[who];
            World { peers: w.peers.update(who, tmo(p)), net: w.net }
        }
    }
}
pub open spec fn next(d: Deps, n: int, w: World, st: Step, w2: World) -> bool {
    guard(d, n, w, st) && w2 == apply(d, n, w, st)
}
pub open spec fn init_peer() -> Peer {
    Peer { doc: ISet::empty(), queue: ISet::empty(), shared_heads: ISet::empty(), last_sent_heads: ISet::empty(),
           their_heads: None, their_have: Some(Seq::empty()), their_need: None, sent_hashes: ISet::empty(),
           in_flight: false, have_responded: false, needs_reset: false }
}
pub open spec fn init(w: World) -> bool {
    w.peers == seq![init_peer(), init_peer()] && w.net == seq![ISet::<Msg>::empty(), ISet::<Msg>::empty()]
}
pub open spec fn reachable(d: Deps, n: int, w: World, k: nat) -> bool decreases k {
    if k == 0 { init(w) } else {
        exists|w0: World, st: Step| reachable(d, n, w0, (k - 1) as nat) && next(d, n, w0, st, w)
    }
}

// ---------- safety ----------
pub open spec fn peer_inv(d: Deps, n: int, w: World, i: int) -> bool {
    let p = w.peers[i];
    let o = w.peers[1 - i];
    closed(d, p.doc) && bounded(p.doc, n)
    && (forall|m: Msg| #[trigger] w.net[i].contains(m) ==> exists|t: ISet<int>|
          closed(d, t) && bounded(t, n) && t.subset_of(p.doc) && heads(d, t) == m.heads)
    && (match p.their_heads { None => true, Some(h) => exists|t: ISet<int>|
          closed(d, t) && bounded(t, n) && t.subset_of(o.doc) && heads(d, t) == h })
}
pub open spec fn inv(d: Deps, n: int, w: World) -> bool {
    w.peers.len() == 2 && w.net.len() == 2 && peer_inv(d, n, w, 0) && peer_inv(d, n, w, 1)
}

// heads determine a closed set
proof fn lemma_sub(d: Deps, n: int, s: ISet<int>, t: ISet<int>, c: int)
    requires wf(d, n), closed(d, s), closed(d, t), bounded(s, n), bounded(t, n), heads(d, s) == heads(d, t), s.contains(c),
    ensures t.contains(c),
    decreases n - c,
{
    if heads(d, s).contains(c) {
        assert(heads(d, t).contains(c));
    } else {
        let c2 = choose|c2: int| s.contains(c2) && #[trigger] d(c2).contains(c);
        assert(c < c2);
        lemma_sub(d, n, s, t, c2);
        assert(t.contains(c));
    }
}
pub proof fn lemma_heads_determine(d: Deps, n: int, s: ISet<int>, t: ISet<int>)
    requires wf(d, n), closed(d, s), closed(d, t), bounded(s, n), bounded(t, n), heads(d, s) == heads(d, t),
    ensures s == t,
{
    assert forall|c: int| s.contains(c) implies t.contains(c) by { lemma_sub(d, n, s, t, c); }
    assert forall|c: int| t.contains(c) implies s.contains(c) by { lemma_sub(d, n, t, s, c); }
    assert(s =~= t);
}

pub proof fn lemma_init(d: Deps, n: int, w: World)
    requires wf(d, n), init(w), ensures inv(d, n, w),
{
    assert(w.peers.len() == 2);
    assert(w.net[0] == ISet::<Msg>::empty());
    assert(w.net[1] == ISet::<Msg>::empty());
    let e = ISet::<int>::empty();
    assert(closed(d, e)); assert(bounded(e, n));
}

// gen keeps docs and only emits messages whose heads are the heads of a closed sub-doc
pub proof fn lemma_step(d: Deps, n: int, w: World, st: Step, w2: World)
    requires wf(d, n), inv(d, n, w), next(d, n, w, st, w2), ensures inv(d, n, w2),
{
    let e = ISet::<int>::empty();
    assert(closed(d, e) && bounded(e, n));
    match st {
        Step::Edit { who, c } => {
            let p = w.peers[who];
            let nd = p.doc.insert(c);
            assert(closed(d, nd)) by {
                assert forall|a: int, x: int| nd.contains(a) && #[trigger] d(a).contains(x) implies nd.contains(x) by {
                    if a == c { assert(d(c).subset_of(p.doc)); assert(p.doc.contains(x)); }
                }
            }
            assert(bounded(nd, n));
            assert(w2.peers.len() == 2 && w2.net == w.net);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { Peer { doc: nd, ..p } } else { w.peers[i] });
            }
        }
        Step::Gen { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen(d, n, p, bloom, fake);
            assert(r.0.doc == p.doc);
            assert(w2.peers.len() == 2);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { r.0 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { r.0 } else { w.peers[1 - i] });
                if i == who {
                    if let Some(m) = r.1 {
                        assert(w2.net[i] == w.net[i].insert(m));
                        if must_reset(p) { lemma_reset_msg(heads(d, p.doc)); }
                        assert(m.heads == heads(d, p.doc) || m.heads == e || m.heads == heads(d, p.doc));
                        assert(heads(d, e) == e) by { assert(heads(d, e) =~= e); }
                    }
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies exists|t: ISet<int>|
                        closed(d, t) && bounded(t, n) && t.subset_of(p.doc) && heads(d, t) == m2.heads by {
                        if w.net[i].contains(m2) { } else {
                            assert(Some(m2) == r.1);
                            if m2.heads == heads(d, p.doc) {
                                assert(p.doc.subset_of(p.doc));
                            } else {
                                assert(m2.heads == e);
                                assert(heads(d, e) == e) by { assert(heads(d, e) =~= e); }
                                assert(e.subset_of(p.doc));
                            }
                        }
                    }
                } else {
                    assert(w2.net[i] == w.net[i]);
                }
            }
        }
        Step::GenDoc { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen_s(d, n, p, bloom, fake, p.doc);
            assert(r.0.doc == p.doc);
            assert(w2.peers.len() == 2);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { r.0 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { r.0 } else { w.peers[1 - i] });
                if i == who {
                    if let Some(m) = r.1 {
                        assert(w2.net[i] == w.net[i].insert(m));
                        if must_reset(p) { lemma_reset_msg(heads(d, p.doc)); }
                        assert(m.heads == heads(d, p.doc) || m.heads == e || m.heads == heads(d, p.doc));
                        assert(heads(d, e) == e) by { assert(heads(d, e) =~= e); }
                    }
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies exists|t: ISet<int>|
                        closed(d, t) && bounded(t, n) && t.subset_of(p.doc) && heads(d, t) == m2.heads by {
                        if w.net[i].contains(m2) { } else {
                            assert(Some(m2) == r.1);
                            if m2.heads == heads(d, p.doc) {
                                assert(p.doc.subset_of(p.doc));
                            } else {
                                assert(m2.heads == e);
                                assert(heads(d, e) == e) by { assert(heads(d, e) =~= e); }
                                assert(e.subset_of(p.doc));
                            }
                        }
                    }
                } else {
                    assert(w2.net[i] == w.net[i]);
                }
            }
        }
        Step::Recv { who, m, s2, keep } => {
            let p = w.peers[who];
            let q = 1 - who;
            let p2 = recv(d, n, p, m, s2);
            assert(p2.doc == s2);
            assert(bounded(s2, n)) by {
                assert forall|c: int| s2.contains(c) implies 0 <= c && c < n by {
                    assert(p.doc.contains(c) || p.queue.union(m.changes).contains(c));
                }
            }
            assert(w2.peers.len() == 2);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { p2 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { p2 } else { w.peers[1 - i] });
                if i == who {
                    assert(w2.net[i] == w.net[i]);
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies exists|t: ISet<int>|
                        closed(d, t) && bounded(t, n) && t.subset_of(s2) && heads(d, t) == m2.heads by {
                        let t = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(p.doc) && heads(d, t) == m2.heads;
                        assert(t.subset_of(s2));
                    }
                    // their_heads of receiver
                    assert(w.net[q].contains(m));
                    assert(peer_inv(d, n, w, q));
                    let t = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(w.peers[q].doc) && heads(d, t) == m.heads;
                    assert(closed(d, t) && bounded(t, n) && t.subset_of(w.peers[q].doc) && heads(d, t) == m.heads);
                } else {
                    // other peer: its net and its their_heads (witness inside p.doc subset s2)
                    if keep { assert(w2.net[i] == w.net[i]); } else { assert(w2.net[i] == w.net[i].remove(m)); }
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies w.net[i].contains(m2) by {}
                    match w.peers[i].their_heads {
                        None => {},
                        Some(h) => {
                            let t = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(p.doc) && heads(d, t) == h;
                            assert(t.subset_of(s2));
                        }
                    }
                }
            }
        }
        Step::Drop { who, m } => {
            assert(w2.peers == w.peers);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies w.net[i].contains(m2) by {
                    if i == who { assert(w2.net[i] == w.net[i].remove(m)); } else { assert(w2.net[i] == w.net[i]); }
                }
            }
        }
        Step::SetReset { who } => {
            let p = w.peers[who];
            assert(w2.net == w.net);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { Peer { needs_reset: true, ..p } } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { Peer { needs_reset: true, ..p } } else { w.peers[1 - i] });
            }
        }
        Step::Timeout { who } => {
            let p = w.peers[who];
            assert(w2.net == w.net);
            assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { tmo(p) } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { tmo(p) } else { w.peers[1 - i] });
            }
        }
    }
}

// every reachable world satisfies inv (any number of drops, duplicates, reorderings)
pub proof fn theorem_inv_reachable(d: Deps, n: int, w: World, k: nat)
    requires wf(d, n), reachable(d, n, w, k), ensures inv(d, n, w),
    decreases k,
{
    if k == 0 { lemma_init(d, n, w); } else {
        reveal_with_fuel(reachable, 2);
        assert(reachable(d, n, w, k) == (exists|w0: World, st: Step| reachable(d, n, w0, (k - 1) as nat) && next(d, n, w0, st, w)));
        assert(exists|w0: World, st: Step| #[trigger] reachable(d, n, w0, (k - 1) as nat) && #[trigger] next(d, n, w0, st, w));
        let (w0, st) = choose|w0: World, st: Step| #[trigger] reachable(d, n, w0, (k - 1) as nat) && #[trigger] next(d, n, w0, st, w);
        theorem_inv_reachable(d, n, w0, (k - 1) as nat);
        lemma_step(d, n, w0, st, w);
    }
}

// SAFETY: if both peers would answer None through the heads_equal branch, their change sets are identical.
// (from any world satisfying inv, e.g. any reachable world, or the start of a real session)
pub proof fn theorem_safety_inv(d: Deps, n: int, w: World)
    requires wf(d, n), inv(d, n, w),
        report_in_sync(d, n, w.peers[0]), report_in_sync(d, n, w.peers[1]),
    ensures w.peers[0].doc == w.peers[1].doc,
{
    let a = w.peers[0]; let b = w.peers[1];
    let ta = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(b.doc) && heads(d, t) == heads(d, a.doc);
    let tb = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(a.doc) && heads(d, t) == heads(d, b.doc);
    lemma_heads_determine(d, n, a.doc, ta);
    lemma_heads_determine(d, n, b.doc, tb);
    assert(a.doc =~= b.doc);
}
pub proof fn theorem_safety(d: Deps, n: int, w: World, k: nat)
    requires wf(d, n), reachable(d, n, w, k),
        report_in_sync(d, n, w.peers[0]), report_in_sync(d, n, w.peers[1]),
    ensures w.peers[0].doc == w.peers[1].doc,
{
    theorem_inv_reachable(d, n, w, k);
    theorem_safety_inv(d, n, w);
}

// =====================================================================================
// Part 2: extra invariant (needed by liveness).  xinv holds in every reachable world.
// =====================================================================================
pub open spec fn xinv_p(d: Deps, n: int, w: World, i: int) -> bool {
    let p = w.peers[i];
    let o = w.peers[1 - i];
    bounded(p.queue, n) && p.queue.subset_of(o.doc)
    && (forall|c: int| #[trigger] p.queue.contains(c) ==> !p.doc.contains(c) && !d(c).subset_of(p.doc))
    && p.shared_heads.subset_of(o.doc)
    && (match p.their_have { Some(h) => forall|k: int| 0 <= k < h.len() ==> #[trigger] h[k].last_sync.subset_of(p.doc), None => true })
    && (forall|m: Msg| #[trigger] w.net[i].contains(m) ==>
          m.changes.subset_of(p.doc) && bounded(m.changes, n)
          && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(o.doc)))
}
pub open spec fn xinv(d: Deps, n: int, w: World) -> bool {
    w.peers.len() == 2 && w.net.len() == 2 && xinv_p(d, n, w, 0) && xinv_p(d, n, w, 1)
}
pub open spec fn sinv(d: Deps, n: int, w: World) -> bool { inv(d, n, w) && xinv(d, n, w) }

pub proof fn lemma_xinit(d: Deps, n: int, w: World)
    requires init(w), ensures xinv(d, n, w),
{
    assert(w.net[0] == ISet::<Msg>::empty());
    assert(w.net[1] == ISet::<Msg>::empty());
    let e = ISet::<int>::empty();
    assert(bounded(e, n));
    assert(e.subset_of(e));
}

proof fn lemma_gen_props(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool)
    ensures
        gen(d, n, p, bloom, fake).0.doc == p.doc, gen(d, n, p, bloom, fake).0.queue == p.queue,
        gen(d, n, p, bloom, fake).0.shared_heads == p.shared_heads,
        gen(d, n, p, bloom, fake).0.their_have == p.their_have,
        gen(d, n, p, bloom, fake).1 is Some ==> ({
            let m = gen(d, n, p, bloom, fake).1.unwrap();
            m.changes.subset_of(p.doc)
            && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(p.shared_heads))
        }),
{
    lemma_send_subset(d, n, p);
    let r = gen(d, n, p, bloom, fake);
    if r.1 is Some {
        let m = r.1.unwrap();
        if must_reset(p) { lemma_reset_msg(heads(d, p.doc)); }
        assert(m.changes.subset_of(p.doc));
        assert forall|k: int| 0 <= k < m.have.len() implies #[trigger] m.have[k].last_sync.subset_of(p.shared_heads) by {
            if must_reset(p) {
                lemma_reset_msg(heads(d, p.doc));
                assert(m.have[k].last_sync == ISet::<int>::empty());
                assert(ISet::<int>::empty().subset_of(p.shared_heads));
            } else { assert(m.have[k].last_sync == p.shared_heads); }
        }
    }
}
pub proof fn lemma_gens_props(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool, send: ISet<int>)
    requires send.subset_of(p.doc),
    ensures
        gen_s(d, n, p, bloom, fake, send).0.doc == p.doc, gen_s(d, n, p, bloom, fake, send).0.queue == p.queue,
        gen_s(d, n, p, bloom, fake, send).0.shared_heads == p.shared_heads,
        gen_s(d, n, p, bloom, fake, send).0.their_have == p.their_have,
        gen_s(d, n, p, bloom, fake, send).1 is Some ==> ({
            let m = gen_s(d, n, p, bloom, fake, send).1.unwrap();
            m.changes.subset_of(p.doc) && m.have.len() <= 1
            && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(p.shared_heads))
        }),
{
    let r = gen_s(d, n, p, bloom, fake, send);
    if r.1 is Some {
        let m = r.1.unwrap();
        if must_reset(p) { lemma_reset_msg(heads(d, p.doc)); }
        assert(m.changes.subset_of(p.doc));
        assert forall|k: int| 0 <= k < m.have.len() implies #[trigger] m.have[k].last_sync.subset_of(p.shared_heads) by {
            if must_reset(p) {
                lemma_reset_msg(heads(d, p.doc));
                assert(m.have[k].last_sync == ISet::<int>::empty());
                assert(ISet::<int>::empty().subset_of(p.shared_heads));
            } else { assert(m.have[k].last_sync == p.shared_heads); }
        }
    }
}
proof fn lemma_send_subset(d: Deps, n: int, p: Peer)
    ensures send_set(d, n, p).subset_of(p.doc),
{
    match (p.their_have, p.their_need) {
        (Some(h), Some(nd)) => {
            let hts = hashes_to_send(d, n, p.doc, h, nd);
            assert(hts.subset_of(p.doc)) by {
                assert forall|x: int| hts.contains(x) implies p.doc.contains(x) by {}
            }
        }
        _ => {}
    }
}
proof fn sub_tr(a: ISet<int>, b: ISet<int>, c: ISet<int>)
    requires a.subset_of(b), b.subset_of(c), ensures a.subset_of(c),
{
    assert forall|x: int| a.contains(x) implies c.contains(x) by { assert(b.contains(x)); }
}
proof fn lemma_newheads(d: Deps, s: ISet<int>, s2: ISet<int>, c: int)
    requires s.subset_of(s2), heads(d, s2).contains(c), !heads(d, s).contains(c), ensures !s.contains(c),
{
    if s.contains(c) {
        assert(s2.contains(c));
        assert(!exists|c2: int| s2.contains(c2) && #[trigger] d(c2).contains(c));
        assert(heads(d, s).contains(c));
    }
}

pub proof fn lemma_xstep(d: Deps, n: int, w: World, st: Step, w2: World)
    requires wf(d, n), inv(d, n, w), xinv(d, n, w), next(d, n, w, st, w2), ensures xinv(d, n, w2),
{
    lemma_step(d, n, w, st, w2);
    assert(w2.peers.len() == 2 && w2.net.len() == 2);
    match st {
        Step::Edit { who, c } => {
            let p = w.peers[who];
            let nd = p.doc.insert(c);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { Peer { doc: nd, ..p } } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { Peer { doc: nd, ..p } } else { w.peers[1 - i] });
                assert(w2.net == w.net);
                let pi = w.peers[i]; let oi = w.peers[1 - i];
                assert(p.doc.subset_of(nd));
                assert(pi.queue.subset_of(oi.doc));
                assert(pi.shared_heads.subset_of(oi.doc));
                assert(w2.peers[i].queue == pi.queue && w2.peers[i].shared_heads == pi.shared_heads);
                assert(oi.doc.subset_of(w2.peers[1 - i].doc)) by {
                    if 1 - i == who { } else { assert(w2.peers[1 - i] == oi); }
                }
                sub_tr(pi.queue, oi.doc, w2.peers[1 - i].doc);
                sub_tr(pi.shared_heads, oi.doc, w2.peers[1 - i].doc);
                assert(pi.doc.subset_of(w2.peers[i].doc)) by { if i == who { } else { assert(w2.peers[i] == pi); } }
                match pi.their_have { Some(h) => {
                    assert forall|k: int| 0 <= k < h.len() implies #[trigger] h[k].last_sync.subset_of(w2.peers[i].doc) by {
                        sub_tr(h[k].last_sync, pi.doc, w2.peers[i].doc);
                    } }, None => {} }
                assert forall|y: int| #[trigger] w2.peers[i].queue.contains(y) implies !w2.peers[i].doc.contains(y) && !d(y).subset_of(w2.peers[i].doc) by {
                    if i == who {
                        assert(pi.queue.contains(y));
                        assert(!d(y).contains(c));
                        if d(y).subset_of(nd) {
                            assert forall|x: int| d(y).contains(x) implies p.doc.contains(x) by { assert(nd.contains(x)); assert(x != c); }
                        }
                    }
                }
                assert forall|m: Msg| #[trigger] w2.net[i].contains(m) implies
                    m.changes.subset_of(w2.peers[i].doc) && bounded(m.changes, n)
                    && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc)) by {
                    assert(w.net[i].contains(m));
                    sub_tr(m.changes, pi.doc, w2.peers[i].doc);
                    assert forall|k: int| 0 <= k < m.have.len() implies #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc) by {
                        sub_tr(m.have[k].last_sync, oi.doc, w2.peers[1 - i].doc);
                    }
                }
            }
        }
        Step::Gen { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen(d, n, p, bloom, fake);
            lemma_gen_props(d, n, p, bloom, fake);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { r.0 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { r.0 } else { w.peers[1 - i] });
                assert forall|m: Msg| #[trigger] w2.net[i].contains(m) implies
                    m.changes.subset_of(w2.peers[i].doc) && bounded(m.changes, n)
                    && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc)) by {
                    if i == who {
                        match r.1 {
                            Some(m0) => {
                                assert(w2.net[i] == w.net[i].insert(m0));
                                if m0 == m {
                                    assert(m.changes.subset_of(p.doc));
                                    assert forall|x: int| m.changes.contains(x) implies 0 <= x && x < n by {
                                        assert(p.doc.contains(x));
                                    }
                                    assert forall|k: int| 0 <= k < m.have.len() implies #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc) by {
                                        assert(m.have[k].last_sync.subset_of(p.shared_heads));
                                    }
                                } else { assert(w.net[i].contains(m)); }
                            }
                            None => { assert(w2.net[i] == w.net[i]); }
                        }
                    } else { assert(w2.net[i] == w.net[i]); assert(w.net[i].contains(m)); }
                }
            }
        }
        Step::GenDoc { who, bloom, fake } => {
            let p = w.peers[who];
            let r = gen_s(d, n, p, bloom, fake, p.doc);
            lemma_gens_props(d, n, p, bloom, fake, p.doc);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { r.0 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { r.0 } else { w.peers[1 - i] });
                assert forall|m: Msg| #[trigger] w2.net[i].contains(m) implies
                    m.changes.subset_of(w2.peers[i].doc) && bounded(m.changes, n)
                    && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc)) by {
                    if i == who {
                        match r.1 {
                            Some(m0) => {
                                assert(w2.net[i] == w.net[i].insert(m0));
                                if m0 == m {
                                    assert(m.changes.subset_of(p.doc));
                                    assert forall|x: int| m.changes.contains(x) implies 0 <= x && x < n by {
                                        assert(p.doc.contains(x));
                                    }
                                    assert forall|k: int| 0 <= k < m.have.len() implies #[trigger] m.have[k].last_sync.subset_of(w2.peers[1 - i].doc) by {
                                        assert(m.have[k].last_sync.subset_of(p.shared_heads));
                                    }
                                } else { assert(w.net[i].contains(m)); }
                            }
                            None => { assert(w2.net[i] == w.net[i]); }
                        }
                    } else { assert(w2.net[i] == w.net[i]); assert(w.net[i].contains(m)); }
                }
            }
        }
        Step::Recv { who, m, s2, keep } => {
            let p = w.peers[who];
            let q = 1 - who;
            let p2 = recv(d, n, p, m, s2);
            assert(w.net[q].contains(m));
            assert(m.changes.subset_of(w.peers[q].doc) && bounded(m.changes, n));
            assert(p.doc.subset_of(s2));
            let pool = p.queue.union(m.changes);
            assert(pool.subset_of(w.peers[q].doc)) by {
                assert forall|x: int| pool.contains(x) implies w.peers[q].doc.contains(x) by {
                    if p.queue.contains(x) { assert(p.queue.subset_of(w.peers[q].doc)); }
                }
            }
            let t = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(w.peers[q].doc) && heads(d, t) == m.heads;
            assert(m.heads.subset_of(w.peers[q].doc)) by {
                assert forall|x: int| m.heads.contains(x) implies w.peers[q].doc.contains(x) by {
                    assert(heads(d, t).contains(x)); assert(t.contains(x));
                }
            }
            assert(p2.shared_heads.subset_of(w.peers[q].doc)) by {
                let before = heads(d, p.doc);
                let newheads = heads(d, s2);
                let known = m.heads.intersect(s2);
                assert forall|x: int| p2.shared_heads.contains(x) implies w.peers[q].doc.contains(x) by {
                    if known == m.heads {
                        assert(p2.shared_heads == m.heads);
                    } else {
                        if m.changes != ISet::<int>::empty() {
                            if newheads.difference(before).contains(x) {
                                lemma_newheads(d, p.doc, s2, x);
                                assert(s2.contains(x));
                                assert(pool.contains(x));
                            }
                        }
                    }
                }
            }
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { p2 } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { p2 } else { w.peers[1 - i] });
                if i == who {
                    assert(w2.net[i] == w.net[i]);
                    assert(p2.queue == pool.difference(s2));
                    assert forall|x: int| #[trigger] p2.queue.contains(x) implies 0 <= x && x < n by {
                        assert(bounded(pool, n)); assert(pool.contains(x));
                    }
                    assert forall|x: int| #[trigger] p2.queue.contains(x) implies !p2.doc.contains(x) && !d(x).subset_of(p2.doc) by {
                        assert(pool.contains(x) && !s2.contains(x));
                    }
                    assert(p2.queue.subset_of(w.peers[q].doc));
                    match p2.their_have { Some(h) => {
                        assert forall|k: int| 0 <= k < h.len() implies #[trigger] h[k].last_sync.subset_of(p2.doc) by {
                            assert(m.have[k].last_sync.subset_of(w.peers[who].doc));
                            assert(h == m.have);
                        } }, None => {} }
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies
                        m2.changes.subset_of(p2.doc) && bounded(m2.changes, n)
                        && (forall|k: int| 0 <= k < m2.have.len() ==> #[trigger] m2.have[k].last_sync.subset_of(w2.peers[1 - i].doc)) by {
                        assert(w.net[i].contains(m2));
                    }
                } else {
                    assert forall|x: int| w2.peers[i].queue.contains(x) implies w2.peers[1 - i].doc.contains(x) by {
                        assert(w.peers[i].queue.subset_of(w.peers[1 - i].doc));
                    }
                    assert(w.peers[i].shared_heads.subset_of(s2));
                    assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies
                        m2.changes.subset_of(w2.peers[i].doc) && bounded(m2.changes, n)
                        && (forall|k: int| 0 <= k < m2.have.len() ==> #[trigger] m2.have[k].last_sync.subset_of(w2.peers[1 - i].doc)) by {
                        assert(w.net[i].contains(m2));
                        if keep { assert(w2.net[i] == w.net[i]); } else { assert(w2.net[i] == w.net[i].remove(m)); }
                        assert forall|k: int| 0 <= k < m2.have.len() implies #[trigger] m2.have[k].last_sync.subset_of(w2.peers[1 - i].doc) by {
                            assert(m2.have[k].last_sync.subset_of(w.peers[1 - i].doc));
                        }
                    }
                }
            }
        }
        Step::Drop { who, m } => {
            assert(w2.peers == w.peers);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert forall|m2: Msg| #[trigger] w2.net[i].contains(m2) implies w.net[i].contains(m2) by {
                    if i == who { assert(w2.net[i] == w.net[i].remove(m)); } else { assert(w2.net[i] == w.net[i]); }
                }
            }
        }
        Step::SetReset { who } => {
            let p = w.peers[who];
            assert(w2.net == w.net);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { Peer { needs_reset: true, ..p } } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { Peer { needs_reset: true, ..p } } else { w.peers[1 - i] });
            }
        }
        Step::Timeout { who } => {
            let p = w.peers[who];
            assert(w2.net == w.net);
            assert forall|i: int| 0 <= i < 2 implies xinv_p(d, n, w2, i) by {
                assert(w2.peers[i] == if i == who { tmo(p) } else { w.peers[i] });
                assert(w2.peers[1 - i] == if 1 - i == who { tmo(p) } else { w.peers[1 - i] });
            }
        }
    }
}

pub proof fn theorem_sinv_reachable(d: Deps, n: int, w: World, k: nat)
    requires wf(d, n), reachable(d, n, w, k), ensures sinv(d, n, w),
    decreases k,
{
    if k == 0 { lemma_init(d, n, w); lemma_xinit(d, n, w); } else {
        reveal_with_fuel(reachable, 2);
        assert(reachable(d, n, w, k) == (exists|w0: World, st: Step| reachable(d, n, w0, (k - 1) as nat) && next(d, n, w0, st, w)));
        assert(exists|w0: World, st: Step| #[trigger] reachable(d, n, w0, (k - 1) as nat) && #[trigger] next(d, n, w0, st, w));
        let (w0, st) = choose|w0: World, st: Step| #[trigger] reachable(d, n, w0, (k - 1) as nat) && #[trigger] next(d, n, w0, st, w);
        theorem_sinv_reachable(d, n, w0, (k - 1) as nat);
        lemma_step(d, n, w0, st, w);
        lemma_xstep(d, n, w0, st, w);
    }
}

// =====================================================================================
// Part 3: counting measure and step monotonicity (no edits)
// =====================================================================================
pub open spec fn cnt(s: ISet<int>, k: nat) -> nat decreases k {
    if k == 0 { 0 } else { cnt(s, (k - 1) as nat) + (if s.contains((k - 1) as int) { 1nat } else { 0nat }) }
}
proof fn cnt_mono(s: ISet<int>, t: ISet<int>, k: nat)
    requires s.subset_of(t), ensures cnt(s, k) <= cnt(t, k), decreases k,
{ if k > 0 { cnt_mono(s, t, (k - 1) as nat); } }
proof fn cnt_eq(s: ISet<int>, t: ISet<int>, k: nat)
    requires s.subset_of(t), cnt(s, k) == cnt(t, k),
    ensures forall|c: int| 0 <= c < k && t.contains(c) ==> s.contains(c), decreases k,
{
    if k > 0 {
        cnt_mono(s, t, (k - 1) as nat);
        cnt_eq(s, t, (k - 1) as nat);
        assert(s.contains((k - 1) as int) == t.contains((k - 1) as int));
    }
}

pub open spec fn gset(w: World, a: int) -> ISet<int> { w.peers[1 - a].doc.difference(w.peers[a].doc) }
pub open spec fn rset(w: World, a: int) -> ISet<int> { w.peers[1 - a].doc.difference(w.peers[a].doc.union(w.peers[a].queue)) }
pub open spec fn phi(n: int, w: World) -> nat {
    cnt(gset(w, 0), n as nat) + cnt(gset(w, 1), n as nat) + cnt(rset(w, 0), n as nat) + cnt(rset(w, 1), n as nat)
}
pub open spec fn rel_i(w: World, w2: World, i: int) -> bool {
    w.peers[i].doc.subset_of(w2.peers[i].doc)
    && w2.peers[i].doc.subset_of(w.peers[i].doc.union(w.peers[1 - i].doc))
    && gset(w2, i).subset_of(gset(w, i)) && rset(w2, i).subset_of(rset(w, i))
}
pub open spec fn rel(w: World, w2: World) -> bool { rel_i(w, w2, 0) && rel_i(w, w2, 1) }

pub proof fn lemma_rel_trans(w: World, w1: World, w2: World)
    requires w.peers.len() == 2, w1.peers.len() == 2, w2.peers.len() == 2, rel(w, w1), rel(w1, w2), ensures rel(w, w2),
{
    assert forall|i: int| 0 <= i < 2 implies rel_i(w, w2, i) by {
        assert(rel_i(w, w1, i) && rel_i(w1, w2, i) && rel_i(w, w1, 1 - i) && rel_i(w1, w2, 1 - i));
        assert forall|x: int| w.peers[i].doc.contains(x) implies w2.peers[i].doc.contains(x) by {
            assert(w1.peers[i].doc.contains(x));
        }
        assert forall|x: int| w2.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {
            if !w1.peers[i].doc.contains(x) { assert(w1.peers[1 - i].doc.contains(x)); }
        }
        assert forall|x: int| gset(w2, i).contains(x) implies gset(w, i).contains(x) by { assert(gset(w1, i).contains(x)); }
        assert forall|x: int| rset(w2, i).contains(x) implies rset(w, i).contains(x) by { assert(rset(w1, i).contains(x)); }
    }
}
pub proof fn lemma_rel_refl(w: World)
    requires w.peers.len() == 2, ensures rel(w, w),
{
    assert forall|i: int| 0 <= i < 2 implies rel_i(w, w, i) by {
        assert forall|x: int| w.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {}
    }
}
pub proof fn lemma_phi_le(n: int, w: World, w2: World)
    requires n >= 0, w.peers.len() == 2, w2.peers.len() == 2, rel(w, w2), ensures phi(n, w2) <= phi(n, w),
{
    cnt_mono(gset(w2, 0), gset(w, 0), n as nat); cnt_mono(gset(w2, 1), gset(w, 1), n as nat);
    cnt_mono(rset(w2, 0), rset(w, 0), n as nat); cnt_mono(rset(w2, 1), rset(w, 1), n as nat);
}

pub open spec fn passive_step(st: Step) -> bool { match st { Step::Edit { .. } => false, _ => true } }

pub proof fn lemma_rel_step(d: Deps, n: int, w: World, st: Step, w2: World)
    requires wf(d, n), inv(d, n, w), xinv(d, n, w), next(d, n, w, st, w2), passive_step(st), ensures rel(w, w2),
{
    lemma_xstep(d, n, w, st, w2);
    lemma_step(d, n, w, st, w2);
    assert(w2.peers.len() == 2);
    match st {
        Step::Recv { who, m, s2, keep } => {
            let p = w.peers[who];
            let q = 1 - who;
            let p2 = recv(d, n, p, m, s2);
            let pool = p.queue.union(m.changes);
            assert(w.net[q].contains(m));
            assert(pool.subset_of(w.peers[q].doc)) by {
                assert forall|x: int| pool.contains(x) implies w.peers[q].doc.contains(x) by {
                    if p.queue.contains(x) { assert(p.queue.subset_of(w.peers[q].doc)); }
                }
            }
            assert(w2.peers[who] == p2 && w2.peers[q] == w.peers[q]);
            assert forall|i: int| 0 <= i < 2 implies rel_i(w, w2, i) by {
                if i == who {
                    assert(p.doc.subset_of(s2) && s2.subset_of(p.doc.union(pool)));
                    assert forall|x: int| s2.contains(x) implies p.doc.union(w.peers[q].doc).contains(x) by {
                        if !p.doc.contains(x) { assert(pool.contains(x)); }
                    }
                    assert forall|x: int| gset(w2, i).contains(x) implies gset(w, i).contains(x) by {}
                    assert forall|x: int| rset(w2, i).contains(x) implies rset(w, i).contains(x) by {
                        assert(!p2.doc.contains(x) && !p2.queue.contains(x));
                        if p.queue.contains(x) { assert(pool.contains(x)); assert(s2.contains(x) || p2.queue.contains(x)); }
                    }
                } else {
                    assert forall|x: int| gset(w2, i).contains(x) implies gset(w, i).contains(x) by {
                        if !p.doc.contains(x) { assert(pool.contains(x)); }
                    }
                    assert forall|x: int| rset(w2, i).contains(x) implies rset(w, i).contains(x) by {
                        if !p.doc.contains(x) { assert(pool.contains(x)); }
                    }
                    assert forall|x: int| w.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {}
                }
            }
        }
        Step::Gen { who, bloom, fake } => {
            let p = w.peers[who];
            lemma_gen_props(d, n, p, bloom, fake);
            let r = gen(d, n, p, bloom, fake);
            assert(w2.peers[who] == r.0);
            assert forall|i: int| 0 <= i < 2 implies rel_i(w, w2, i) by {
                assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[i].queue == w.peers[i].queue);
                assert(w2.peers[1 - i].doc == w.peers[1 - i].doc && w2.peers[1 - i].queue == w.peers[1 - i].queue);
                assert forall|x: int| w.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {}
                assert(gset(w2, i) == gset(w, i) && rset(w2, i) == rset(w, i));
                assert(gset(w2, i).subset_of(gset(w, i)) && rset(w2, i).subset_of(rset(w, i)));
            }
        }
        Step::Timeout { who } => {
            assert forall|i: int| 0 <= i < 2 implies rel_i(w, w2, i) by {
                assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[i].queue == w.peers[i].queue);
                assert(w2.peers[1 - i].doc == w.peers[1 - i].doc && w2.peers[1 - i].queue == w.peers[1 - i].queue);
                assert forall|x: int| w.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {}
                assert(gset(w2, i) == gset(w, i) && rset(w2, i) == rset(w, i));
                assert(gset(w2, i).subset_of(gset(w, i)) && rset(w2, i).subset_of(rset(w, i)));
            }
        }
        _ => {
            assert forall|i: int| 0 <= i < 2 implies rel_i(w, w2, i) by {
                assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[i].queue == w.peers[i].queue);
                assert(w2.peers[1 - i].doc == w.peers[1 - i].doc && w2.peers[1 - i].queue == w.peers[1 - i].queue);
                assert forall|x: int| w.peers[i].doc.contains(x) implies w.peers[i].doc.union(w.peers[1 - i].doc).contains(x) by {}
                assert(gset(w2, i) == gset(w, i) && rset(w2, i) == rset(w, i));
                assert(gset(w2, i).subset_of(gset(w, i)) && rset(w2, i).subset_of(rset(w, i)));
            }
        }
    }
}

// =====================================================================================
// Part 4: lock-step rounds (a particular scheduler of the model; every round is 4-6 model steps)
//   Timeout A; Timeout B; Gen A; Gen B; then each generated message is either dropped (loss) or received.
// =====================================================================================
pub struct RP {
    pub ba: ISet<int>, pub fa: bool, pub bb: ISet<int>, pub fb: bool,
    pub s2a: ISet<int>, pub s2b: ISet<int>, pub lossa: bool, pub lossb: bool,
    // [vlm47#3] da/db: the peer's Gen in this round sends the whole document (GenDoc) instead of send_set
    pub da: bool, pub db: bool,
}
pub open spec fn gstep(who: int, bloom: ISet<int>, fake: bool, isdoc: bool) -> Step {
    if isdoc { Step::GenDoc { who, bloom, fake } } else { Step::Gen { who, bloom, fake } }
}
pub open spec fn gen_x(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool, isdoc: bool) -> (Peer, Option<Msg>) {
    gen_s(d, n, p, bloom, fake, if isdoc { p.doc } else { send_set(d, n, p) })
}
pub open spec fn rw1(d: Deps, n: int, w: World) -> World { apply(d, n, w, Step::Timeout { who: 0 }) }
pub open spec fn rw2(d: Deps, n: int, w: World) -> World { apply(d, n, rw1(d, n, w), Step::Timeout { who: 1 }) }
pub open spec fn rw3(d: Deps, n: int, w: World, rp: RP) -> World { apply(d, n, rw2(d, n, w), gstep(0, rp.ba, rp.fa, rp.da)) }
pub open spec fn rw4(d: Deps, n: int, w: World, rp: RP) -> World { apply(d, n, rw3(d, n, w, rp), gstep(1, rp.bb, rp.fb, rp.db)) }
pub open spec fn msg_a(d: Deps, n: int, w: World, rp: RP) -> Option<Msg> { gen_x(d, n, rw2(d, n, w).peers[0], rp.ba, rp.fa, rp.da).1 }
pub open spec fn msg_b(d: Deps, n: int, w: World, rp: RP) -> Option<Msg> { gen_x(d, n, rw3(d, n, w, rp).peers[1], rp.bb, rp.fb, rp.db).1 }
pub open spec fn st5(rp: RP, m: Msg) -> Step {
    if rp.lossa { Step::Drop { who: 0, m } } else { Step::Recv { who: 1, m, s2: rp.s2b, keep: false } }
}
pub open spec fn st6(rp: RP, m: Msg) -> Step {
    if rp.lossb { Step::Drop { who: 1, m } } else { Step::Recv { who: 0, m, s2: rp.s2a, keep: false } }
}
pub open spec fn rw5(d: Deps, n: int, w: World, rp: RP) -> World {
    match msg_a(d, n, w, rp) { Some(m) => apply(d, n, rw4(d, n, w, rp), st5(rp, m)), None => rw4(d, n, w, rp) }
}
pub open spec fn rw6(d: Deps, n: int, w: World, rp: RP) -> World {
    match msg_b(d, n, w, rp) { Some(m) => apply(d, n, rw5(d, n, w, rp), st6(rp, m)), None => rw5(d, n, w, rp) }
}
pub open spec fn rvalid(d: Deps, n: int, w: World, rp: RP) -> bool {
    guard(d, n, w, Step::Timeout { who: 0 })
    && guard(d, n, rw1(d, n, w), Step::Timeout { who: 1 })
    && guard(d, n, rw2(d, n, w), gstep(0, rp.ba, rp.fa, rp.da))
    && guard(d, n, rw3(d, n, w, rp), gstep(1, rp.bb, rp.fb, rp.db))
    && (match msg_a(d, n, w, rp) { Some(m) => guard(d, n, rw4(d, n, w, rp), st5(rp, m)), None => true })
    && (match msg_b(d, n, w, rp) { Some(m) => guard(d, n, rw5(d, n, w, rp), st6(rp, m)), None => true })
}
pub open spec fn good(rp: RP) -> bool { !rp.lossa && !rp.lossb }

proof fn lemma_one(d: Deps, n: int, w: World, st: Step, w2: World)
    requires wf(d, n), sinv(d, n, w), next(d, n, w, st, w2), passive_step(st), ensures sinv(d, n, w2), rel(w, w2),
{
    lemma_step(d, n, w, st, w2); lemma_xstep(d, n, w, st, w2); lemma_rel_step(d, n, w, st, w2);
}

pub proof fn lemma_round(d: Deps, n: int, w: World, rp: RP)
    requires wf(d, n), sinv(d, n, w), rvalid(d, n, w, rp),
    ensures sinv(d, n, rw6(d, n, w, rp)), rel(w, rw6(d, n, w, rp)),
{
    let w1 = rw1(d, n, w); let w2 = rw2(d, n, w); let w3 = rw3(d, n, w, rp); let w4 = rw4(d, n, w, rp);
    let w5 = rw5(d, n, w, rp); let w6 = rw6(d, n, w, rp);
    lemma_one(d, n, w, Step::Timeout { who: 0 }, w1);
    lemma_one(d, n, w1, Step::Timeout { who: 1 }, w2);
    lemma_one(d, n, w2, gstep(0, rp.ba, rp.fa, rp.da), w3);
    lemma_one(d, n, w3, gstep(1, rp.bb, rp.fb, rp.db), w4);
    lemma_rel_trans(w, w1, w2); lemma_rel_trans(w, w2, w3); lemma_rel_trans(w, w3, w4);
    match msg_a(d, n, w, rp) {
        Some(m) => { lemma_one(d, n, w4, st5(rp, m), w5); lemma_rel_trans(w, w4, w5); }
        None => { lemma_rel_refl(w4); lemma_rel_trans(w, w4, w5); }
    }
    match msg_b(d, n, w, rp) {
        Some(m) => { lemma_one(d, n, w5, st6(rp, m), w6); lemma_rel_trans(w, w5, w6); }
        None => { lemma_rel_refl(w5); lemma_rel_trans(w, w5, w6); }
    }
}

// peer-level view of a round
pub open spec fn tga(d: Deps, n: int, w: World, rp: RP) -> (Peer, Option<Msg>) { gen_x(d, n, tmo(w.peers[0]), rp.ba, rp.fa, rp.da) }
pub open spec fn tgb(d: Deps, n: int, w: World, rp: RP) -> (Peer, Option<Msg>) { gen_x(d, n, tmo(w.peers[1]), rp.bb, rp.fb, rp.db) }
pub open spec fn fin_b(d: Deps, n: int, w: World, rp: RP) -> Peer {
    match tga(d, n, w, rp).1 {
        Some(m) => if rp.lossa { tgb(d, n, w, rp).0 } else { recv(d, n, tgb(d, n, w, rp).0, m, rp.s2b) },
        None => tgb(d, n, w, rp).0,
    }
}
pub open spec fn fin_a(d: Deps, n: int, w: World, rp: RP) -> Peer {
    match tgb(d, n, w, rp).1 {
        Some(m) => if rp.lossb { tga(d, n, w, rp).0 } else { recv(d, n, tga(d, n, w, rp).0, m, rp.s2a) },
        None => tga(d, n, w, rp).0,
    }
}
pub proof fn lemma_round_peers(d: Deps, n: int, w: World, rp: RP)
    requires wf(d, n), sinv(d, n, w), rvalid(d, n, w, rp),
    ensures rw6(d, n, w, rp).peers.len() == 2, rw6(d, n, w, rp).peers[0] == fin_a(d, n, w, rp), rw6(d, n, w, rp).peers[1] == fin_b(d, n, w, rp),
{
    let w1 = rw1(d, n, w); let w2 = rw2(d, n, w); let w3 = rw3(d, n, w, rp); let w4 = rw4(d, n, w, rp);
    let w5 = rw5(d, n, w, rp); let w6 = rw6(d, n, w, rp);
    assert(w.peers.len() == 2);
    assert(w1.peers == w.peers.update(0, tmo(w.peers[0])));
    assert(w2.peers == w1.peers.update(1, tmo(w.peers[1])));
    assert(w2.peers[0] == tmo(w.peers[0]) && w2.peers[1] == tmo(w.peers[1]));
    assert(w2.net == w.net);
    let ga = tga(d, n, w, rp);
    assert(w3.peers == w2.peers.update(0, ga.0));
    assert(w3.peers[1] == tmo(w.peers[1]));
    let gb = tgb(d, n, w, rp);
    assert(w4.peers == w3.peers.update(1, gb.0));
    assert(w4.peers[0] == ga.0 && w4.peers[1] == gb.0 && w4.peers.len() == 2);
    match msg_a(d, n, w, rp) {
        Some(m) => {
            if rp.lossa { assert(w5.peers == w4.peers); }
            else { assert(w5.peers == w4.peers.update(1, recv(d, n, w4.peers[1], m, rp.s2b))); }
        }
        None => {}
    }
    assert(w5.peers.len() == 2);
    assert(w5.peers[0] == ga.0);
    match msg_b(d, n, w, rp) {
        Some(m) => {
            if rp.lossb { assert(w6.peers == w5.peers); }
            else { assert(w6.peers == w5.peers.update(0, recv(d, n, w5.peers[0], m, rp.s2a))); }
        }
        None => {}
    }
}

// =====================================================================================
// Part 5: one round, facts about the sender's message and the receiver's resulting state
// =====================================================================================
proof fn lemma_head_out(d: Deps, n: int, sb: ISet<int>, sa: ISet<int>, c: int)
    requires wf(d, n), closed(d, sa), bounded(sb, n), sb.contains(c), !sa.contains(c),
    ensures exists|h: int| heads(d, sb).contains(h) && !sa.contains(h),
    decreases n - c,
{
    if !heads(d, sb).contains(c) {
        let c2 = choose|c2: int| sb.contains(c2) && #[trigger] d(c2).contains(c);
        assert(!sa.contains(c2)) by { if sa.contains(c2) { assert(sa.contains(c)); } }
        assert(c < c2);
        lemma_head_out(d, n, sb, sa, c2);
    }
}
proof fn lemma_heads_ne(d: Deps, n: int, sa: ISet<int>, sb: ISet<int>)
    requires wf(d, n), closed(d, sa), closed(d, sb), bounded(sa, n), bounded(sb, n), !sb.subset_of(sa),
    ensures heads(d, sb) != heads(d, sa),
{
    if heads(d, sb) == heads(d, sa) {
        lemma_heads_determine(d, n, sa, sb);
        assert(sb.subset_of(sa));
    }
}
proof fn lemma_not_known(d: Deps, n: int, w: World, a: int)
    requires wf(d, n), sinv(d, n, w), 0 <= a < 2, !w.peers[1 - a].doc.subset_of(w.peers[a].doc),
    ensures w.peers[1 - a].their_heads != Some(heads(d, w.peers[1 - a].doc)),
{
    let b = 1 - a;
    assert(peer_inv(d, n, w, b));
    if w.peers[b].their_heads == Some(heads(d, w.peers[b].doc)) {
        let t = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(w.peers[a].doc) && heads(d, t) == heads(d, w.peers[b].doc);
        lemma_heads_determine(d, n, w.peers[b].doc, t);
        assert(w.peers[b].doc.subset_of(w.peers[a].doc));
    }
}
proof fn lemma_no_reset(d: Deps, n: int, w: World, i: int)
    requires sinv(d, n, w), 0 <= i < 2, ensures !must_reset(w.peers[i]),
{
    assert(xinv_p(d, n, w, i));
    match w.peers[i].their_have {
        Some(h) => { if h.len() > 0 { assert(h[0].last_sync.subset_of(w.peers[i].doc)); } }
        None => {}
    }
}
proof fn lemma_gen_ns(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool, isdoc: bool)
    requires !must_reset(p), !p.in_flight, p.their_heads != Some(heads(d, p.doc)),
    ensures
        gen_x(d, n, p, bloom, fake, isdoc).1 is Some,
        ({ let m = gen_x(d, n, p, bloom, fake, isdoc).1.unwrap();
           m.heads == (if p.needs_reset && fake { ISet::<int>::empty() } else { heads(d, p.doc) })
           && m.need == missing(d, n, p.doc, p.queue, opt_set(p.their_heads))
           && m.changes == (if isdoc { p.doc } else { send_set(d, n, p) }) }),
        gen_x(d, n, p, bloom, fake, isdoc).0.needs_reset == false,
        gen_x(d, n, p, bloom, fake, isdoc).0.their_heads == p.their_heads,
{}
proof fn lemma_genx_props(d: Deps, n: int, p: Peer, bloom: ISet<int>, fake: bool, isdoc: bool)
    ensures
        gen_x(d, n, p, bloom, fake, isdoc).0.doc == p.doc, gen_x(d, n, p, bloom, fake, isdoc).0.queue == p.queue,
        gen_x(d, n, p, bloom, fake, isdoc).0.shared_heads == p.shared_heads,
        gen_x(d, n, p, bloom, fake, isdoc).0.their_have == p.their_have,
        gen_x(d, n, p, bloom, fake, isdoc).1 is Some ==> ({
            let m = gen_x(d, n, p, bloom, fake, isdoc).1.unwrap();
            m.changes.subset_of(p.doc)
            && (forall|k: int| 0 <= k < m.have.len() ==> #[trigger] m.have[k].last_sync.subset_of(p.shared_heads))
        }),
{
    lemma_send_subset(d, n, p);
    lemma_gens_props(d, n, p, bloom, fake, if isdoc { p.doc } else { send_set(d, n, p) });
}

// ---- walk / missing
proof fn lemma_walk_notin(d: Deps, s: ISet<int>, q: ISet<int>, st: ISet<int>, k: nat, x: int)
    requires walk(d, s, q, st, k).contains(x), ensures !s.contains(x), decreases k,
{
    if k > 0 {
        if walk(d, s, q, st, (k - 1) as nat).contains(x) { lemma_walk_notin(d, s, q, st, (k - 1) as nat, x); }
    }
}
proof fn lemma_walk_sub(d: Deps, s: ISet<int>, q: ISet<int>, st: ISet<int>, t: ISet<int>, k: nat)
    requires closed(d, t), st.subset_of(t), ensures walk(d, s, q, st, k).subset_of(t), decreases k,
{
    if k > 0 {
        lemma_walk_sub(d, s, q, st, t, (k - 1) as nat);
        let r = walk(d, s, q, st, (k - 1) as nat);
        assert forall|x: int| walk(d, s, q, st, k).contains(x) implies t.contains(x) by {
            if !r.contains(x) {
                let y = choose|y: int| r.contains(y) && q.contains(y) && #[trigger] d(y).contains(x) && !s.contains(x);
                assert(t.contains(y));
            }
        }
    }
}
proof fn lemma_walk_mono(d: Deps, s: ISet<int>, q: ISet<int>, st: ISet<int>, k1: nat, k2: nat)
    requires k1 <= k2, ensures walk(d, s, q, st, k1).subset_of(walk(d, s, q, st, k2)), decreases k2,
{
    if k1 < k2 {
        lemma_walk_mono(d, s, q, st, k1, (k2 - 1) as nat);
        let r = walk(d, s, q, st, (k2 - 1) as nat);
        assert forall|x: int| walk(d, s, q, st, k1).contains(x) implies walk(d, s, q, st, k2).contains(x) by {
            assert(r.contains(x));
        }
    }
}
proof fn lemma_chain(d: Deps, n: int, s: ISet<int>, q: ISet<int>, st: ISet<int>, y: int, k: nat)
    requires wf(d, n), 0 <= y, walk(d, s, q, st, k).contains(y), k + y + 1 <= n,
        forall|c: int| #[trigger] q.contains(c) ==> !d(c).subset_of(s),
    ensures exists|x: int| walk(d, s, q, st, n as nat).contains(x) && !q.contains(x),
    decreases y,
{
    if !q.contains(y) {
        lemma_walk_mono(d, s, q, st, k, n as nat);
        assert(walk(d, s, q, st, n as nat).contains(y));
    } else {
        assert(!d(y).subset_of(s));
        let z = choose|z: int| d(y).contains(z) && !s.contains(z);
        assert(0 <= z && z < y);
        let r = walk(d, s, q, st, k);
        assert(walk(d, s, q, st, (k + 1) as nat).contains(z)) by { assert(r.contains(y) && q.contains(y) && d(y).contains(z) && !s.contains(z)); }
        lemma_chain(d, n, s, q, st, z, (k + 1) as nat);
    }
}
proof fn lemma_exists_missing(d: Deps, n: int, sa: ISet<int>, qa: ISet<int>, sb: ISet<int>)
    requires wf(d, n), closed(d, sa), closed(d, sb), bounded(sb, n), !sb.subset_of(sa),
        forall|c: int| #[trigger] qa.contains(c) ==> !d(c).subset_of(sa),
    ensures exists|x: int| missing(d, n, sa, qa, heads(d, sb)).contains(x) && sb.contains(x) && !sa.contains(x) && !qa.contains(x),
{
    let c = choose|c: int| sb.contains(c) && !sa.contains(c);
    lemma_head_out(d, n, sb, sa, c);
    let h = choose|h: int| heads(d, sb).contains(h) && !sa.contains(h);
    assert(sb.contains(h));
    assert(walk(d, sa, qa, heads(d, sb), 0).contains(h));
    lemma_chain(d, n, sa, qa, heads(d, sb), h, 0);
    let x = choose|x: int| walk(d, sa, qa, heads(d, sb), n as nat).contains(x) && !qa.contains(x);
    lemma_walk_sub(d, sa, qa, heads(d, sb), sb, n as nat);
    lemma_walk_notin(d, sa, qa, heads(d, sb), n as nat, x);
    assert(heads(d, sb).subset_of(sb));
}

// ---- round facts
pub open spec fn tg(d: Deps, n: int, w: World, rp: RP, c: int) -> (Peer, Option<Msg>) { if c == 0 { tga(d, n, w, rp) } else { tgb(d, n, w, rp) } }
pub open spec fn fin(d: Deps, n: int, w: World, rp: RP, c: int) -> Peer { if c == 0 { fin_a(d, n, w, rp) } else { fin_b(d, n, w, rp) } }
pub open spec fn isdoc(rp: RP, c: int) -> bool { if c == 0 { rp.da } else { rp.db } }
pub open spec fn flag(rp: RP, c: int) -> bool { if c == 0 { rp.fa } else { rp.fb } }

proof fn lemma_rw4(d: Deps, n: int, w: World, rp: RP)
    requires wf(d, n), sinv(d, n, w),
    ensures rw4(d, n, w, rp).peers.len() == 2, rw4(d, n, w, rp).peers[0] == tga(d, n, w, rp).0, rw4(d, n, w, rp).peers[1] == tgb(d, n, w, rp).0,
{
    let w1 = rw1(d, n, w); let w2 = rw2(d, n, w); let w3 = rw3(d, n, w, rp);
    assert(w2.peers[0] == tmo(w.peers[0]) && w2.peers[1] == tmo(w.peers[1]));
    assert(w3.peers == w2.peers.update(0, tga(d, n, w, rp).0));
    assert(w3.peers[1] == tmo(w.peers[1]));
}

pub proof fn lemma_msg_of(d: Deps, n: int, w: World, rp: RP, c: int)
    requires wf(d, n), sinv(d, n, w), rvalid(d, n, w, rp), good(rp), 0 <= c < 2,
        w.peers[c].their_heads != Some(heads(d, w.peers[c].doc)),
    ensures
        tg(d, n, w, rp, c).1 is Some,
        ({ let m = tg(d, n, w, rp, c).1.unwrap();
           let pc = w.peers[c];
           let fo = fin(d, n, w, rp, 1 - c);
           m.heads == (if pc.needs_reset && flag(rp, c) { ISet::<int>::empty() } else { heads(d, pc.doc) })
           && m.need == missing(d, n, pc.doc, pc.queue, opt_set(pc.their_heads))
           && m.changes == (if isdoc(rp, c) { pc.doc } else { send_set(d, n, tmo(pc)) })
           && fo.their_heads == Some(m.heads) && fo.their_need == Some(m.need) && fo.their_have == Some(m.have)
           && (forall|x: int| m.changes.contains(x) ==> fo.doc.contains(x) || fo.queue.contains(x)) }),
        fin(d, n, w, rp, c).needs_reset == false,
{
    lemma_no_reset(d, n, w, c);
    let pc = w.peers[c];
    let t = tmo(pc);
    assert(!must_reset(t));
    lemma_gen_ns(d, n, t, if c == 0 { rp.ba } else { rp.bb }, flag(rp, c), isdoc(rp, c));
    lemma_genx_props(d, n, t, if c == 0 { rp.ba } else { rp.bb }, flag(rp, c), isdoc(rp, c));
    lemma_rw4(d, n, w, rp);
    let g = tg(d, n, w, rp, c);
    let m = g.1.unwrap();
    let o = 1 - c;
    assert(w.peers.len() == 2);
    // the receiver's drain guard
    if c == 0 {
        assert(msg_a(d, n, w, rp) == g.1);
        assert(rw5(d, n, w, rp).peers.len() == 2 || true);
        assert(guard(d, n, rw4(d, n, w, rp), st5(rp, m)));
        let go = tgb(d, n, w, rp).0;
        assert(go.doc == w.peers[1].doc && go.queue == w.peers[1].queue);
        assert(drain_ok(d, go.doc, go.queue.union(m.changes), rp.s2b));
        let r = recv(d, n, go, m, rp.s2b);
        assert(fin_b(d, n, w, rp) == r);
        assert forall|x: int| m.changes.contains(x) implies r.doc.contains(x) || r.queue.contains(x) by {
            assert(go.queue.union(m.changes).contains(x));
        }
    } else {
        assert(msg_b(d, n, w, rp) == g.1);
        assert(guard(d, n, rw5(d, n, w, rp), st6(rp, m)));
        let go = tga(d, n, w, rp).0;
        // rw5 peer 0 is go (peer 0 untouched by a message to peer 1)
        let w4 = rw4(d, n, w, rp);
        let w5 = rw5(d, n, w, rp);
        match msg_a(d, n, w, rp) {
            Some(m0) => {
                if rp.lossa { assert(w5.peers == w4.peers); }
                else { assert(w5.peers == w4.peers.update(1, recv(d, n, w4.peers[1], m0, rp.s2b))); }
            }
            None => {}
        }
        assert(w5.peers[0] == go);
        assert(go.doc == w.peers[0].doc && go.queue == w.peers[0].queue);
        assert(drain_ok(d, go.doc, go.queue.union(m.changes), rp.s2a));
        let r = recv(d, n, go, m, rp.s2a);
        assert(fin_a(d, n, w, rp) == r);
        assert forall|x: int| m.changes.contains(x) implies r.doc.contains(x) || r.queue.contains(x) by {
            assert(go.queue.union(m.changes).contains(x));
        }
    }
}

// =====================================================================================
// Part 6: four good rounds strictly decrease phi unless the docs are equal
// =====================================================================================
proof fn lemma_const(d: Deps, n: int, w: World, w2: World)
    requires wf(d, n), sinv(d, n, w), sinv(d, n, w2), rel(w, w2), phi(n, w2) == phi(n, w),
    ensures forall|i: int| 0 <= i < 2 ==> (w2.peers[i].doc == w.peers[i].doc && w2.peers[i].queue == w.peers[i].queue
        && gset(w2, i) == gset(w, i) && rset(w2, i) == rset(w, i)),
{
    cnt_mono(gset(w2, 0), gset(w, 0), n as nat); cnt_mono(gset(w2, 1), gset(w, 1), n as nat);
    cnt_mono(rset(w2, 0), rset(w, 0), n as nat); cnt_mono(rset(w2, 1), rset(w, 1), n as nat);
    assert(inv(d, n, w) && inv(d, n, w2));
    assert forall|i: int| 0 <= i < 2 implies (w2.peers[i].doc == w.peers[i].doc
        && gset(w2, i) == gset(w, i) && rset(w2, i) == rset(w, i)) by {
        assert(peer_inv(d, n, w, 0) && peer_inv(d, n, w, 1) && peer_inv(d, n, w2, 0) && peer_inv(d, n, w2, 1));
        assert(rel_i(w, w2, i));
        cnt_eq(gset(w2, i), gset(w, i), n as nat);
        cnt_eq(rset(w2, i), rset(w, i), n as nat);
        assert(gset(w2, i) =~= gset(w, i)) by {
            assert forall|x: int| gset(w, i).contains(x) implies gset(w2, i).contains(x) by {
                assert(w.peers[1 - i].doc.contains(x));
                assert(bounded(w.peers[1 - i].doc, n));
            }
        }
        assert(rset(w2, i) =~= rset(w, i)) by {
            assert forall|x: int| rset(w, i).contains(x) implies rset(w2, i).contains(x) by {
                assert(w.peers[1 - i].doc.contains(x));
                assert(bounded(w.peers[1 - i].doc, n));
            }
        }
        // docs: elements gained by doc_i would leave gset
        assert forall|x: int| w2.peers[i].doc.contains(x) implies w.peers[i].doc.contains(x) by {
            if !w.peers[i].doc.contains(x) {
                assert(w.peers[1 - i].doc.contains(x));
                assert(gset(w, i).contains(x));
                assert(gset(w2, i).contains(x));
            }
        }
        assert(w2.peers[i].doc =~= w.peers[i].doc);
    }
    assert forall|i: int| 0 <= i < 2 implies w2.peers[i].queue == w.peers[i].queue by {
        assert(xinv_p(d, n, w, i) && xinv_p(d, n, w2, i));
        assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[1 - i].doc == w.peers[1 - i].doc);
        assert(w2.peers[i].queue =~= w.peers[i].queue) by {
            assert forall|x: int| w2.peers[i].queue.contains(x) implies w.peers[i].queue.contains(x) by {
                assert(w2.peers[1 - i].doc.contains(x) && !w2.peers[i].doc.contains(x));
                assert(gset(w, i).contains(x));
                assert(!rset(w2, i).contains(x));
                assert(!rset(w, i).contains(x));
            }
            assert forall|x: int| w.peers[i].queue.contains(x) implies w2.peers[i].queue.contains(x) by {
                assert(w.peers[1 - i].doc.contains(x) && !w.peers[i].doc.contains(x));
                assert(gset(w2, i).contains(x));
                assert(!rset(w, i).contains(x));
                assert(!rset(w2, i).contains(x));
            }
        }
    }
}

proof fn lemma_send_has_need(d: Deps, n: int, s: ISet<int>, have: Seq<Have>, need: ISet<int>, x: int)
    requires need.contains(x), s.contains(x), ensures hashes_to_send(d, n, s, have, need).contains(x),
{}

proof fn lemma_peer_is_fin(d: Deps, n: int, w: World, rp: RP, c: int)
    requires wf(d, n), sinv(d, n, w), rvalid(d, n, w, rp), 0 <= c < 2,
    ensures rw6(d, n, w, rp).peers[c] == fin(d, n, w, rp, c),
{ lemma_round_peers(d, n, w, rp); }

pub open spec fn rnd_pre(d: Deps, n: int, w: World, rp: RP, a: int) -> bool {
    wf(d, n) && 0 <= a < 2 && sinv(d, n, w) && rvalid(d, n, w, rp) && good(rp)
    && !w.peers[1 - a].doc.subset_of(w.peers[a].doc)
}
proof fn lemma_s_flag(d: Deps, n: int, w: World, rp: RP, a: int)
    requires rnd_pre(d, n, w, rp, a), ensures rw6(d, n, w, rp).peers[1 - a].needs_reset == false,
{
    lemma_not_known(d, n, w, a);
    lemma_msg_of(d, n, w, rp, 1 - a);
    lemma_peer_is_fin(d, n, w, rp, 1 - a);
}
proof fn lemma_s_heads(d: Deps, n: int, w: World, rp: RP, a: int)
    requires rnd_pre(d, n, w, rp, a), w.peers[1 - a].needs_reset == false,
    ensures rw6(d, n, w, rp).peers[a].their_heads == Some(heads(d, w.peers[1 - a].doc)),
{
    lemma_not_known(d, n, w, a);
    lemma_msg_of(d, n, w, rp, 1 - a);
    lemma_peer_is_fin(d, n, w, rp, a);
}
proof fn lemma_s_need(d: Deps, n: int, w: World, rp: RP, a: int)
    requires rnd_pre(d, n, w, rp, a), w.peers[a].their_heads == Some(heads(d, w.peers[1 - a].doc)),
    ensures rw6(d, n, w, rp).peers[1 - a].their_need
        == Some(missing(d, n, w.peers[a].doc, w.peers[a].queue, heads(d, w.peers[1 - a].doc))),
        rw6(d, n, w, rp).peers[1 - a].their_have is Some,
{
    let b = 1 - a;
    assert(peer_inv(d, n, w, 0) && peer_inv(d, n, w, 1));
    lemma_heads_ne(d, n, w.peers[a].doc, w.peers[b].doc);
    lemma_msg_of(d, n, w, rp, a);
    lemma_peer_is_fin(d, n, w, rp, b);
}
proof fn lemma_s_send(d: Deps, n: int, w: World, rp: RP, a: int, x: int)
    requires rnd_pre(d, n, w, rp, a), w.peers[1 - a].doc.contains(x), w.peers[1 - a].their_have is Some,
        (match w.peers[1 - a].their_need { Some(nd) => nd.contains(x), None => false }),
    ensures rw6(d, n, w, rp).peers[a].doc.contains(x) || rw6(d, n, w, rp).peers[a].queue.contains(x),
{
    let b = 1 - a;
    lemma_not_known(d, n, w, a);
    lemma_msg_of(d, n, w, rp, b);
    lemma_peer_is_fin(d, n, w, rp, a);
    let pb = w.peers[b];
    let t = tmo(pb);
    match (pb.their_have, pb.their_need) {
        (Some(h), Some(nd)) => {
            lemma_send_has_need(d, n, pb.doc, h, nd, x);
            if !isdoc(rp, b) { assert(send_set(d, n, t).contains(x)); }
        }
        _ => { assert(false); }
    }
}

pub proof fn lemma_window(d: Deps, n: int, w0: World, rp0: RP, rp1: RP, rp2: RP, rp3: RP, a: int)
    requires wf(d, n), 0 <= a < 2, sinv(d, n, w0),
        rvalid(d, n, w0, rp0), good(rp0),
        rvalid(d, n, rw6(d, n, w0, rp0), rp1), good(rp1),
        rvalid(d, n, rw6(d, n, rw6(d, n, w0, rp0), rp1), rp2), good(rp2),
        rvalid(d, n, rw6(d, n, rw6(d, n, rw6(d, n, w0, rp0), rp1), rp2), rp3), good(rp3),
        !w0.peers[1 - a].doc.subset_of(w0.peers[a].doc),
    ensures phi(n, rw6(d, n, rw6(d, n, rw6(d, n, rw6(d, n, w0, rp0), rp1), rp2), rp3)) < phi(n, w0),
{
    let b = 1 - a;
    let w1 = rw6(d, n, w0, rp0); let w2 = rw6(d, n, w1, rp1); let w3 = rw6(d, n, w2, rp2); let w4 = rw6(d, n, w3, rp3);
    lemma_round(d, n, w0, rp0); lemma_round(d, n, w1, rp1); lemma_round(d, n, w2, rp2); lemma_round(d, n, w3, rp3);
    assert(w0.peers.len() == 2 && w1.peers.len() == 2 && w2.peers.len() == 2 && w3.peers.len() == 2 && w4.peers.len() == 2);
    lemma_phi_le(n, w0, w1); lemma_phi_le(n, w1, w2); lemma_phi_le(n, w2, w3); lemma_phi_le(n, w3, w4);
    if phi(n, w4) >= phi(n, w0) {
        lemma_const(d, n, w0, w1); lemma_const(d, n, w1, w2); lemma_const(d, n, w2, w3); lemma_const(d, n, w3, w4);
        let da = w0.peers[a].doc; let db = w0.peers[b].doc; let qa = w0.peers[a].queue;
        assert(w1.peers[a].doc == da && w2.peers[a].doc == da && w3.peers[a].doc == da && w4.peers[a].doc == da);
        assert(w1.peers[b].doc == db && w2.peers[b].doc == db && w3.peers[b].doc == db && w4.peers[b].doc == db);
        assert(w1.peers[a].queue == qa && w2.peers[a].queue == qa && w3.peers[a].queue == qa);
        lemma_s_flag(d, n, w0, rp0, a);
        lemma_s_heads(d, n, w1, rp1, a);
        assert(inv(d, n, w2) && xinv(d, n, w2));
        assert(peer_inv(d, n, w0, 0) && peer_inv(d, n, w0, 1) && inv(d, n, w0));
        assert(peer_inv(d, n, w2, 0) && peer_inv(d, n, w2, 1));
        assert(xinv_p(d, n, w2, a));
        lemma_exists_missing(d, n, da, qa, db);
        let x = choose|x: int| missing(d, n, da, qa, heads(d, db)).contains(x) && db.contains(x) && !da.contains(x) && !qa.contains(x);
        lemma_s_need(d, n, w2, rp2, a);
        lemma_s_send(d, n, w3, rp3, a, x);
        assert(rset(w3, a).contains(x));
        assert(rset(w4, a) == rset(w3, a));
    }
}

// =====================================================================================
// Part 7: rounds are enabled (a drain always exists), so the liveness theorem is not vacuous
// =====================================================================================
pub open spec fn in_drain(d: Deps, s: ISet<int>, pool: ISet<int>, c: int) -> bool decreases (if c < 0 { 0int } else { c + 1 }) {
    if s.contains(c) { true } else if c < 0 || !pool.contains(c) { false } else {
        forall|x: int| #[trigger] d(c).contains(x) ==> (0 <= x && x < c && in_drain(d, s, pool, x))
    }
}
pub open spec fn drain_set(d: Deps, s: ISet<int>, pool: ISet<int>) -> ISet<int> { ISet::new(|c: int| in_drain(d, s, pool, c)) }

pub proof fn lemma_drain_exists(d: Deps, n: int, s: ISet<int>, pool: ISet<int>)
    requires wf(d, n), closed(d, s), bounded(s, n), bounded(pool, n),
    ensures drain_ok(d, s, pool, drain_set(d, s, pool)),
{
    let s2 = drain_set(d, s, pool);
    assert(s.subset_of(s2)) by { assert forall|c: int| s.contains(c) implies s2.contains(c) by { reveal_with_fuel(in_drain, 2); } }
    assert(s2.subset_of(s.union(pool))) by {
        assert forall|c: int| s2.contains(c) implies s.union(pool).contains(c) by { reveal_with_fuel(in_drain, 2); }
    }
    assert(closed(d, s2)) by {
        assert forall|c: int, x: int| s2.contains(c) && #[trigger] d(c).contains(x) implies s2.contains(x) by {
            reveal_with_fuel(in_drain, 2);
            if s.contains(c) { assert(s.contains(x)); }
        }
    }
    assert forall|c: int| pool.contains(c) && !s2.contains(c) implies !(d(c).subset_of(s2)) by {
        reveal_with_fuel(in_drain, 2);
        if d(c).subset_of(s2) {
            assert forall|x: int| #[trigger] d(c).contains(x) implies (0 <= x && x < c && in_drain(d, s, pool, x)) by {
                assert(s2.contains(x));
            }
            assert(in_drain(d, s, pool, c));
        }
    }
}

pub proof fn lemma_round_exists(d: Deps, n: int, w: World)
    requires wf(d, n), sinv(d, n, w),
    ensures exists|rp: RP| rvalid(d, n, w, rp) && good(rp),
{
    assert(inv(d, n, w) && xinv(d, n, w));
    assert(peer_inv(d, n, w, 0) && peer_inv(d, n, w, 1) && xinv_p(d, n, w, 0) && xinv_p(d, n, w, 1));
    let e = ISet::<int>::empty();
    let rp0 = RP { ba: w.peers[0].doc, fa: false, bb: w.peers[1].doc, fb: false, s2a: e, s2b: e, lossa: false, lossb: false, da: false, db: false };
    let w1 = rw1(d, n, w); let w2 = rw2(d, n, w); let w3 = rw3(d, n, w, rp0); let w4 = rw4(d, n, w, rp0);
    assert(w2.peers[0] == tmo(w.peers[0]) && w2.peers[1] == tmo(w.peers[1]) && w2.peers.len() == 2);
    lemma_genx_props(d, n, tmo(w.peers[0]), rp0.ba, rp0.fa, false);
    lemma_genx_props(d, n, tmo(w.peers[1]), rp0.bb, rp0.fb, false);
    lemma_rw4(d, n, w, rp0);
    let ga = tga(d, n, w, rp0); let gb = tgb(d, n, w, rp0);
    assert(w4.peers[0].doc == w.peers[0].doc && w4.peers[0].queue == w.peers[0].queue);
    assert(w4.peers[1].doc == w.peers[1].doc && w4.peers[1].queue == w.peers[1].queue);
    // s2 for B receiving A's message, s2 for A receiving B's message
    let s2b = match ga.1 {
        Some(m) => if m.changes == e { w.peers[1].doc } else { drain_set(d, w.peers[1].doc, w.peers[1].queue.union(m.changes)) },
        None => e };
    let s2a = match gb.1 {
        Some(m) => if m.changes == e { w.peers[0].doc } else { drain_set(d, w.peers[0].doc, w.peers[0].queue.union(m.changes)) },
        None => e };
    let rp = RP { s2a: s2a, s2b: s2b, ..rp0 };
    assert(rw3(d, n, w, rp) == w3 && rw4(d, n, w, rp) == w4);
    assert(msg_a(d, n, w, rp) == ga.1 && msg_b(d, n, w, rp) == gb.1);
    // recv guard facts
    match ga.1 {
        Some(m) => {
            assert(w4.net[0].contains(m)) by { assert(w4.net[0] == w3.net[0]); assert(w3.net[0] == w2.net[0].insert(m)); }
            let p = w.peers[1];
            assert(bounded(p.queue.union(m.changes), n)) by {
                assert forall|x: int| p.queue.union(m.changes).contains(x) implies 0 <= x && x < n by {
                    if !p.queue.contains(x) { assert(m.changes.subset_of(w.peers[0].doc)); assert(w.peers[0].doc.contains(x)); }
                }
            }
            if m.changes == e {
                assert(drain_ok(d, p.doc, p.queue.union(m.changes), p.doc)) by {
                    assert(p.queue.union(e) =~= p.queue);
                    assert forall|c: int| p.queue.contains(c) && !p.doc.contains(c) implies !(d(c).subset_of(p.doc)) by {}
                }
            } else { lemma_drain_exists(d, n, p.doc, p.queue.union(m.changes)); }
        }
        None => {}
    }
    let w5 = rw5(d, n, w, rp);
    match gb.1 {
        Some(m) => {
            let p = w.peers[0];
            match ga.1 {
                Some(m0) => { assert(w5.net[1] == w4.net[1]); }
                None => {}
            }
            assert(w4.net[1].contains(m)) by { assert(w4.net[1] == w3.net[1].insert(m)); }
            assert(w5.net[1].contains(m));
            assert(w5.peers.len() == 2);
            assert(w5.peers[0] == w4.peers[0]);
            assert(bounded(p.queue.union(m.changes), n)) by {
                assert forall|x: int| p.queue.union(m.changes).contains(x) implies 0 <= x && x < n by {
                    if !p.queue.contains(x) { assert(m.changes.subset_of(w.peers[1].doc)); assert(w.peers[1].doc.contains(x)); }
                }
            }
            if m.changes == e {
                assert(drain_ok(d, p.doc, p.queue.union(m.changes), p.doc)) by {
                    assert(p.queue.union(e) =~= p.queue);
                    assert forall|c: int| p.queue.contains(c) && !p.doc.contains(c) implies !(d(c).subset_of(p.doc)) by {}
                }
            } else { lemma_drain_exists(d, n, p.doc, p.queue.union(m.changes)); }
        }
        None => {}
    }
    assert(rvalid(d, n, w, rp) && good(rp));
}

// =====================================================================================
// Part 8: LIVENESS under fair-lossy rounds
//   A run is an infinite sequence of rounds starting from any reachable world (after the last local edit).
//   Fair-lossy (our formalization): for every m there are 4 consecutive loss-free rounds at some k >= m.
//   Conclusion: from some round on, the two docs are identical (and stay so).
// =====================================================================================
pub open spec fn run_ok(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP) -> bool {
    forall|k: nat| #![trigger rps(k)] rvalid(d, n, ws(k), rps(k)) && ws((k + 1) as nat) == rw6(d, n, ws(k), rps(k))
}
pub open spec fn win4(rps: spec_fn(nat) -> RP, m: nat) -> bool {
    exists|k: nat| #![trigger rps(k)] k >= m && good(rps(k)) && good(rps((k + 1) as nat))
        && good(rps((k + 2) as nat)) && good(rps((k + 3) as nat))
}
pub open spec fn fair_lossy(rps: spec_fn(nat) -> RP) -> bool { forall|m: nat| #[trigger] win4(rps, m) }

proof fn lemma_run_at(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP, k: nat)
    requires run_ok(d, n, ws, rps),
    ensures rvalid(d, n, ws(k), rps(k)), ws((k + 1) as nat) == rw6(d, n, ws(k), rps(k)),
{}
proof fn lemma_run_sinv(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP, k: nat)
    requires wf(d, n), sinv(d, n, ws(0)), run_ok(d, n, ws, rps), ensures sinv(d, n, ws(k)), decreases k,
{
    if k > 0 {
        lemma_run_sinv(d, n, ws, rps, (k - 1) as nat);
        lemma_run_at(d, n, ws, rps, (k - 1) as nat);
        lemma_round(d, n, ws((k - 1) as nat), rps((k - 1) as nat));
    }
}
proof fn lemma_run_mono(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP, i: nat, j: nat)
    requires wf(d, n), n >= 0, sinv(d, n, ws(0)), run_ok(d, n, ws, rps), i <= j,
    ensures phi(n, ws(j)) <= phi(n, ws(i)), decreases j - i,
{
    if i < j {
        lemma_run_mono(d, n, ws, rps, i, (j - 1) as nat);
        lemma_run_sinv(d, n, ws, rps, (j - 1) as nat);
        lemma_run_at(d, n, ws, rps, (j - 1) as nat);
        lemma_round(d, n, ws((j - 1) as nat), rps((j - 1) as nat));
        lemma_phi_le(n, ws((j - 1) as nat), ws(j));
    }
}
proof fn cnt_pos(s: ISet<int>, k: nat)
    requires cnt(s, k) > 0, ensures exists|c: int| 0 <= c < k && s.contains(c), decreases k,
{ if k > 0 { if cnt(s, (k - 1) as nat) > 0 { cnt_pos(s, (k - 1) as nat); } } }

// phi == 0 means identical docs
proof fn lemma_phi_zero(d: Deps, n: int, w: World)
    requires wf(d, n), sinv(d, n, w), phi(n, w) == 0, ensures w.peers[0].doc == w.peers[1].doc,
{
    assert(inv(d, n, w));
    assert(peer_inv(d, n, w, 0) && peer_inv(d, n, w, 1));
    assert(cnt(gset(w, 0), n as nat) == 0 && cnt(gset(w, 1), n as nat) == 0);
    assert forall|x: int| w.peers[1].doc.contains(x) implies w.peers[0].doc.contains(x) by {
        if !w.peers[0].doc.contains(x) { assert(gset(w, 0).contains(x)); cnt_mono(ISet::<int>::empty().insert(x), gset(w, 0), n as nat); lemma_cnt_single(x, n as nat); }
    }
    assert forall|x: int| w.peers[0].doc.contains(x) implies w.peers[1].doc.contains(x) by {
        if !w.peers[1].doc.contains(x) { assert(gset(w, 1).contains(x)); cnt_mono(ISet::<int>::empty().insert(x), gset(w, 1), n as nat); lemma_cnt_single(x, n as nat); }
    }
    assert(w.peers[0].doc =~= w.peers[1].doc);
}
proof fn lemma_cnt_single(x: int, k: nat)
    requires 0 <= x < k, ensures cnt(ISet::<int>::empty().insert(x), k) == 1, decreases k,
{
    let s = ISet::<int>::empty().insert(x);
    if k > 0 {
        if x < k - 1 { lemma_cnt_single(x, (k - 1) as nat); assert(!s.contains((k - 1) as int)); }
        else { lemma_cnt_zero_below(x, (k - 1) as nat); assert(s.contains((k - 1) as int)); }
    }
}
proof fn lemma_cnt_zero_below(x: int, k: nat)
    requires k <= x, ensures cnt(ISet::<int>::empty().insert(x), k) == 0, decreases k,
{ if k > 0 { lemma_cnt_zero_below(x, (k - 1) as nat); } }

proof fn lemma_live_from(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP, v: nat, m: nat)
    requires wf(d, n), n >= 0, sinv(d, n, ws(0)), run_ok(d, n, ws, rps), fair_lossy(rps), phi(n, ws(m)) <= v,
    ensures exists|K: nat| #![trigger ws(K)] K >= m && ws(K).peers[0].doc == ws(K).peers[1].doc,
    decreases v,
{
    assert(win4(rps, m));
    let k = choose|k: nat| #![trigger rps(k)] k >= m && good(rps(k)) && good(rps((k + 1) as nat)) && good(rps((k + 2) as nat)) && good(rps((k + 3) as nat));
    lemma_run_mono(d, n, ws, rps, m, k);
    lemma_run_sinv(d, n, ws, rps, k);
    if phi(n, ws(k)) == 0 {
        lemma_phi_zero(d, n, ws(k));
    } else {
        let w0 = ws(k);
        assert(phi(n, w0) > 0);
        // some direction has a gap
        let a = if cnt(gset(w0, 0), n as nat) > 0 { 0int } else { 1int };
        if cnt(gset(w0, 0), n as nat) == 0 && cnt(gset(w0, 1), n as nat) == 0 {
            // R sets are subsets of G sets, so their counts are 0 too
            cnt_mono(rset(w0, 0), gset(w0, 0), n as nat); cnt_mono(rset(w0, 1), gset(w0, 1), n as nat);
            assert(false);
        }
        assert(cnt(gset(w0, a), n as nat) > 0);
        cnt_pos(gset(w0, a), n as nat);
        assert(!w0.peers[1 - a].doc.subset_of(w0.peers[a].doc));
        lemma_run_at(d, n, ws, rps, k);
        lemma_run_at(d, n, ws, rps, (k + 1) as nat);
        lemma_run_at(d, n, ws, rps, (k + 2) as nat);
        lemma_run_at(d, n, ws, rps, (k + 3) as nat);
        lemma_window(d, n, w0, rps(k), rps((k + 1) as nat), rps((k + 2) as nat), rps((k + 3) as nat), a);
        lemma_live_from(d, n, ws, rps, (v - 1) as nat, (k + 4) as nat);
    }
}

// THEOREM (liveness): any fair-lossy run from a world satisfying sinv reaches identical docs.
pub proof fn theorem_liveness(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP)
    requires wf(d, n), sinv(d, n, ws(0)), run_ok(d, n, ws, rps), fair_lossy(rps),
    ensures exists|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc,
{
    lemma_live_from(d, n, ws, rps, phi(n, ws(0)), 0);
}

// docs stay identical once identical (so "eventually equal" is "eventually always equal")
pub proof fn theorem_stays_equal(d: Deps, n: int, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP, i: nat, j: nat)
    requires wf(d, n), sinv(d, n, ws(0)), run_ok(d, n, ws, rps), i <= j, ws(i).peers[0].doc == ws(i).peers[1].doc,
    ensures ws(j).peers[0].doc == ws(j).peers[1].doc, decreases j - i,
{
    if i < j {
        theorem_stays_equal(d, n, ws, rps, i, (j - 1) as nat);
        let w = ws((j - 1) as nat);
        lemma_run_sinv(d, n, ws, rps, (j - 1) as nat);
        lemma_run_at(d, n, ws, rps, (j - 1) as nat);
        lemma_round(d, n, w, rps((j - 1) as nat));
        let w2 = ws(j);
        assert(rel(w, w2));
        assert(rel_i(w, w2, 0) && rel_i(w, w2, 1));
        assert(w.peers[0].doc.union(w.peers[1].doc) =~= w.peers[0].doc);
        assert(w2.peers[0].doc =~= w2.peers[1].doc) by {
            assert forall|x: int| w2.peers[0].doc.contains(x) implies w2.peers[1].doc.contains(x) by {
                assert(w.peers[0].doc.union(w.peers[1].doc).contains(x));
                assert(w.peers[1].doc.contains(x));
            }
            assert forall|x: int| w2.peers[1].doc.contains(x) implies w2.peers[0].doc.contains(x) by {
                assert(w.peers[1].doc.union(w.peers[0].doc).contains(x));
                assert(w.peers[0].doc.contains(x));
            }
        }
    }
}

// Every round is a sequence of model steps (so a run of rounds is an execution of the model).
pub proof fn lemma_round_is_model_steps(d: Deps, n: int, w: World, rp: RP)
    requires rvalid(d, n, w, rp),
    ensures
        next(d, n, w, Step::Timeout { who: 0 }, rw1(d, n, w)),
        next(d, n, rw1(d, n, w), Step::Timeout { who: 1 }, rw2(d, n, w)),
        next(d, n, rw2(d, n, w), gstep(0, rp.ba, rp.fa, rp.da), rw3(d, n, w, rp)),
        next(d, n, rw3(d, n, w, rp), gstep(1, rp.bb, rp.fb, rp.db), rw4(d, n, w, rp)),
        (match msg_a(d, n, w, rp) { Some(m) => next(d, n, rw4(d, n, w, rp), st5(rp, m), rw5(d, n, w, rp)), None => true }),
        (match msg_b(d, n, w, rp) { Some(m) => next(d, n, rw5(d, n, w, rp), st6(rp, m), rw6(d, n, w, rp)), None => true }),
{}

// Liveness from any world reachable by the fixed model (including worlds stuck under the original protocol).
pub proof fn theorem_liveness_reachable(d: Deps, n: int, w: World, k: nat, ws: spec_fn(nat) -> World, rps: spec_fn(nat) -> RP)
    requires wf(d, n), reachable(d, n, w, k), ws(0) == w, run_ok(d, n, ws, rps), fair_lossy(rps),
    ensures exists|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc,
{
    theorem_sinv_reachable(d, n, w, k);
    theorem_liveness(d, n, ws, rps);
}

// =====================================================================================
// Part 9: executable refinement of the patch.  EState mirrors the fields of sync::State that the model uses
// (types simplified: hashes are u64, sets are Vec).  on_timeout is the body of the proposed State::on_timeout.
// =====================================================================================
pub struct EHave { pub last_sync: Vec<u64>, pub bloom: Vec<u64> }
pub struct EState {
    pub shared_heads: Vec<u64>, pub last_sent_heads: Vec<u64>,
    pub their_heads: Option<Vec<u64>>, pub their_need: Option<Vec<u64>>, pub their_have: Option<Vec<EHave>>,
    pub sent_hashes: Vec<u64>, pub in_flight: bool, pub have_responded: bool, pub needs_reset: bool,
}
pub open spec fn vset(v: Seq<u64>) -> ISet<int> { ISet::new(|x: int| exists|i: int| 0 <= i < v.len() && v[i] as int == x) }
pub open spec fn abs_have(h: EHave) -> Have { Have { last_sync: vset(h.last_sync@), bloom: vset(h.bloom@) } }
pub open spec fn abs_opt(o: Option<Vec<u64>>) -> Option<ISet<int>> { match o { Some(v) => Some(vset(v@)), None => None } }
// abstraction: the doc and the change queue live in the Automerge document, not in State
pub open spec fn abs(s: EState, doc: ISet<int>, queue: ISet<int>) -> Peer {
    Peer {
        doc: doc, queue: queue, shared_heads: vset(s.shared_heads@), last_sent_heads: vset(s.last_sent_heads@),
        their_heads: abs_opt(s.their_heads), their_need: abs_opt(s.their_need),
        their_have: match s.their_have { Some(v) => Some(Seq::new(v@.len(), |i: int| abs_have(v@[i]))), None => None },
        sent_hashes: vset(s.sent_hashes@), in_flight: s.in_flight, have_responded: s.have_responded, needs_reset: s.needs_reset,
    }
}
impl EState {
    // proposed:  pub fn on_timeout(&mut self) { self.sent_hashes.clear(); self.in_flight = false; }
    pub fn on_timeout(&mut self)
        ensures
            forall|doc: ISet<int>, queue: ISet<int>| abs(*final(self), doc, queue) == tmo(abs(*old(self), doc, queue)),
            final(self).shared_heads == old(self).shared_heads, final(self).last_sent_heads == old(self).last_sent_heads,
            final(self).their_heads == old(self).their_heads, final(self).their_need == old(self).their_need,
            final(self).their_have == old(self).their_have, final(self).have_responded == old(self).have_responded,
            final(self).needs_reset == old(self).needs_reset,
            final(self).sent_hashes@.len() == 0, final(self).in_flight == false,
    {
        self.sent_hashes.clear();
        self.in_flight = false;
        proof {
            assert forall|doc: ISet<int>, queue: ISet<int>| abs(*final(self), doc, queue) == tmo(abs(*old(self), doc, queue)) by {
                assert(vset(self.sent_hashes@) =~= ISet::<int>::empty());
            }
        }
    }
}



// =====================================================================================
// Part 10 (vlm45_amproof): general runs.  A block is either a lock-step round (as above) or ONE arbitrary
// model step other than Edit: deliver any pending (stale, reordered) message, deliver-and-keep (duplicate),
// Drop, Gen, Timeout, SetReset, by either peer, in any order.  Fairness: infinitely often, 4 consecutive
// blocks are loss-free rounds.  Conclusion: docs become identical and stay identical.
// =====================================================================================
pub open spec fn blk_ok(d: Deps, n: int, w: World, isr: bool, rp: RP, st: Step, w2: World) -> bool {
    if isr { rvalid(d, n, w, rp) && w2 == rw6(d, n, w, rp) } else { next(d, n, w, st, w2) && passive_step(st) }
}
pub open spec fn grun_ok(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step) -> bool {
    forall|k: nat| #![trigger rps(k)] blk_ok(d, n, ws(k), isr(k), rps(k), sts(k), ws((k + 1) as nat))
}
pub open spec fn gr(isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, k: nat) -> bool { isr(k) && good(rps(k)) }
pub open spec fn gwin4(isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, m: nat) -> bool {
    exists|k: nat| #![trigger rps(k)] k >= m && gr(isr, rps, k) && gr(isr, rps, (k + 1) as nat)
        && gr(isr, rps, (k + 2) as nat) && gr(isr, rps, (k + 3) as nat)
}
pub open spec fn gfair(isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP) -> bool { forall|m: nat| #[trigger] gwin4(isr, rps, m) }

proof fn lemma_grun_at(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step, k: nat)
    requires grun_ok(d, n, ws, isr, rps, sts),
    ensures blk_ok(d, n, ws(k), isr(k), rps(k), sts(k), ws((k + 1) as nat)),
{ let _ = rps(k); }
proof fn lemma_blk(d: Deps, n: int, w: World, isr: bool, rp: RP, st: Step, w2: World)
    requires wf(d, n), sinv(d, n, w), blk_ok(d, n, w, isr, rp, st, w2),
    ensures sinv(d, n, w2), rel(w, w2),
{
    if isr { lemma_round(d, n, w, rp); } else { lemma_one(d, n, w, st, w2); }
}
proof fn lemma_grun_sinv(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step, k: nat)
    requires wf(d, n), sinv(d, n, ws(0)), grun_ok(d, n, ws, isr, rps, sts), ensures sinv(d, n, ws(k)), decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        lemma_grun_sinv(d, n, ws, isr, rps, sts, j);
        lemma_grun_at(d, n, ws, isr, rps, sts, j);
        lemma_blk(d, n, ws(j), isr(j), rps(j), sts(j), ws(k));
    }
}
proof fn lemma_grun_rel(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step, i: nat, j: nat)
    requires wf(d, n), sinv(d, n, ws(0)), grun_ok(d, n, ws, isr, rps, sts), i <= j,
    ensures rel(ws(i), ws(j)), ws(i).peers.len() == 2, ws(j).peers.len() == 2, decreases j - i,
{
    lemma_grun_sinv(d, n, ws, isr, rps, sts, i);
    lemma_grun_sinv(d, n, ws, isr, rps, sts, j);
    assert(inv(d, n, ws(i)) && inv(d, n, ws(j)));
    if i < j {
        let p = (j - 1) as nat;
        lemma_grun_rel(d, n, ws, isr, rps, sts, i, p);
        lemma_grun_sinv(d, n, ws, isr, rps, sts, p);
        lemma_grun_at(d, n, ws, isr, rps, sts, p);
        lemma_blk(d, n, ws(p), isr(p), rps(p), sts(p), ws(j));
        lemma_rel_trans(ws(i), ws(p), ws(j));
    } else { lemma_rel_refl(ws(i)); }
}
proof fn lemma_glive_from(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step, v: nat, m: nat)
    requires wf(d, n), n >= 0, sinv(d, n, ws(0)), grun_ok(d, n, ws, isr, rps, sts), gfair(isr, rps), phi(n, ws(m)) <= v,
    ensures exists|K: nat| #![trigger ws(K)] K >= m && ws(K).peers[0].doc == ws(K).peers[1].doc,
    decreases v,
{
    assert(gwin4(isr, rps, m));
    let k = choose|k: nat| #![trigger rps(k)] k >= m && gr(isr, rps, k) && gr(isr, rps, (k + 1) as nat) && gr(isr, rps, (k + 2) as nat) && gr(isr, rps, (k + 3) as nat);
    lemma_grun_rel(d, n, ws, isr, rps, sts, m, k);
    lemma_phi_le(n, ws(m), ws(k));
    lemma_grun_sinv(d, n, ws, isr, rps, sts, k);
    if phi(n, ws(k)) == 0 {
        lemma_phi_zero(d, n, ws(k));
    } else {
        let w0 = ws(k);
        let a = if cnt(gset(w0, 0), n as nat) > 0 { 0int } else { 1int };
        if cnt(gset(w0, 0), n as nat) == 0 && cnt(gset(w0, 1), n as nat) == 0 {
            cnt_mono(rset(w0, 0), gset(w0, 0), n as nat); cnt_mono(rset(w0, 1), gset(w0, 1), n as nat);
            assert(false);
        }
        cnt_pos(gset(w0, a), n as nat);
        assert(!w0.peers[1 - a].doc.subset_of(w0.peers[a].doc));
        lemma_grun_at(d, n, ws, isr, rps, sts, k);
        lemma_grun_at(d, n, ws, isr, rps, sts, (k + 1) as nat);
        lemma_grun_at(d, n, ws, isr, rps, sts, (k + 2) as nat);
        lemma_grun_at(d, n, ws, isr, rps, sts, (k + 3) as nat);
        lemma_window(d, n, w0, rps(k), rps((k + 1) as nat), rps((k + 2) as nat), rps((k + 3) as nat), a);
        lemma_glive_from(d, n, ws, isr, rps, sts, (v - 1) as nat, (k + 4) as nat);
    }
}
// THEOREM (general liveness)
pub proof fn theorem_gliveness(d: Deps, n: int, w: World, k0: nat, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step)
    requires wf(d, n), reachable(d, n, w, k0), ws(0) == w, grun_ok(d, n, ws, isr, rps, sts), gfair(isr, rps),
    ensures exists|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc,
{
    theorem_sinv_reachable(d, n, w, k0);
    lemma_glive_from(d, n, ws, isr, rps, sts, phi(n, ws(0)), 0);
}
// THEOREM (general stability): once equal, docs stay equal under any blocks.
pub proof fn theorem_gstays_equal(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step, i: nat, j: nat)
    requires wf(d, n), sinv(d, n, ws(0)), grun_ok(d, n, ws, isr, rps, sts), i <= j, ws(i).peers[0].doc == ws(i).peers[1].doc,
    ensures ws(j).peers[0].doc == ws(j).peers[1].doc,
{
    lemma_grun_rel(d, n, ws, isr, rps, sts, i, j);
    let w = ws(i); let w2 = ws(j);
    assert(rel_i(w, w2, 0) && rel_i(w, w2, 1));
    assert(w2.peers[0].doc =~= w2.peers[1].doc) by {
        assert forall|x: int| w2.peers[0].doc.contains(x) implies w2.peers[1].doc.contains(x) by {
            assert(w.peers[0].doc.union(w.peers[1].doc).contains(x)); assert(w.peers[1].doc.contains(x));
        }
        assert forall|x: int| w2.peers[1].doc.contains(x) implies w2.peers[0].doc.contains(x) by {
            assert(w.peers[1].doc.union(w.peers[0].doc).contains(x)); assert(w.peers[0].doc.contains(x));
        }
    }
}
// Not vacuous: a stale delivery between rounds is a legal block (any guard-satisfying non-Edit step is).
pub proof fn lemma_block_exists(d: Deps, n: int, w: World, st: Step)
    requires guard(d, n, w, st), passive_step(st),
    ensures blk_ok(d, n, w, false, arbitrary(), st, apply(d, n, w, st)),
{}

// =====================================================================================
// Part 11 (vlm47_amcode#7, sched): the general liveness theorem from any `sinv` world (not only model-reachable ones),
// so that code runs, whose start is given by `sinv`, can use it.  Additive; uses the private lemma above.
// =====================================================================================
pub proof fn theorem_gliveness_sinv(d: Deps, n: int, ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step)
    requires wf(d, n), sinv(d, n, ws(0)), grun_ok(d, n, ws, isr, rps, sts), gfair(isr, rps),
    ensures exists|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc,
{
    lemma_glive_from(d, n, ws, isr, rps, sts, phi(n, ws(0)), 0);
}

// =====================================================================================
// Part 12 (vlm47_amcode#7, sched): a COUNTEREXAMPLE LASSO to liveness under per-action fairness without lock-step.
// Deps: none (n = 1, one change 0).  Peer A (index 0) has change 0; peer B (index 1) has nothing.
// Schedule: finite prefix (Edit, then 7 steps) and then a 7-step cycle forever.  The cycle contains, with no Drop:
// Timeout of each peer, Gen of each peer, and a (keep = true) Recv of EVERY message in the network.
// Yet B never gets change 0: in every cycle A's last Recv is the STALE message R0 (B's first message, whose
// Bloom filter claims "B has 0", a false positive the model allows), so A believes B needs nothing.
// =====================================================================================
pub open spec fn dz() -> Deps { |c: int| ISet::<int>::empty() }
pub open spec fn zs() -> ISet<int> { ISet::<int>::empty() }
pub open spec fn os() -> ISet<int> { ISet::<int>::empty().insert(0int) }
pub open spec fn hv0() -> Have { Have { last_sync: zs(), bloom: zs() } }
pub open spec fn hv1() -> Have { Have { last_sync: zs(), bloom: os() } }
pub open spec fn m_a() -> Msg { Msg { heads: os(), need: zs(), have: seq![hv1()], changes: zs() } }
pub open spec fn m_r0() -> Msg { Msg { heads: zs(), need: zs(), have: seq![hv1()], changes: zs() } }
pub open spec fn m_r1() -> Msg { Msg { heads: zs(), need: os(), have: seq![hv0()], changes: zs() } }
pub open spec fn mk(doc: ISet<int>, lsh: ISet<int>, th: Option<ISet<int>>, thave: Option<Seq<Have>>, tneed: Option<ISet<int>>, infl: bool, resp: bool) -> Peer {
    Peer { doc: doc, queue: zs(), shared_heads: zs(), last_sent_heads: lsh, their_heads: th, their_have: thave, their_need: tneed,
           sent_hashes: zs(), in_flight: infl, have_responded: resp, needs_reset: false }
}
pub open spec fn net0() -> Seq<ISet<Msg>> {
    seq![ISet::<Msg>::empty().insert(m_a()), ISet::<Msg>::empty().insert(m_r0()).insert(m_r1())]
}
pub open spec fn pa_init() -> Peer { Peer { doc: os(), ..init_peer() } }
pub open spec fn pa2() -> Peer { mk(os(), os(), Some(zs()), Some(seq![hv1()]), Some(zs()), true, true) }
pub open spec fn pa4() -> Peer { mk(os(), zs(), Some(zs()), Some(seq![hv0()]), Some(os()), false, true) }
pub open spec fn pa0() -> Peer { mk(os(), zs(), Some(zs()), Some(seq![hv1()]), Some(zs()), false, true) }
pub open spec fn pb0() -> Peer { mk(zs(), zs(), Some(os()), Some(seq![hv1()]), Some(zs()), false, true) }
pub open spec fn pb3() -> Peer { mk(zs(), zs(), Some(os()), Some(seq![hv1()]), Some(zs()), true, true) }
pub open spec fn w2(a: Peer, b: Peer, na: ISet<Msg>, nb: ISet<Msg>) -> World { World { peers: seq![a, b], net: seq![na, nb] } }
pub open spec fn nmt() -> ISet<Msg> { ISet::<Msg>::empty() }
// prefix worlds 0..7
pub open spec fn pw(k: nat) -> World {
    if k == 0 { w2(init_peer(), init_peer(), nmt(), nmt()) }
    else if k == 1 { w2(pa_init(), init_peer(), nmt(), nmt()) }
    else if k == 2 { w2(pa_init(), mk(zs(), zs(), None, Some(Seq::empty()), None, true, true), nmt(), nmt().insert(m_r0())) }
    else if k == 3 { w2(mk(os(), os(), None, Some(Seq::empty()), None, true, true), mk(zs(), zs(), None, Some(Seq::empty()), None, true, true), nmt().insert(m_a()), nmt().insert(m_r0())) }
    else if k == 4 { w2(mk(os(), os(), None, Some(Seq::empty()), None, true, true), mk(zs(), zs(), Some(os()), Some(seq![hv1()]), Some(zs()), false, true), nmt().insert(m_a()), nmt().insert(m_r0())) }
    else if k == 5 { w2(mk(os(), os(), None, Some(Seq::empty()), None, true, true), pb3(), nmt().insert(m_a()), nmt().insert(m_r0()).insert(m_r1())) }
    else if k == 6 { w2(pa4(), pb3(), nmt().insert(m_a()), nmt().insert(m_r0()).insert(m_r1())) }
    else { w2(pa0(), pb3(), nmt().insert(m_a()), nmt().insert(m_r0()).insert(m_r1())) }
}
pub open spec fn pst(k: nat) -> Step {
    if k == 0 { Step::Edit { who: 0, c: 0 } }
    else if k == 1 { Step::Gen { who: 1, bloom: os(), fake: false } }
    else if k == 2 { Step::Gen { who: 0, bloom: os(), fake: false } }
    else if k == 3 { Step::Recv { who: 1, m: m_a(), s2: zs(), keep: true } }
    else if k == 4 { Step::Gen { who: 1, bloom: zs(), fake: false } }
    else if k == 5 { Step::Recv { who: 0, m: m_r1(), s2: os(), keep: true } }
    else if k == 6 { Step::Recv { who: 0, m: m_r0(), s2: os(), keep: true } }
    else { Step::Timeout { who: 1 } }
}
// cycle worlds j = 0..6 (world before cycle step j)
pub open spec fn cw(j: nat) -> World {
    if j == 0 { w2(pa0(), pb0(), net0()[0], net0()[1]) }
    else if j == 1 || j == 2 { w2(pa2(), pb0(), net0()[0], net0()[1]) }
    else if j == 3 { w2(pa2(), pb3(), net0()[0], net0()[1]) }
    else if j == 4 { w2(pa4(), pb3(), net0()[0], net0()[1]) }
    else { w2(pa0(), pb3(), net0()[0], net0()[1]) }
}
pub open spec fn cst(j: nat) -> Step {
    if j == 0 { Step::Gen { who: 0, bloom: os(), fake: false } }
    else if j == 1 { Step::Recv { who: 1, m: m_a(), s2: zs(), keep: true } }
    else if j == 2 { Step::Gen { who: 1, bloom: zs(), fake: false } }
    else if j == 3 { Step::Recv { who: 0, m: m_r1(), s2: os(), keep: true } }
    else if j == 4 { Step::Recv { who: 0, m: m_r0(), s2: os(), keep: true } }
    else if j == 5 { Step::Timeout { who: 0 } }
    else { Step::Timeout { who: 1 } }
}
pub open spec fn lw(k: nat) -> World { if k < 8 { pw(k) } else { cw(((k - 8) % 7) as nat) } }
pub open spec fn lst(k: nat) -> Step { if k < 8 { pst(k) } else { cst(((k - 8) % 7) as nat) } }

// --- facts about the empty dependency function ---
proof fn dz_heads(s: ISet<int>) ensures heads(dz(), s) =~= s {}
proof fn dz_closure(h: ISet<int>) ensures closure(dz(), 1, h) =~= h {
    reveal_with_fuel(reach, 2);
}
proof fn dz_missing(s: ISet<int>, q: ISet<int>, st: ISet<int>) ensures missing(dz(), 1, s, q, st) =~= st.difference(s).difference(q) {
    reveal_with_fuel(walk, 2);
}
proof fn dz_wf() ensures wf(dz(), 1) {}

proof fn peer_ext(p: Peer, q: Peer)
    requires p.doc == q.doc, p.queue == q.queue, p.shared_heads == q.shared_heads, p.last_sent_heads == q.last_sent_heads,
        p.their_heads == q.their_heads, p.their_have == q.their_have, p.their_need == q.their_need, p.sent_hashes == q.sent_hashes,
        p.in_flight == q.in_flight, p.have_responded == q.have_responded, p.needs_reset == q.needs_reset,
    ensures p == q {}
// no-op sets
proof fn ins_same(s: ISet<Msg>, m: Msg) requires s.contains(m), ensures s.insert(m) == s { assert(s.insert(m) =~= s); }
proof fn net0_has() ensures net0()[0].contains(m_a()), net0()[1].contains(m_r0()), net0()[1].contains(m_r1()) {}

// A (doc {0}) facing a Have whose Bloom contains 0 and empty need sends nothing.
proof fn lemma_hts_zero(p: Peer)
    requires p.doc == os(), p.their_have == Some(seq![hv1()]), p.their_need == Some(zs()), p.sent_hashes == zs(),
    ensures send_set(dz(), 1, p) =~= zs(),
{
    let have = seq![hv1()];
    assert(have.len() == 1 && have[0] == hv1());
    assert(all_last_sync(have) =~= zs()) by {
        assert forall|x: int| !all_last_sync(have).contains(x) by {
            if all_last_sync(have).contains(x) {
                let i = choose|i: int| 0 <= i < 1 && #[trigger] have[i].last_sync.contains(x);
                assert(have[i] == hv1());
            }
        }
    }
    dz_closure(all_last_sync(have));
    let need2 = zs().intersect(p.doc);
    assert(need2 =~= zs());
    let hs = p.doc.difference(closure(dz(), 1, all_last_sync(have)));
    let miss = ISet::new(|h: int| hs.contains(h) && forall|i: int| 0 <= i < have.len() ==> !(#[trigger] have[i].bloom.contains(h)));
    assert(miss =~= zs()) by {
        assert forall|h: int| !miss.contains(h) by {
            if miss.contains(h) { assert(hs.contains(h)); assert(h == 0); assert(have[0].bloom.contains(h)); }
        }
    }
    let sent = ISet::new(|h: int| hs.contains(h) && exists|m: int| miss.contains(m) && closure(dz(), 1, ISet::empty().insert(h)).contains(m));
    assert(sent =~= zs());
    assert(hashes_to_send(dz(), 1, p.doc, have, zs()) =~= zs());
    assert(send_set(dz(), 1, p) =~= zs());
}

// A generates in the cycle: A0 -> A2 and the message m_a (already in the net)
proof fn c0() ensures next(dz(), 1, cw(0), cst(0), cw(1)) {
    dz_wf();
    let p = pa0();
    let o = os();
    dz_heads(p.doc); dz_closure(p.shared_heads);
    dz_missing(p.doc, p.queue, opt_set(p.their_heads));
    let need = missing(dz(), 1, p.doc, p.queue, opt_set(p.their_heads));
    assert(need =~= zs());
    assert(all_last_sync(seq![hv1()]) =~= zs()) by {
        assert forall|x: int| !all_last_sync(seq![hv1()]).contains(x) by {
            if all_last_sync(seq![hv1()]).contains(x) {
                let i = choose|i: int| 0 <= i < 1 && #[trigger] seq![hv1()][i].last_sync.contains(x);
                assert(seq![hv1()][i] == hv1());
            }
        }
    }
    dz_closure(all_last_sync(seq![hv1()]));
    let hs = p.doc.difference(closure(dz(), 1, all_last_sync(seq![hv1()])));
    assert(hs =~= o);
    lemma_hts_zero(p);
    assert(send_set(dz(), 1, p) =~= zs());
    assert(guard(dz(), 1, cw(0), cst(0)));
    let r = gen(dz(), 1, p, o, false);
    assert(os().contains(0int) && !zs().contains(0int));
    assert(heads(dz(), p.doc) == os());
    assert(!must_reset(p)) by { assert(seq![hv1()][0] == hv1()); assert(zs().subset_of(p.doc)); }
    assert(zs().union(zs()) =~= zs());
    assert(need == zs());
    assert(zs().subset_of(opt_set(p.their_heads)));
    assert(r.1 == Some(m_a()));
    assert(r.0 == pa2()) by { peer_ext(r.0, pa2()); }
    ins_same(net0()[0], m_a());
    assert(apply(dz(), 1, cw(0), cst(0)) == cw(1)) by { assert(apply(dz(), 1, cw(0), cst(0)).net =~= cw(1).net); assert(apply(dz(), 1, cw(0), cst(0)).peers =~= cw(1).peers); }
}

proof fn world_ext(w: World, w2: World)
    requires w.peers.len() == 2, w2.peers.len() == 2, w.net.len() == 2, w2.net.len() == 2,
        w.peers[0] == w2.peers[0], w.peers[1] == w2.peers[1], w.net[0] == w2.net[0], w.net[1] == w2.net[1],
    ensures w == w2
{ assert(w.peers =~= w2.peers); assert(w.net =~= w2.net); }
proof fn ins_ex(s: ISet<Msg>, m: Msg, t: ISet<Msg>) requires s.contains(m), t =~= s, ensures s.insert(m) == t { assert(s.insert(m) =~= t); }

// ---- generic peer-level facts ----
// B (doc {}, knows nothing of 0) receives A's message m_a
proof fn lemma_recv_b(p: Peer)
    requires p.doc == zs(), p.queue == zs(), p.shared_heads == zs(), p.last_sent_heads == zs(), p.sent_hashes == zs(),
    ensures recv(dz(), 1, p, m_a(), zs()) == (Peer { in_flight: false, their_heads: Some(os()), their_have: Some(seq![hv1()]), their_need: Some(zs()), ..p })
{
    dz_heads(p.doc); dz_closure(zs()); dz_heads(zs());
    let m = m_a();
    assert(os().contains(0int) && !zs().contains(0int));
    let q = recv(dz(), 1, p, m, zs());
    assert(zs().union(zs()) =~= zs()); assert(zs().difference(zs()) =~= zs());
    assert(os().intersect(zs()) =~= zs());
    assert(heads(dz(), zs()) == zs());
    assert(zs().union(zs()) == zs());
    assert(p.sent_hashes.difference(closure(dz(), 1, zs())) =~= zs());
    peer_ext(q, Peer { in_flight: false, their_heads: Some(os()), their_have: Some(seq![hv1()]), their_need: Some(zs()), ..p });
}
// A (doc {0}) receives a message with empty heads, no changes (R0 or R1): wipe
proof fn lemma_recv_a(p: Peer, m: Msg)
    requires p.doc == os(), p.queue == zs(), p.shared_heads == zs(), p.sent_hashes == zs(), m.heads == zs(), m.changes == zs(),
    ensures recv(dz(), 1, p, m, os()) == (Peer { last_sent_heads: zs(), in_flight: false, their_heads: Some(zs()), their_have: Some(m.have), their_need: Some(m.need), ..p })
{
    dz_heads(p.doc); dz_heads(os()); dz_closure(zs());
    assert(os().contains(0int) && !zs().contains(0int));
    let q = recv(dz(), 1, p, m, os());
    assert(os().union(zs()) =~= os()); assert(os().difference(os()) =~= zs());
    assert(zs().intersect(os()) =~= zs());
    assert(m.heads.intersect(os()) =~= m.heads);
    assert(p.queue.union(m.changes).difference(os()) =~= zs());
    assert(m.heads == ISet::<int>::empty());
    assert(p.sent_hashes.difference(closure(dz(), 1, zs())) =~= zs());
    peer_ext(q, Peer { last_sent_heads: zs(), in_flight: false, their_heads: Some(zs()), their_have: Some(m.have), their_need: Some(m.need), ..p });
}
// B generates its reply to A's heads
proof fn lemma_gen_b(p: Peer)
    requires p.doc == zs(), p.queue == zs(), p.shared_heads == zs(), p.last_sent_heads == zs(), p.sent_hashes == zs(), !p.needs_reset,
        p.their_heads == Some(os()), p.their_have == Some(seq![hv1()]), p.their_need == Some(zs()), p.have_responded, !p.in_flight,
    ensures gen(dz(), 1, p, zs(), false) == (Peer { in_flight: true, ..p }, Some(m_r1()))
{
    dz_heads(p.doc); dz_missing(p.doc, p.queue, opt_set(p.their_heads));
    assert(os().contains(0int) && !zs().contains(0int));
    let need = missing(dz(), 1, p.doc, p.queue, opt_set(p.their_heads));
    assert(need =~= os());
    let have = seq![hv1()];
    assert(have.len() == 1 && have[0] == hv1());
    assert(os().subset_of(opt_set(p.their_heads)));
    assert(!must_reset(p));
    // send set is empty (nothing to send: doc is empty)
    assert(all_last_sync(have) =~= zs()) by {
        assert forall|x: int| !all_last_sync(have).contains(x) by {
            if all_last_sync(have).contains(x) { let i = choose|i: int| 0 <= i < 1 && #[trigger] have[i].last_sync.contains(x); assert(have[i] == hv1()); }
        }
    }
    dz_closure(all_last_sync(have));
    let hs = p.doc.difference(closure(dz(), 1, all_last_sync(have)));
    assert(hs =~= zs());
    let miss = ISet::new(|h: int| hs.contains(h) && forall|i: int| 0 <= i < have.len() ==> !(#[trigger] have[i].bloom.contains(h)));
    assert(miss =~= zs());
    let sent = ISet::new(|h: int| hs.contains(h) && exists|m: int| miss.contains(m) && closure(dz(), 1, ISet::empty().insert(h)).contains(m));
    assert(sent =~= zs());
    assert(zs().intersect(p.doc) =~= zs());
    assert(hashes_to_send(dz(), 1, p.doc, have, zs()) =~= zs());
    assert(send_set(dz(), 1, p) =~= zs());
    assert(zs().union(zs()) =~= zs());
    assert(heads(dz(), p.doc) == zs());
    assert(Some(os()) != Some(zs())) by { assert(os() != zs()); }
    let r = gen(dz(), 1, p, zs(), false);
    peer_ext(r.0, Peer { in_flight: true, ..p });
    assert(r.1 == Some(m_r1()));
}

// ---- Recv / Timeout / Edit / Gen at world level ----
proof fn recv_guard(w: World, who: int, m: Msg, s2: ISet<int>)
    requires w.peers.len() == 2, w.net.len() == 2, w.peers[who].queue == zs(), m.changes == zs(), s2 == w.peers[who].doc, who == 0 || who == 1, w.net[1 - who].contains(m),
    ensures guard(dz(), 1, w, Step::Recv { who, m, s2, keep: true })
{
    assert(zs().union(zs()) =~= zs());
    assert(w.peers[who].queue.union(m.changes) == zs());
}
// a world that is two peers and two nets
proof fn w2_ok(a: Peer, b: Peer, na: ISet<Msg>, nb: ISet<Msg>) ensures w2(a, b, na, nb).peers.len() == 2, w2(a, b, na, nb).net.len() == 2 {}

// Recv of keep = true: only the receiving peer changes
proof fn recv_apply(w: World, who: int, m: Msg, s2: ISet<int>, w3: World)
    requires w.peers.len() == 2, w.net.len() == 2, who == 0 || who == 1,
        w3.peers.len() == 2, w3.net.len() == 2, w3.net == w.net,
        w3.peers[who] == recv(dz(), 1, w.peers[who], m, s2), w3.peers[1 - who] == w.peers[1 - who],
    ensures apply(dz(), 1, w, Step::Recv { who, m, s2, keep: true }) == w3
{
    let a = apply(dz(), 1, w, Step::Recv { who, m, s2, keep: true });
    assert(a.peers.len() == 2 && a.net.len() == 2);
    assert(a.peers =~= w3.peers); assert(a.net =~= w3.net);
}

proof fn lasso_prefix(k: nat)
    requires k < 8,
    ensures next(dz(), 1, pw(k), pst(k), if k + 1 < 8 { pw((k + 1) as nat) } else { cw(0) }),
{
    dz_wf();
    assert(os().contains(0int) && !zs().contains(0int));
    reveal_with_fuel(pw, 1);
    let tgt = if k + 1 < 8 { pw((k + 1) as nat) } else { cw(0) };
    if k == 0 {
        let w = pw(0); let st = pst(0);
        assert(guard(dz(), 1, w, st)) by { assert(zs().difference(zs()) =~= zs()); assert(forall|y: int| !w.peers[0].queue.contains(y)); }
        let a = apply(dz(), 1, w, st);
        assert(a.peers[0] == pa_init());
        world_ext(a, tgt);
    } else if k == 1 {
        let w = pw(1); let st = pst(1);
        gen_init_b();
        assert(guard(dz(), 1, w, st));
        let a = apply(dz(), 1, w, st);
        world_ext(a, tgt);
    } else if k == 2 {
        let w = pw(2); let st = pst(2);
        gen_init_a();
        assert(guard(dz(), 1, w, st)) by { dz_closure(zs()); assert(os().difference(zs()) =~= os()); }
        let a = apply(dz(), 1, w, st);
        world_ext(a, tgt);
    } else if k == 3 {
        let w = pw(3); let st = pst(3);
        recv_guard(w, 1, m_a(), zs());
        lemma_recv_b(w.peers[1]);
        assert(w.net[0].contains(m_a()));
        recv_apply(w, 1, m_a(), zs(), tgt);
    } else if k == 4 {
        let w = pw(4); let st = pst(4);
        lemma_gen_b(w.peers[1]);
        assert(guard(dz(), 1, w, st)) by { dz_closure(zs()); assert(zs().difference(zs()) =~= zs()); }
        let a = apply(dz(), 1, w, st);
        world_ext(a, tgt);
    } else if k == 5 {
        let w = pw(5); let st = pst(5);
        recv_guard(w, 0, m_r1(), os());
        lemma_recv_a(w.peers[0], m_r1());
        assert(w.net[1].contains(m_r1()));
        recv_apply(w, 0, m_r1(), os(), tgt);
    } else if k == 6 {
        let w = pw(6); let st = pst(6);
        recv_guard(w, 0, m_r0(), os());
        lemma_recv_a(w.peers[0], m_r0());
        assert(w.net[1].contains(m_r0()));
        recv_apply(w, 0, m_r0(), os(), tgt);
    } else {
        let w = pw(7); let st = pst(7);
        let a = apply(dz(), 1, w, st);
        assert(zs().union(zs()) =~= zs());
        peer_ext(tmo(pb3()), pb0());
        world_ext(a, tgt);
    }
}
proof fn gen_init_b() ensures gen(dz(), 1, init_peer(), os(), false) == (mk(zs(), zs(), None, Some(Seq::empty()), None, true, true), Some(m_r0())) {
    let p = init_peer();
    dz_heads(p.doc); dz_missing(p.doc, p.queue, opt_set(p.their_heads));
    assert(zs().union(zs()) =~= zs());
    assert(send_set(dz(), 1, p) == zs());
    let r = gen(dz(), 1, p, os(), false);
    assert(opt_set(p.their_heads) == zs());
    assert(missing(dz(), 1, p.doc, p.queue, zs()) == zs()) by { assert(zs().difference(zs()).difference(zs()) =~= zs()); }
    assert(!must_reset(p));
    peer_ext(r.0, mk(zs(), zs(), None, Some(Seq::empty()), None, true, true));
}
proof fn gen_init_a() ensures gen(dz(), 1, pa_init(), os(), false) == (mk(os(), os(), None, Some(Seq::empty()), None, true, true), Some(m_a())) {
    let p = pa_init();
    dz_heads(p.doc); dz_missing(p.doc, p.queue, opt_set(p.their_heads));
    assert(os().contains(0int) && !zs().contains(0int));
    assert(zs().union(zs()) =~= zs());
    assert(send_set(dz(), 1, p) == zs());
    let r = gen(dz(), 1, p, os(), false);
    assert(opt_set(p.their_heads) == zs());
    assert(missing(dz(), 1, p.doc, p.queue, zs()) == zs()) by { assert(zs().difference(os()).difference(zs()) =~= zs()); }
    assert(!must_reset(p));
    assert(heads(dz(), p.doc) == os());
    peer_ext(r.0, mk(os(), os(), None, Some(Seq::empty()), None, true, true));
}

proof fn lasso_cycle(j: nat)
    requires j < 7,
    ensures next(dz(), 1, cw(j), cst(j), cw(((j + 1) % 7) as nat)),
{
    dz_wf();
    assert(os().contains(0int) && !zs().contains(0int));
    net0_has();
    let w = cw(j); let st = cst(j);
    let tgt = cw(((j + 1) % 7) as nat);
    if j == 0 { c0(); }
    else if j == 1 {
        recv_guard(w, 1, m_a(), zs());
        lemma_recv_b(w.peers[1]);
        recv_apply(w, 1, m_a(), zs(), tgt);
    } else if j == 2 {
        lemma_gen_b(w.peers[1]);
        assert(guard(dz(), 1, w, st)) by { dz_closure(zs()); assert(zs().difference(zs()) =~= zs()); }
        let a = apply(dz(), 1, w, st);
        ins_same(net0()[1], m_r1());
        world_ext(a, tgt);
    } else if j == 3 {
        recv_guard(w, 0, m_r1(), os());
        lemma_recv_a(w.peers[0], m_r1());
        recv_apply(w, 0, m_r1(), os(), tgt);
    } else if j == 4 {
        recv_guard(w, 0, m_r0(), os());
        lemma_recv_a(w.peers[0], m_r0());
        recv_apply(w, 0, m_r0(), os(), tgt);
    } else if j == 5 {
        let a = apply(dz(), 1, w, st);
        assert(zs().union(zs()) =~= zs());
        peer_ext(tmo(pa0()), pa0());
        world_ext(a, tgt);
    } else {
        let a = apply(dz(), 1, w, st);
        peer_ext(tmo(pb3()), pb0());
        world_ext(a, tgt);
    }
}
proof fn lasso_next(k: nat) ensures next(dz(), 1, lw(k), lst(k), lw((k + 1) as nat)) {
    if k < 8 { lasso_prefix(k); } else {
        let j = ((k - 8) % 7) as nat;
        lasso_cycle(j);
        assert(((k + 1 - 8) % 7) as nat == ((j + 1) % 7) as nat);
    }
}
proof fn lasso_docs(k: nat) requires k >= 1, ensures lw(k).peers[0].doc == os(), lw(k).peers[1].doc == zs() {
    if k < 8 { reveal_with_fuel(pw, 1); } else { let j = ((k - 8) % 7) as nat; assert(j < 7); }
}
// the network only ever holds the three messages
proof fn lasso_net(k: nat) ensures forall|x: Msg| #[trigger] lw(k).net[0].contains(x) ==> x == m_a(),
    forall|x: Msg| #[trigger] lw(k).net[1].contains(x) ==> x == m_r0() || x == m_r1(),
{
    if k < 8 { reveal_with_fuel(pw, 1); } else { let j = ((k - 8) % 7) as nat; assert(j < 7); net0_has(); }
}
// actions
pub open spec fn is_recv(st: Step, who: int, m: Msg) -> bool { match st { Step::Recv { who: w, m: mm, .. } => w == who && mm == m, _ => false } }
pub open spec fn is_gen(st: Step, who: int) -> bool { match st { Step::Gen { who: w, .. } => w == who, _ => false } }
pub open spec fn is_tmo(st: Step, who: int) -> bool { match st { Step::Timeout { who: w } => w == who, _ => false } }
pub open spec fn is_drop(st: Step) -> bool { match st { Step::Drop { .. } => true, _ => false } }
pub open spec fn is_edit(st: Step) -> bool { match st { Step::Edit { .. } => true, _ => false } }
pub open spec fn tmo_after(sts: spec_fn(nat) -> Step, who: int, m: nat) -> bool { exists|k: nat| #![trigger sts(k)] k >= m && is_tmo(sts(k), who) }
pub open spec fn gen_after(sts: spec_fn(nat) -> Step, who: int, m: nat) -> bool { exists|k: nat| #![trigger sts(k)] k >= m && is_gen(sts(k), who) }
pub open spec fn recv_after(sts: spec_fn(nat) -> Step, who: int, msg: Msg, m: nat) -> bool { exists|k: nat| #![trigger sts(k)] k >= m && is_recv(sts(k), who, msg) }
pub open spec fn in_net_after(ws: spec_fn(nat) -> World, who: int, msg: Msg, m: nat) -> bool { exists|k: nat| #![trigger ws(k)] k >= m && ws(k).net[1 - who].contains(msg) }
pub open spec fn inf_in_net(ws: spec_fn(nat) -> World, who: int, msg: Msg) -> bool { forall|m: nat| #[trigger] in_net_after(ws, who, msg, m) }
pub open spec fn inf_recv(sts: spec_fn(nat) -> Step, who: int, msg: Msg) -> bool { forall|m: nat| #[trigger] recv_after(sts, who, msg, m) }
// "per-action fairness" of an infinite schedule of model steps
pub open spec fn per_action_fair(ws: spec_fn(nat) -> World, sts: spec_fn(nat) -> Step) -> bool {
    // weak fairness of each peer's timeout and generate action
    (forall|who: int, m: nat| (who == 0 || who == 1) ==> #[trigger] tmo_after(sts, who, m))
    && (forall|who: int, m: nat| (who == 0 || who == 1) ==> #[trigger] gen_after(sts, who, m))
    // a message that sits in the network infinitely often (so it was sent) is delivered infinitely often
    && (forall|who: int, msg: Msg| (who == 0 || who == 1) && #[trigger] inf_in_net(ws, who, msg) ==> #[trigger] inf_recv(sts, who, msg))
    // loss-free, and no edit after the first step
    && (forall|k: nat| #![trigger sts(k)] !is_drop(sts(k)) && (k >= 1 ==> !is_edit(sts(k))))
}
// THEOREM (counterexample).  There is an infinite model schedule (a lasso) that is a legal run from `init`,
// satisfies per-action fairness (even delivering every network message every cycle, no drops, no stale-only luck)
// and in which the documents are never equal after the first edit.
pub proof fn theorem_no_liveness_per_action_fairness()
    ensures
        wf(dz(), 1),
        init(lw(0)),
        forall|k: nat| #[trigger] next(dz(), 1, lw(k), lst(k), lw((k + 1) as nat)),
        per_action_fair(|k: nat| lw(k), |k: nat| lst(k)),
        forall|k: nat| k >= 1 ==> #[trigger] lw(k).peers[0].doc != lw(k).peers[1].doc,
{
    dz_wf();
    assert(init(lw(0))) by { reveal_with_fuel(pw, 1); }
    assert forall|k: nat| #[trigger] next(dz(), 1, lw(k), lst(k), lw((k + 1) as nat)) by { lasso_next(k); }
    assert forall|k: nat| k >= 1 implies #[trigger] lw(k).peers[0].doc != lw(k).peers[1].doc by {
        lasso_docs(k); assert(os().contains(0int) && !zs().contains(0int));
    }
    let ws = |k: nat| lw(k);
    let sts = |k: nat| lst(k);
    assert forall|who: int, m: nat| (who == 0 || who == 1) implies #[trigger] tmo_after(sts, who, m) by {
        if who == 0 || who == 1 {
            let k = (8 + 7 * m + 5 + who) as nat;
            assert(sts(k) == cst(((k - 8) % 7) as nat));
        }
    }
    assert forall|who: int, m: nat| (who == 0 || who == 1) implies #[trigger] gen_after(sts, who, m) by {
        if who == 0 || who == 1 {
            let k = (8 + 7 * m + 2 * who) as nat;
            assert(sts(k) == cst(((k - 8) % 7) as nat));
        }
    }
    assert forall|who: int, msg: Msg| (who == 0 || who == 1)
        && #[trigger] inf_in_net(ws, who, msg)
        implies #[trigger] inf_recv(sts, who, msg) by {
        if (who == 0 || who == 1) && inf_in_net(ws, who, msg) {
            assert(in_net_after(ws, who, msg, 0));
            let k0 = choose|k: nat| #![trigger ws(k)] k >= 0 && ws(k).net[1 - who].contains(msg);
            lasso_net(k0);
            assert forall|m: nat| #[trigger] recv_after(sts, who, msg, m) by {
                let off: nat = if who == 1 { 1 } else if msg == m_r1() { 3 } else { 4 };
                let k = (8 + 7 * m + off) as nat;
                assert(sts(k) == cst(((k - 8) % 7) as nat));
            }
        }
    }
    assert forall|k: nat| #![trigger sts(k)] !is_drop(sts(k)) && (k >= 1 ==> !is_edit(sts(k))) by {
        if k >= 8 { let j = ((k - 8) % 7) as nat; assert(j < 7); assert(sts(k) == cst(j)); }
    }
}
}
