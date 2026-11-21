// Part F (vlm47_amcode#7): a failing receive_sync_message. Kept in its own file so that conform.rs is unchanged.
use vstd::prelude::*;
use crate::model as M;
use crate::model::vset;
use crate::conform::*;

verus! {

// =====================================================================================
// Part F (vlm47_amcode#7, "receive never fails"): a FAILING receive_sync_message.
// Real code (sync.rs receive_sync_message_inner): the only call that can return Err on a message that passed
// msg_wf is `load_incremental_log_patches`; `filter_changes` always returns Ok (T11).  Before that call the code
// has already set in_flight = false (M3) and the capability fields; msg_wf excludes SYNC_RESET, so sent_hashes is
// untouched.  shared_heads, last_sent_heads, their_* are written only after the call, so an Err leaves them.
// recv_post's Err clause (proved) says exactly this about the sync state.  About the DOCUMENT on Err nothing is
// proved (T10 is silent), so Part F ASSUMES (reading of apply.rs / automerge.rs, not proved): the applied set is
// unchanged, deps and n unchanged, a_wf holds, and the queue (staged changes) may only shrink
// (`staged.remove_actor_branch_from` on the duplicate_seq error).
// =====================================================================================
pub open spec fn recv_err_core(c: Cfg, c2: Cfg, who: int, keep: bool, msg: Message, a1: Automerge, s1: State) -> bool {
    c.net[1 - who].contains(abs_msg(msg)) && msg_wf(msg, c.a[who])
    // proved clause of recv_post (Err)
    && abs_state(s1) == M::Peer { in_flight: false, ..abs_state(c.s[who]) }
    && s1.read_only == c.s[who].read_only && s1.peer_read_only == c.s[who].peer_read_only
    // ASSUMED about the document on Err
    && a_wf(a1) && st_wf(s1, a1) && a_deps(a1) == a_deps(c.a[who]) && a_n(a1) == a_n(c.a[who])
    && a_doc(a1) == a_doc(c.a[who]) && a_queue(a1).subset_of(a_queue(c.a[who]))
    && c2.a == c.a.update(who, a1) && c2.s == c.s.update(who, s1)
    && c2.net == (if keep { c.net } else { c.net.update(1 - who, c.net[1 - who].remove(abs_msg(msg))) })
}
pub open spec fn step_recv_err(c: Cfg, c2: Cfg, who: int, keep: bool) -> bool {
    (who == 0 || who == 1)
    && exists|msg: Message, a1: Automerge, s1: State| recv_err_core(c, c2, who, keep, msg, a1, s1)
}
pub open spec fn code_next_f(c: Cfg, c2: Cfg) -> bool {
    code_next(c, c2) || exists|who: int, keep: bool| step_recv_err(c, c2, who, keep)
}
pub open spec fn code_run_f(cs: spec_fn(nat) -> Cfg, k: nat) -> bool {
    cfg_wf(cs(0)) && forall|i: nat| i < k ==> #[trigger] code_next_f(cs(i), cs(i + 1))
}

// a failing receive keeps cfg_wf and the model's invariant `inv`
pub proof fn lemma_err_step(c: Cfg, c2: Cfg, who: int, keep: bool)
    requires cfg_wf(c), M::inv(cfg_d(c), cfg_n(c), abs_cfg(c)), step_recv_err(c, c2, who, keep),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c), M::inv(cfg_d(c2), cfg_n(c2), abs_cfg(c2)),
{
    let d = cfg_d(c); let n = cfg_n(c); let w = abs_cfg(c); let w2 = abs_cfg(c2);
    let (msg, a1, s1) = choose|msg: Message, a1: Automerge, s1: State| recv_err_core(c, c2, who, keep, msg, a1, s1);
    assert(w.peers.len() == 2);
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    assert(a_deps(c.a[who]) == d && a_n(c.a[who]) == n);
    assert(c2.s.len() == 2 && c2.a.len() == 2 && c2.net.len() == 2);
    assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
    assert(w2.peers.len() == 2);
    let p = w.peers[who]; let q = w2.peers[who];
    assert(q.doc == p.doc && q.their_heads == p.their_heads);
    assert(w2.peers[1 - who] == w.peers[1 - who]);
    assert(w2.net[who] == w.net[who] || keep || who == who);
    assert forall|i: int| 0 <= i < 2 implies #[trigger] M::peer_inv(d, n, w2, i) by {
        assert(M::peer_inv(d, n, w, i));
        assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[i].their_heads == w.peers[i].their_heads);
        assert(w2.peers[1 - i].doc == w.peers[1 - i].doc);
        assert forall|m: M::Msg| #[trigger] w2.net[i].contains(m) implies w.net[i].contains(m) by {
            if !keep && i == 1 - who { assert(w2.net[i] == w.net[i].remove(abs_msg(msg))); }
        }
    }
}

pub proof fn lemma_run_inv_f(cs: spec_fn(nat) -> Cfg, k: nat)
    requires code_run_f(cs, k), session_start(cs(0)),
    ensures cfg_wf(cs(k)), M::inv(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k))), cfg_d(cs(k)) == cfg_d(cs(0)), cfg_n(cs(k)) == cfg_n(cs(0)),
    decreases k,
{
    if k == 0 { lemma_session_inv(cs(0)); } else {
        lemma_run_inv_f(cs, (k - 1) as nat);
        let c = cs((k - 1) as nat); let c2 = cs(k);
        let i = (k - 1) as nat;
        assert(code_next_f(cs(i), cs(i + 1)));
        assert(i + 1 == k);
        if code_next(c, c2) {
            lemma_code_step(c, c2);
            let st = choose|st: M::Step| M::next(cfg_d(c), cfg_n(c), abs_cfg(c), st, abs_cfg(c2));
            assert(M::wf(cfg_d(c), cfg_n(c)));
            M::lemma_step(cfg_d(c), cfg_n(c), abs_cfg(c), st, abs_cfg(c2));
            assert(cfg_d(c2) == cfg_d(c) && cfg_n(c2) == cfg_n(c)) by { assert(a_deps(c2.a[0]) == a_deps(c2.a[0])); }
        } else {
            let (who, keep) = choose|who: int, keep: bool| step_recv_err(c, c2, who, keep);
            lemma_err_step(c, c2, who, keep);
        }
    }
}
// SAFETY with failing receives: in any run of the code from a session start in which receive may also fail (Err
// clause as above), if at the end both peers are in report_in_sync, the documents are equal.
pub proof fn theorem_code_safety_err(cs: spec_fn(nat) -> Cfg, k: nat)
    requires code_run_f(cs, k), session_start(cs(0)),
        M::report_in_sync(cfg_d(cs(k)), cfg_n(cs(k)), abs_peer(cs(k).a[0], cs(k).s[0])),
        M::report_in_sync(cfg_d(cs(k)), cfg_n(cs(k)), abs_peer(cs(k).a[1], cs(k).s[1])),
    ensures a_doc(cs(k).a[0]) == a_doc(cs(k).a[1]),
{
    lemma_run_inv_f(cs, k);
    let c = cs(k);
    assert(M::wf(cfg_d(c), cfg_n(c)));
    M::theorem_safety_inv(cfg_d(c), cfg_n(c), abs_cfg(c));
}


// ---------------------------------------------------------------------------------------------------------
// Part F, liveness.  In a lock-step round the next round starts with Timeout A and Timeout B, which overwrite
// in_flight and sent_hashes.  A failed receive differs from a Drop only in the receiver's in_flight (Err clause),
// so a round whose delivery fails is the model's LOSSY round up to in_flight (`eqi`), and the model's fairness
// ("4 consecutive rounds lose nothing") must count a failed receive as a loss.
// ASSUMED for liveness (beyond Part F safety): the failing receive also leaves the QUEUE unchanged.  With the
// duplicate_seq error path (staged.remove_actor_branch_from) the queue may shrink; I did not prove liveness then.
// ---------------------------------------------------------------------------------------------------------
pub open spec fn recv_err_q(c: Cfg, c2: Cfg, who: int, keep: bool, msg: Message, a1: Automerge, s1: State) -> bool {
    recv_err_core(c, c2, who, keep, msg, a1, s1) && a_queue(a1) == a_queue(c.a[who])
}
pub open spec fn nrm(p: M::Peer) -> M::Peer { M::Peer { in_flight: false, ..p } }
// equal worlds up to the in_flight flags
pub open spec fn eqi(w: M::World, w2: M::World) -> bool {
    w.peers.len() == 2 && w2.peers.len() == 2 && w.net == w2.net
    && forall|i: int| 0 <= i < 2 ==> nrm(w.peers[i]) == nrm(w2.peers[i])
}
pub open spec fn deliver_f(c: Cfg, c2: Cfg, from: int, r: Option<Message>, loss: bool, err: bool) -> bool {
    match r {
        None => c2 == c && !loss && !err,
        Some(m) => if loss { !err && drop_rel(c, c2, from, abs_msg(m)) }
                   else if err { exists|a1: Automerge, s1: State| #[trigger] recv_err_q(c, c2, 1 - from, false, m, a1, s1) }
                   else { exists|a1: Automerge, s1: State| #[trigger] recv_core(c, c2, 1 - from, false, m, a1, s1) },
    }
}
pub struct CRoundF { pub c1: Cfg, pub c2: Cfg, pub c3: Cfg, pub c4: Cfg, pub c5: Cfg,
    pub ra: Option<Message>, pub rb: Option<Message>, pub lossa: bool, pub lossb: bool, pub erra: bool, pub errb: bool }
pub open spec fn cround_ok_f(c0: Cfg, c6: Cfg, cr: CRoundF) -> bool {
    step_tmo(c0, cr.c1, 0) && step_tmo(cr.c1, cr.c2, 1)
    && gen_rel_r(cr.c2, cr.c3, 0, cr.ra) && gen_rel_r(cr.c3, cr.c4, 1, cr.rb)
    && deliver_f(cr.c4, cr.c5, 0, cr.ra, cr.lossa, cr.erra) && deliver_f(cr.c5, c6, 1, cr.rb, cr.lossb, cr.errb)
}
// a loss or a failed receive is a loss
pub open spec fn cr_good_f(cr: CRoundF) -> bool { !cr.lossa && !cr.lossb && !cr.erra && !cr.errb }

pub proof fn lemma_err_wf(c: Cfg, c2: Cfg, who: int, keep: bool, msg: Message, a1: Automerge, s1: State)
    requires cfg_wf(c), who == 0 || who == 1, recv_err_core(c, c2, who, keep, msg, a1, s1),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
{
    assert(cfg_peer_ok(c, who) && cfg_peer_ok(c, 1 - who));
    assert(a_deps(c.a[who]) == cfg_d(c) && a_n(c.a[who]) == cfg_n(c));
    assert(c2.s.len() == 2 && c2.a.len() == 2 && c2.net.len() == 2);
    assert(cfg_peer_ok(c2, who)); assert(cfg_peer_ok(c2, 1 - who));
}

// the model's rounds depend on the start world only through rw2, which does not see in_flight
pub proof fn lemma_eqi_round(d: M::Deps, n: int, w: M::World, w2: M::World, rp: M::RP)
    requires eqi(w, w2),
    ensures M::rvalid(d, n, w, rp) == M::rvalid(d, n, w2, rp), M::rw6(d, n, w, rp) == M::rw6(d, n, w2, rp),
{
    assert(M::tmo(w.peers[0]) == M::tmo(w2.peers[0]));
    assert(M::tmo(w.peers[1]) == M::tmo(w2.peers[1]));
    assert(M::rw2(d, n, w).peers =~= M::rw2(d, n, w2).peers);
    assert(M::rw2(d, n, w) == M::rw2(d, n, w2));
}

// One delivery inside a round.  `w` is the model world; the receiver is exact, the sender equal up to in_flight.
pub open spec fn dstep(c: Cfg, c2: Cfg, from: int, m: Message, loss: bool, err: bool) -> M::Step {
    if loss || err { M::Step::Drop { who: from, m: abs_msg(m) } }
    else { M::Step::Recv { who: 1 - from, m: abs_msg(m), s2: s2_of(c, c2, 1 - from, m), keep: false } }
}
pub proof fn lemma_deliver_f(c: Cfg, c2: Cfg, from: int, r: Option<Message>, loss: bool, err: bool, w: M::World)
    requires cfg_wf(c), from == 0 || from == 1, deliver_f(c, c2, from, r, loss, err),
        w.peers.len() == 2, w.net == c.net,
        w.peers[1 - from] == abs_cfg(c).peers[1 - from], nrm(w.peers[from]) == nrm(abs_cfg(c).peers[from]),
    ensures cfg_wf(c2), cfg_d(c2) == cfg_d(c), cfg_n(c2) == cfg_n(c),
        match r {
            None => eqi(abs_cfg(c2), w) && w.peers[1 - from] == abs_cfg(c2).peers[1 - from]
                && (w.peers[from] == abs_cfg(c).peers[from] ==> w.peers[from] == abs_cfg(c2).peers[from]),
            Some(m) => M::guard(cfg_d(c), cfg_n(c), w, dstep(c, c2, from, m, loss, err))
                && eqi(abs_cfg(c2), M::apply(cfg_d(c), cfg_n(c), w, dstep(c, c2, from, m, loss, err)))
                && (w.peers[from] == abs_cfg(c).peers[from] ==>
                    M::apply(cfg_d(c), cfg_n(c), w, dstep(c, c2, from, m, loss, err)).peers[from] == abs_cfg(c2).peers[from])
                && (!err ==> M::apply(cfg_d(c), cfg_n(c), w, dstep(c, c2, from, m, loss, err)).peers[1 - from] == abs_cfg(c2).peers[1 - from])
        },
{
    let d = cfg_d(c); let n = cfg_n(c); let wc = abs_cfg(c); let wc2 = abs_cfg(c2);
    assert(wc.peers.len() == 2);
    match r {
        None => {
            assert(c2 == c);
            assert forall|i: int| 0 <= i < 2 implies nrm(wc2.peers[i]) == nrm(w.peers[i]) by {
                if i == from { } else { assert(i == 1 - from); }
            }
        }
        Some(m) => {
            let st = dstep(c, c2, from, m, loss, err);
            if loss {
                lemma_drop_model(c, c2, from, abs_msg(m));
                assert(M::guard(d, n, w, st));
                let w2 = M::apply(d, n, w, st);
                assert(w2.peers =~= w.peers);
                assert(w2.net =~= wc2.net);
                assert forall|i: int| 0 <= i < 2 implies nrm(wc2.peers[i]) == nrm(w2.peers[i]) by { assert(wc2.peers[i] == wc.peers[i]); }
                assert(eqi(wc2, w2));
            } else if err {
                let (a1, s1) = choose|a1: Automerge, s1: State| #[trigger] recv_err_q(c, c2, 1 - from, false, m, a1, s1);
                lemma_err_wf(c, c2, 1 - from, false, m, a1, s1);
                assert(M::guard(d, n, w, st));
                let w2 = M::apply(d, n, w, st);
                assert(w2.peers =~= w.peers);
                assert(w2.net =~= wc2.net);
                let who = 1 - from;
                assert(cfg_peer_ok(c, who));
                assert(a_deps(c.a[who]) == d && a_n(c.a[who]) == n);
                assert(abs_peer(a1, s1) == nrm(abs_peer(c.a[who], c.s[who])));
                assert(wc2.peers[who] == abs_peer(a1, s1));
                assert(wc2.peers[from] == wc.peers[from]);
                assert forall|i: int| 0 <= i < 2 implies nrm(wc2.peers[i]) == nrm(w2.peers[i]) by {
                    if i == who { assert(nrm(wc2.peers[i]) == nrm(wc.peers[i])); } else { assert(i == from); }
                }
                assert(eqi(wc2, w2));
            } else {
                let (a1, s1) = choose|a1: Automerge, s1: State| #[trigger] recv_core(c, c2, 1 - from, false, m, a1, s1);
                lemma_recv_model(c, c2, 1 - from, m, a1, s1);
                let who = 1 - from;
                assert(a_doc(a1) == s2_of(c, c2, who, m));
                assert(M::next(d, n, wc, st, wc2));
                assert(M::guard(d, n, w, st));
                let w2 = M::apply(d, n, w, st);
                assert(w2.net =~= wc2.net);
                assert(w2.peers =~= w.peers.update(who, M::recv(d, n, w.peers[who], abs_msg(m), s2_of(c, c2, who, m))));
                assert(wc2.peers =~= wc.peers.update(who, M::recv(d, n, wc.peers[who], abs_msg(m), s2_of(c, c2, who, m))));
                assert forall|i: int| 0 <= i < 2 implies nrm(wc2.peers[i]) == nrm(w2.peers[i]) by {
                    if i == who { assert(w.peers[who] == wc.peers[who]); } else { assert(i == from); }
                }
                assert(eqi(wc2, w2));
            }
        }
    }
}


pub open spec fn rp_of_round_f(cr: CRoundF, c6: Cfg, ba: ISet<int>, fa: bool, da: bool, bb: ISet<int>, fb: bool, db: bool) -> M::RP {
    M::RP { ba, fa, da, bb, fb, db,
        s2a: match cr.rb { Some(m) => if cr.lossb || cr.errb { ISet::empty() } else { s2_of(cr.c5, c6, 0, m) }, None => ISet::empty() },
        s2b: match cr.ra { Some(m) => if cr.lossa || cr.erra { ISet::empty() } else { s2_of(cr.c4, cr.c5, 1, m) }, None => ISet::empty() },
        lossa: cr.lossa || cr.erra, lossb: cr.lossb || cr.errb }
}

// A code round with failing receives is a model round up to in_flight (a failed receive counts as a loss).
pub proof fn lemma_round_code_f(c0: Cfg, c6: Cfg, cr: CRoundF)
    requires cfg_wf(c0), cround_ok_f(c0, c6, cr),
    ensures cfg_wf(c6), cfg_d(c6) == cfg_d(c0), cfg_n(c6) == cfg_n(c0),
        exists|rp: M::RP| M::rvalid(cfg_d(c0), cfg_n(c0), abs_cfg(c0), rp)
            && eqi(abs_cfg(c6), M::rw6(cfg_d(c0), cfg_n(c0), abs_cfg(c0), rp)) && (M::good(rp) <==> cr_good_f(cr)),
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
    let rp = rp_of_round_f(cr, c6, ba, fa, da, bb, fb, db);
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
    let w4 = M::rw4(d, n, w0, rp); let w5 = M::rw5(d, n, w0, rp);
    assert(cfg_wf(cr.c4));
    lemma_deliver_f(cr.c4, cr.c5, 0, cr.ra, cr.lossa, cr.erra, w4);
    assert(cfg_wf(cr.c5) && cfg_d(cr.c5) == d && cfg_n(cr.c5) == n && eqi(abs_cfg(cr.c5), w5)
        && w5.peers[0] == abs_cfg(cr.c5).peers[0]
        && (match M::msg_a(d, n, w0, rp) { Some(m) => M::guard(d, n, w4, M::st5(rp, m)), None => true })) by {
        match cr.ra {
            Some(m) => {
                assert(M::st5(rp, abs_msg(m)) == dstep(cr.c4, cr.c5, 0, m, cr.lossa, cr.erra));
                assert(w5 == M::apply(d, n, w4, M::st5(rp, abs_msg(m))));
                if !(cr.lossa || cr.erra) { assert(rp.s2b == s2_of(cr.c4, cr.c5, 1, m)); }
            }
            None => { assert(w5 == w4); }
        }
    }
    lemma_deliver_f(cr.c5, c6, 1, cr.rb, cr.lossb, cr.errb, w5);
    let w6 = M::rw6(d, n, w0, rp);
    assert(cfg_wf(c6) && cfg_d(c6) == d && cfg_n(c6) == n && eqi(abs_cfg(c6), w6)
        && (match M::msg_b(d, n, w0, rp) { Some(m) => M::guard(d, n, w5, M::st6(rp, m)), None => true })) by {
        match cr.rb {
            Some(m) => {
                assert(M::st6(rp, abs_msg(m)) == dstep(cr.c5, c6, 1, m, cr.lossb, cr.errb));
                assert(w6 == M::apply(d, n, w5, M::st6(rp, abs_msg(m))));
                if !(cr.lossb || cr.errb) { assert(rp.s2a == s2_of(cr.c5, c6, 0, m)); }
            }
            None => { assert(w6 == w5); }
        }
    }
    assert(M::rvalid(d, n, w0, rp)) by {
        assert(M::guard(d, n, w0, M::Step::Timeout { who: 0 }));
        assert(M::guard(d, n, M::rw1(d, n, w0), M::Step::Timeout { who: 1 }));
        assert(M::guard(d, n, M::rw2(d, n, w0), M::gstep(0, ba, fa, da)));
        assert(M::guard(d, n, M::rw3(d, n, w0, rp), M::gstep(1, bb, fb, db)));
    }
    assert(M::good(rp) == cr_good_f(cr));
}


// ---- the run, its fairness, and the theorem
pub open spec fn code_rounds_f(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF) -> bool {
    forall|k: nat| #![trigger crs(k)] cround_ok_f(cs(k), cs((k + 1) as nat), crs(k))
}
pub open spec fn code_win4_f(crs: spec_fn(nat) -> CRoundF, m: nat) -> bool {
    exists|k: nat| #![trigger crs(k)] k >= m && cr_good_f(crs(k)) && cr_good_f(crs((k + 1) as nat))
        && cr_good_f(crs((k + 2) as nat)) && cr_good_f(crs((k + 3) as nat))
}
// 4 consecutive rounds with no loss AND no failed receive, infinitely often
pub open spec fn code_fair_f(crs: spec_fn(nat) -> CRoundF) -> bool { forall|m: nat| #[trigger] code_win4_f(crs, m) }

pub proof fn lemma_rounds_wf_f(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF, k: nat)
    requires cfg_wf(cs(0)), code_rounds_f(cs, crs),
    ensures cfg_wf(cs(k)), cfg_d(cs(k)) == cfg_d(cs(0)), cfg_n(cs(k)) == cfg_n(cs(0)),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        lemma_rounds_wf_f(cs, crs, j);
        assert(cround_ok_f(cs(j), cs((j + 1) as nat), crs(j)));
        lemma_round_code_f(cs(j), cs(k), crs(j));
    }
}
pub open spec fn rp_f(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF, k: nat) -> M::RP {
    choose|rp: M::RP| M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp)
        && eqi(abs_cfg(cs((k + 1) as nat)), M::rw6(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp)) && (M::good(rp) <==> cr_good_f(crs(k)))
}
// the model's own run, started at the code's first world and following the rounds chosen above
pub open spec fn ws_f(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF, k: nat) -> M::World decreases k {
    if k == 0 { abs_cfg(cs(0)) } else { M::rw6(cfg_d(cs(0)), cfg_n(cs(0)), ws_f(cs, crs, (k - 1) as nat), rp_f(cs, crs, (k - 1) as nat)) }
}
pub proof fn lemma_ws_eqi(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF, k: nat)
    requires live_start(cs(0)), code_rounds_f(cs, crs),
    ensures eqi(ws_f(cs, crs, k), abs_cfg(cs(k))),
    decreases k,
{
    let d = cfg_d(cs(0)); let n = cfg_n(cs(0));
    if k == 0 {
        let w = abs_cfg(cs(0));
        assert forall|i: int| 0 <= i < 2 implies nrm(w.peers[i]) == nrm(w.peers[i]) by {}
        assert(eqi(w, w));
    } else {
        let j = (k - 1) as nat;
        lemma_ws_eqi(cs, crs, j);
        lemma_rounds_wf_f(cs, crs, j);
        assert(cround_ok_f(cs(j), cs(k), crs(j)));
        lemma_round_code_f(cs(j), cs(k), crs(j));
        let rp = rp_f(cs, crs, j);
        assert(cfg_d(cs(j)) == d && cfg_n(cs(j)) == n);
        lemma_eqi_round(d, n, ws_f(cs, crs, j), abs_cfg(cs(j)), rp);
        let w6 = M::rw6(d, n, abs_cfg(cs(j)), rp);
        assert forall|i: int| 0 <= i < 2 implies nrm(ws_f(cs, crs, k).peers[i]) == nrm(abs_cfg(cs(k)).peers[i]) by {
            assert(nrm(abs_cfg(cs(k)).peers[i]) == nrm(w6.peers[i]));
        }
        assert(eqi(abs_cfg(cs(k)), w6));
    }
}

// THEOREM (liveness of the code with failing receives).  As theorem_code_liveness, but each delivered message may
// make receive_sync_message return Err (Err clause of recv_post, plus the assumed document clause of recv_err_q),
// and fairness counts a failed receive as a loss: infinitely often, 4 consecutive rounds with no loss and no failed
// receive.  Then some configuration has equal documents.
pub proof fn theorem_code_liveness_err(cs: spec_fn(nat) -> Cfg, crs: spec_fn(nat) -> CRoundF)
    requires live_start(cs(0)), code_rounds_f(cs, crs), code_fair_f(crs),
    ensures exists|K: nat| #![trigger cs(K)] a_doc(cs(K).a[0]) == a_doc(cs(K).a[1]),
{
    let d = cfg_d(cs(0)); let n = cfg_n(cs(0));
    let ws = |k: nat| ws_f(cs, crs, k);
    let rps = |k: nat| rp_f(cs, crs, k);
    lemma_live_start_sinv(cs(0));
    assert(M::wf(d, n)) by { assert(cfg_peer_ok(cs(0), 0)); assert(a_wf(cs(0).a[0])); }
    assert forall|k: nat| #![trigger rps(k)] M::rvalid(d, n, ws(k), rps(k)) && ws((k + 1) as nat) == M::rw6(d, n, ws(k), rps(k)) by {
        lemma_rounds_wf_f(cs, crs, k);
        lemma_ws_eqi(cs, crs, k);
        assert(cround_ok_f(cs(k), cs((k + 1) as nat), crs(k)));
        lemma_round_code_f(cs(k), cs((k + 1) as nat), crs(k));
        let rp = rp_f(cs, crs, k);
        assert(M::rvalid(cfg_d(cs(k)), cfg_n(cs(k)), abs_cfg(cs(k)), rp));
        lemma_eqi_round(d, n, ws(k), abs_cfg(cs(k)), rp);
    }
    assert(M::run_ok(d, n, ws, rps));
    assert forall|m: nat| #[trigger] M::win4(rps, m) by {
        assert(code_win4_f(crs, m));
        let k = choose|k: nat| #![trigger crs(k)] k >= m && cr_good_f(crs(k)) && cr_good_f(crs((k + 1) as nat))
            && cr_good_f(crs((k + 2) as nat)) && cr_good_f(crs((k + 3) as nat));
        let _ = rps(k); let _ = rps((k + 1) as nat); let _ = rps((k + 2) as nat); let _ = rps((k + 3) as nat);
        lemma_rounds_wf_f(cs, crs, k); lemma_rounds_wf_f(cs, crs, (k + 1) as nat);
        lemma_rounds_wf_f(cs, crs, (k + 2) as nat); lemma_rounds_wf_f(cs, crs, (k + 3) as nat);
        lemma_round_code_f(cs(k), cs((k + 1) as nat), crs(k));
        lemma_round_code_f(cs((k + 1) as nat), cs((k + 2) as nat), crs((k + 1) as nat));
        lemma_round_code_f(cs((k + 2) as nat), cs((k + 3) as nat), crs((k + 2) as nat));
        lemma_round_code_f(cs((k + 3) as nat), cs((k + 4) as nat), crs((k + 3) as nat));
        assert(M::good(rps(k)) && M::good(rps((k + 1) as nat)) && M::good(rps((k + 2) as nat)) && M::good(rps((k + 3) as nat)));
    }
    assert(M::fair_lossy(rps));
    M::theorem_liveness(d, n, ws, rps);
    let K = choose|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc;
    lemma_ws_eqi(cs, crs, K);
    assert(nrm(ws(K).peers[0]).doc == nrm(abs_cfg(cs(K)).peers[0]).doc);
    assert(a_doc(cs(K).a[0]) == a_doc(cs(K).a[1]));
}

} // verus!
