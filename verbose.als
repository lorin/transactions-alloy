open util/relation
open util/ordering[VersionNumber] as vo
open util/ordering[WriteNumber] as wo

run {

} for 5 but exactly 1 Transaction, exactly 2 Object, exactly 3 Write


//
//
// Phenomena
//
//

/**
 * G0: Write Cycles. A history H exhibits phenomenon
 * G0 if DSG(H) contains a directed cycle consisting
 * entirely of write-dependency edges.
 */
pred G0 {
    not acyclic[ww, CommittedTransaction]
}

/**
 * Phenomenon G1 captures the essence of no-dirty-reads
 * and is comprised of G1a, G1b and G1c. 
 */
pred G1 {
    G1a or G1b or G1c
}

/**
 * G1a: Aborted Reads
 * 
 * A history H shows phenomenon G1a if it contains an aborted transaction T1 and a
 * committed transaction T2 such that T2 has read some object modified by T1
 * 
 */
pred G1a {
    some T1 : AbortedTransaction, T2 : CommittedTransaction, r : events[T2] & Read, w : events[T1] & Write | r.sees = w
}


//
//
// Isolation levels
//
//


/**
 * We define PL-1 as the level in which G0 is disallowed
 */
assert PL1 {
    not G0
}

/**
 * We define isolation level PL-2 as one in which phenomenon G1 is disallowed
 */
assert PL2 {
    not G1
}

/*
 * We define level PL-2.99 as one that proscribes G1 and G2-item
 */
assert PL2_99 {
    not G1
    not G2item
}

/**
 * We define PL-3 as an isolation level that proscribes G1 and G2
 */
assert PL3 {
    not G1
    not G2
}

fun installs[T : Transaction] : set Version {
    Version <: tr.T
}


// Directly write-depends
fun ww[] : CommittedTransaction -> CommittedTransaction {
    { disj Ti, Tj : CommittedTransaction | some v1 : Ti.installs, v2 : Tj.installs | {
        v1.obj = v2.obj
        v1.tr = Ti
        v2.tr = Tj
        v1.next = v2
        }
    } 
}

// Directly read-depends
fun wr[] : CommittedTransaction -> CommittedTransaction {
    iwr + pwr
}

// True if wr is the last write for an object in its transaction
pred is_last_write[w : Write] {
    no u : w.^enext | u.obj = w.obj
}

// Transaction T contains a read event that reads version v
pred reads[T : Transaction, v: Version] {
    some rd : T.events & Read | let wr=rd.sees | 
    {
        rd.obj = v.obj
        wr.tr = v.tr
        is_last_write[wr]
    }
}

/**
 * Directly item-read depends
 *
 * We say that Tj directly item-read-depends on Ti if 
 * Ti installs some object version xi and Tj reads xi
 */
fun iwr[] : CommittedTransaction -> CommittedTransaction {
    { disj Ti, Tj : CommittedTransaction | some xi : Version | 
        xi in installs[Ti] and reads[Tj, xi] }
}

/**
 * Directly predicate-read-depends
 * 
 * Transaction Tj directly predicate-read-depends on Ti if Tj performs an operation rj (P: Vset(P)),
 * xk ∈ Vset(P), i = k or xi << xk, and xi changes the matches of rj (P: Vset(P)).
 */
 fun pwr[] : CommittedTransaction -> CommittedTransaction {
    { disj Ti, Tj : CommittedTransaction | 
        some rj : events[Tj] & PredicateRead, xk : rj.vset.vs, xi : installs[Ti] | 
            {
                xi.obj = xk.obj
                lte[xi.vn, xk.vn] // xi's version is less than or equal to xk's version
                changes_the_matches_of[xi, rj]
            }
    }
 }

/*
Definition 2 : Change the Matches of a Predicate-Based
Read.

We say that a transaction Ti changes the matches of a predicate-based read rj
(P: Vset(P)) if
 - Ti installs xi,
 - xh immediately precedes xi in the version order,and
 - xh matches P whereas xi does not or vice-versa.

 In this case, we also say that xi changes the matches of the predicate-based read.
*/
pred changes_the_matches_of[xi : Version, rj: PredicateRead] {
    some xh : Version {
        xh = prev[xi]
        let m=rj.p.matches | 
            xh in m <=> xi not in m
    }
}

sig Object {}

abstract sig Transaction {}

abstract sig CommittedTransaction extends Transaction {
    irw : set CommittedTransaction, // directly item-anti-depends
    prw : set CommittedTransaction, // directly directly predicate-anti-depends
    rw : set CommittedTransaction, // directly anti-depends
}

sig T extends CommittedTransaction {}

sig AbortedTransaction extends Transaction {}


abstract sig Event {
    tr: Transaction,
    eo: set Event, // event order (partial ordering of events)
    enext: lone Event // next event in the transaction
}

sig Commit extends Event {}

sig Abort extends Event {}

abstract sig ReadWriteEvent extends Event {
    obj: Object,
    v: Version
}
sig Write extends ReadWriteEvent {
    wn : WriteNumber,
    installs : lone Version
}

sig Read extends ReadWriteEvent {
    sees: Write // operation that did the write
}

sig VersionNumber {}

sig WriteNumber {}

// installed (committed) versions
sig Version {
    obj: Object,
    tr: CommittedTransaction,
    vn: VersionNumber,
}

sig Vset {
    vs : set Version
}

sig Predicate {
    matches : set Version
}

sig PredicateRead extends Event {
    vset : Vset,
    p: Predicate,
    vs : set Version
}

fun events[t : Transaction] : set Event {
    (Event <: tr).t
}


/**
 * G1b: Intermediate Reads.
 * 
 * A history H shows phenomenon G1b if it contains a committed transaction
 * T2 that has read a version of object x written by transaction T1 that was not T1’s
 * final modification of x.
*/
pred G1b {
    some T1 : Transaction, T2 : CommittedTransaction, r : events[T2] & Read | let x = r.obj, wi=r.sees |
    {
        no T1 & T2 // different transactions
        wi.tr = T1
        some wj : (events[T1] - wi) & Write | {
            wj.obj = x
            wi->wj in eo
        }
    }
}


/**
 * G1c: Circular Information Flow.
 * 
 * A history H exhibits phenomenon G1c if DSG(H) contains a directed cycle
 * consisting entirely of dependency edges
 */
pred G1c {
    not acyclic[ww + wr, CommittedTransaction]
}

fun DSG[] : CommittedTransaction -> CommittedTransaction {
    ww + wr + rw
}



/**
 * G2: Anti-dependency Cycles. A history H exhibits
 * phenomenon G2 if DSG(H) contains a directed cycle
 * with one or more anti-dependency edges.
*/
pred G2 {
    // must contain a cycle
    not acyclic[DSG, CommittedTransaction]

    // must not contain a cycle if there are no antidependency edges
    acyclic[DSG - rw, CommittedTransaction]
}


/*
G2-item: Item Anti-dependency Cycles. A history H exhibits phenomenon G2-item if
DSG(H) contains a directed cycle having one or more item-antidependency edges.
*/
pred G2item {
    // must contain a cycle
    some iden & ^DSG

    // must not contain a cycle if there are no item-antidependency edges
    no iden & ^(DSG - irw)
}


//
//
// Facts
//
//

// operations

fact "enext relation" {
    irreflexive[enext]

    all T : Transaction, disj e1, e2 : events[T] |  {
        e1->e2 in enext <=> {
            e1->e2 in eo
            no e3 : events[T] - (e1 + e2) | (e1->e3 + e3->e2) in eo
        }
    }
}

fact "write number is consistent with execution order" {
    all T : Transaction, disj w1, w2 : events[T] & Write | 
        lt[w1.wn, w2.wn] <=> w1 -> w2 in eo
}

fact "first write is first write number" {
    all T : Transaction, w : events[T] & Write |
        no w.^~enext => w.wn = first
}

fact "write number goes up one at a time" {
    all T : Transaction, disj w1, w2 : events[T] & Write | ({
        w1.obj = w2.obj
        w1 -> w2 in eo
        no w3 : events[T] & Write - (w1+w2) | w3.obj=w1.obj and (w1->w3 + w3->w2) in eo
    } => w1.wn.next = w2.wn)
}

/**
 * 4.2: Transaction histoires
 * The partial order of events E in a history obeys the following constraints:
 */
fact "Event order (eo) is a partial order on operations" {
    partialOrder[eo, Event]
}

fact "eo preserves the order of all events within a transaction including the commit and abort events" {
    enext in eo
}

fact "all events within a transaction are totally ordered" {
    all T : Transaction | totalOrder[eo, events[T]]
}

fact "If an event rj (xi:m) exists in E, it is preceded by wi (xi:m) in E" {
    // We model this with the "sees" relation. 
    // If a read sees a write,
    // then it must precede the write.
    // Note: sees points in the opposite direction from eo
    sees in ~eo
}


// If an event wi (xi:m) is followed by ri (xj) without an intervening event wi (xi:n) in E, xj must be xi:m

fact "transaction must read its own writes" {
    all T : Transaction, w : T.events & Write, r : T.events & Read | ({
            w.obj = r.obj
            w->r in eo
            no v : T.events & Write | v.obj = r.obj and (w->v + v->r) in eo
    } => r.sees = w)

}


// transactions

fact "all transactions contain exactly one commit or abort" {
    all t : Transaction | one events[t] & (Commit + Abort)
}

fact "nothing comes after an abort or a commit" {
    no (Commit + Abort).enext
}

fact "no empty transactions" {
    no t : Transaction | no t.events - (Commit + Abort)
}


fact "committed transactions contain a commit" {
    all t : CommittedTransaction | some Commit & t.events
}

fact "aborted transactions contain an abort" {
    all t : AbortedTransaction | some Abort & t.events
}

// predicate reads

fact "predicate read is consistent with predicate" {
    all pread : PredicateRead | pread.vs = pread.vset.vs & pread.p.matches
}


// vsets

fact "Vsets are complete" {
    all vset : Vset |
        Object in vset.vs.obj
}

fact "only one version per object in a vset" {
    all vset : Vset | no disj v1, v2 : vset.vs |
        v1.obj = v2.obj
}

fact "Vsets are unique" {
    no disj vset1, vset2 : Vset | vset1.vs = vset2.vs
}

