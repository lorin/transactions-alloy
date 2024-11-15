open util/relation
open util/ordering[VersionNumber] as vo

run {

} for 5 but exactly 1 Transaction, exactly 1 Object, exactly 3 Write

abstract sig Object {
    vs : set Version,
    next : Version lone -> lone Version
}

abstract sig Transaction {
    events : set Event
}

sig CommittedTransaction extends Transaction {
    installs : set Version,

    ww : set CommittedTransaction, // directly write-depends

    iwr : set CommittedTransaction, // directly item-read-depends
    pwr : set CommittedTransaction, // directly predicate-read-depends
    wr : set CommittedTransaction, // directly read-depends
    irw : set CommittedTransaction, // directly item-anti-depends
    prw : set CommittedTransaction, // directly directly predicate-anti-depends
    rw : set CommittedTransaction, // directly anti-depends
}

sig AbortedTransaction extends Transaction {}


abstract sig Event {
    tr: Transaction,
    eo: set Event, // event order (partial ordering of events)
    next: lone Event // next operation in the transaction
}

sig Commit extends Event {}

sig Abort extends Event {}

abstract sig ReadWriteEvent extends Event {
    obj: Object,
    v: Version
}
sig Write extends ReadWriteEvent {
    ith : VersionNumber,  // which write this is
    installs : lone Version
}

sig Read extends ReadWriteEvent {
    tw: Transaction,  // transaction that did the write
    sees: Write // operation that did the write
}

sig VersionNumber {}

// installed (committed) versions
sig Version {
    obj: Object,
    tr: CommittedTransaction,
    wo: Write,
    i: VersionNumber,
    vn: lone Version // next-version
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
    some T1 : AbortedTransaction, T2 : CommittedTransaction, r : T2.events & Read, w : T1.events & Write | r.sees = w
}


/**
 * G1b: Intermediate Reads.
 * 
 * A history H shows phenomenon G1b if it contains a committed transaction
 * T2 that has read a version of object x written by transaction T1 that was not T1’s
 * final modification of x.
*/
pred G1b {
    some T1 : Transaction, T2 : CommittedTransaction, r : T2.events & Read | let x = r.obj, wi=r.sees |
    {
        no T1 & T2 // different transactions
        wi.tr = T1
        some wj : (T1.events - wi) & Write | {
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

fact "every op is in the set of operations of the transaction it is associated with" {
    all op : Event | op in op.tr.events
}

fact "every op is associated with exactly one transaction" {
    all op : Event | one ~events[op]
}

fact "Event.next relation is irreflexive" {
    irreflexive[this/Event <: next]
}

fact "ith relationship is consistent with eo" {
    all T : Transaction, disj w1, w2 : T.events & Write | 
        lt[w1.ith, w2.ith] <=> w1 -> w2 in eo
}

fact "first write is first ith" {
    all T : Transaction, w : T.events & Write |
        no w.^~next => w.ith = first
}

fact "ith goes up one at a time" {
    all T : Transaction, w1, w2 : T.events & Write | ({
        w1.obj = w2.obj
        w1 -> w2 in eo
        no w3 : T.events & Write | w3.obj=w1.obj and (w1->w3 + w3->w2) in eo
    } => w1.ith.next = w2.ith)
}

/**
 * 4.2: Transaction histoires
 * The partial order of events E in a history obeys the following constraints:
 */
fact "Event order (eo) is a partial order on operations" {
    partialOrder[eo, Event]
}

fact "eo preserves the order of all events within a transaction including the commit and abort events" {
    (this/Event <: next) in eo
}

fact "all events within a transaction are totally ordered" {
    all T : Transaction | totalOrder[eo, T.events]
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
    all t : Transaction | one t.events & (Commit + Abort)
}

fact "nothing comes after an abort or a commit" {
    no (Commit + Abort).next
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


fact installs {
    all t: CommittedTransaction | t.installs = t.events.installs
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

