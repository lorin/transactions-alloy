/**
 * Based on the following paper:
 *
 * Generalized Isolation Level Definitions,
 * Atul Adya, Barbara Liskov, Patrick O'Neil.
 * Proceedings of the IEEE International Conference on Data Engineering, March 2000.
 *
 * https://pmg.csail.mit.edu/papers/icde00.pdf
**/
open util/ordering[VersionNumber] as vo
open transactions as t
open bbg as b


// run {} for 5 but exactly 1 Transaction

run {
    some irw
} for 7 but exactly 3 Transaction, exactly 2 Object, exactly 0 AbortedTransaction

/*
run {
    G2
    // not G2item
    // no AbortedTransaction
} for 7 but exactly 3 Transaction, exactly 1 Predicate, exactly 2 Object
*/

// check PL3_implies_anomaly_serializable_broad for 5

// check PL2_99_implies_PL3 for 7 but exactly 2 Transaction

assert anomaly_serializable_strict_implies_PL3 {
    always_read_most_recent_write => (b/AnomalySerializableStrict => PL3)
}


assert PL3_implies_anomaly_serializable_broad {
    always_read_most_recent_write => (PL3 => b/AnomalySerializableBroad)
}

assert PL2_99_implies_PL3 {
    PL2_99 => PL3
}

// This isn't true in general but it's true for the locking model
pred always_read_most_recent_write[] {
    all rd: Read | no wr: Write | {
        rd.obj = wr.obj
        (rd.sees->wr + wr->rd) in b/teo - iden
    }
}

fun gnext[] : Event -> Event {
    b/gnext
}


one sig InitialTransaction extends CommittedTransaction {}


sig VersionNumber {}

// installed (committed) versions
sig Version {
    obj: Object,
    tr: one CommittedTransaction,
    vn: VersionNumber
}

sig InitialVersion in Version {}

// set of versions seen by a predicate read
sig VsetPredicate extends Predicate {
    matches : set Version
}

sig VsetPredicateRead extends PredicateRead {
    vset : set Version
}

fun vs[pread : VsetPredicateRead] : set Version {
    pread.vset & pread.p.matches
}


fun installs[T : Transaction] : set Version {
    Version <: tr.T
}

fun installs[] : Commit -> set Version {
    {c : Commit, v : Version | v.tr=c.tr}
}

//
// initial transaction
//
fact "initial transaction has one write per object" {
    all o : Object | one events[InitialTransaction] & writes[o]
}

fact "initial transaction has only writes" {
    no events[InitialTransaction] & (Event-Write-Commit)
}


// initial version


fact "initial versions are associated with the initial transaction" {
    all v : Version | v in InitialVersion <=> v.tr = InitialTransaction
}

fact "there is exactly one initial version for each object" {
    all o : Object | one v : InitialVersion |  v.obj = o
}

fact "initial versions have the initial version number" {
    all v : InitialVersion | v.vn = vo/first
}


// predicate reads

fact "objects in predicate read are the objects that match in the version set"{
    all pread : VsetPredicateRead |
        pread.objs = (pread.vset & pread.p.matches).obj
}

pred same_object[v1, v2 : Version] {
    v1.obj = v2.obj
}


// vsets

fact "Vsets are complete" {
    all p : VsetPredicateRead |
        Object in p.vset.obj
}

fact "only one version per object in a vset" {
    all p : VsetPredicateRead | no disj v1, v2 : p.vset |
        same_object[v1, v2]
}


// Installed versions

fact "every installed version must have an associated write" {
    all v : Version - InitialVersion | some w : Write & v.tr.events |  w.obj = v.obj
}

fact "at most one version per (object, transaction) pair" {
    all T : CommittedTransaction, o : Object |
        lone {v : Version | v.tr=T and v.obj=o}
}

fact "every object written in a committed transaction must have an associated installed version" {
    all t : CommittedTransaction, w : Write & events[t], o : w.obj |
        some v : Version | {
            v.tr = t
            v.obj = o
        }
}

fact "one version is the first one" {
    all v1 : Version |
        some v2 : Version | {
            v1.obj = v2.obj
            v2.vn = vo/first
        }
}

fact "all versions except the first have a predecessor" {
    all v1 : Version |
        (no v1.vn & vo/first) => some v2 : Version | {
            same_object[v1, v2]
            v1.vn.prev = v2.vn
        }
}

fact "version numbers are unique" {
    all disj v1, v2 : Version | {
        same_object[v1, v2] => no (v1.vn & v2.vn)
    }
}

fun first_event[T : Transaction] : Event {
    {e : events[T] | no tnext.e}
}

fun last_event[T : Transaction] : Event {
    {e : events[T] | no tnext[e]}
}

pred happens_before[T1, T2 : Transaction] {
    lt[last_event[T1],first_event[T2]]
}

fact "version numbers are consistent with transaction ordering" {
    all disj v1, v2 : Version |
        (same_object[v1,v2] and happens_before[v1.tr, v2.tr]) => lt[v1.vn, v2.vn]
}



// Directly write-depends
fun ww[] : CommittedTransaction -> CommittedTransaction {
    { disj Ti, Tj : CommittedTransaction | some v1 : Ti.installs, v2 : Tj.installs | {
        same_object[v1, v2]
        v1.tr = Ti
        v2.tr = Tj
        next_version[v1] = v2
        }
    }
}

// Directly read-depends
fun wr[] : CommittedTransaction -> CommittedTransaction {
    iwr + pwr
}

// True if wr is the last write for an object in its transaction
pred is_last_write[w : Write] {
    no u : Write & w.^tnext | u.obj = w.obj
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
        some rj : events[Tj] & PredicateRead, xk : rj.vset, xi : installs[Ti] |
            {
                same_object[xi, xk]
                lte[xi.vn, xk.vn] // xi's version is less than or equal to xk's version
                changes_the_matches_of[xi, rj]
            }
    }
 }

 fun prev[x : Version] : lone Version {
    {v : Version | {
        same_object[x,v]
        v.vn=prev[x.vn]
    }}
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
        let m=rj.p.matches | xh in m <=> xi not in m
    }
}

// Directly anti-depends
fun rw[]: CommittedTransaction -> CommittedTransaction {
    irw + prw
}

fun next_version[v : Version] : lone Version {
    {w : Version | {
        same_object[w, v]
        w.vn = vo/next[v.vn]
    }}
}


// Directly item-anti-depends: We say that Tj directly item-anti-depends on
// transaction Ti if Ti reads some object version xk and Tj installs x’s next
// version (after xk ) in the version order. Note that the transaction that wrote
// the later version directly item-anti-depends on the transaction that read the
// earlier version
fun irw[]: CommittedTransaction -> CommittedTransaction {
    {disj Ti, Tj : CommittedTransaction |
        some xk, xl : Version  |  {
            Ti.reads[xk]
            xl = xk.next_version
            some xl & Tj.installs
        }
    }
}

// true if v1 is a later version than v2
pred later_version[v1, v2 : Version] {
    same_object[v1, v2]
    gt[v1.vn, v2.vn]
}

/*

Directly predicate-anti-depends:

We say that Tj directly predicate-anti-depends on Ti if Tj overwrites an
operation ri (P: Vset(P)), i.e.,

Tj installs a later version of some object that changes the matches of a predicate-based read performed by Ti

*/
fun prw[]: CommittedTransaction -> CommittedTransaction {
    {disj Ti, Tj : CommittedTransaction |
        some ri : Ti.events & PredicateRead, xk : ri.vset, xj : Tj.installs |
            later_version[xj, xk] and changes_the_matches_of[xj, ri]
    }
}



//
// Phenomena
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
 * A history H shows phenomenon G1a if it contains an aborted transaction T1
 * and a committed transaction T2 such that T2 has read some object (maybe via a predicate)
 * modified by T1.
 */
pred G1a {
    some T1 : AbortedTransaction, T2 : CommittedTransaction, w : events[T1] & Write,
          r : events[T2] & Read | r.sees = w
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
    some iden & ^DSG

    // must not contain a cycle if there are no antidependency edges
    no iden & ^(DSG - rw)
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
// Isolation levels
//
//


/**
 * We define PL-1 as the level in which G0 is disallowed
 */
pred PL1 {
    not G0
}

/**
 * We define isolation level PL-2 as one in which phenomenon G1 is disallowed
 */
pred PL2 {
    not G1
}

/*
 * We define level PL-2.99 as one that proscribes G1 and G2-item
 */
pred PL2_99 {
    not G0
    not G1
    not G2item
}

/**
 * We define PL-3 as an isolation level that proscribes G1 and G2
 */
pred PL3 {
    not G1
    not G2
}
