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

run {}


sig VersionNumber {}

// installed (committed) versions
sig Version {
    obj: Object,
    tr: CommittedTransaction,
    vn: VersionNumber,
}

// set of versions seen by a predicate read
sig Vset {
    vs : set Version
}

sig VsetPredicate extends Predicate {
    matches : set Version
}

sig VsetPredicateRead extends PredicateRead {
    vset : Vset
}

fun vs[pread : VsetPredicateRead] : set Version {
    pread.vset.vs & pread.p.matches
}


fun installs[T : Transaction] : set Version {
    Version <: tr.T
}


// predicate reads

fact "objects in predicate read are the objects that match in the version set"{
    all pread : VsetPredicateRead |
        pread.objs = (pread.vset.vs & pread.p.matches).obj
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


// Installed version



fact "every installed version must have an associated write" {
    all v : Version | some w : Write & v.tr.events | w.obj = v.obj
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
        let m=rj.p.matches | xh in m <=> xi not in m
    }
}

// Directly anti-depends
fun rw[]: CommittedTransaction -> CommittedTransaction {
    irw + prw
}

fun next_version[v : Version] : lone Version {
    {w : Version | {
        w.obj = v.obj
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
    v1.obj = v2.obj
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
        some ri : Ti.events & PredicateRead, xk : ri.vset.vs, xj : Tj.installs |
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
