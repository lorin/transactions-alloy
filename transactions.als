open util/relation
open util/ordering[N] as vo

one sig X,Y extends Obj {}

run {some prw} for 6 but exactly 1 P


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

/*
* We define PL-3 as an isolation level that proscribes G1 and G2
*/
assert PL3 {
    not G1
    not G2
}


/**
 * G0: Write Cycles. A history H exhibits phenomenon
 * G0 if DSG(H) contains a directed cycle consisting
 * entirely of write-dependency edges.
 */
pred G0 {
    some iden & ^ww
}

pred G1 {
    G1a or G1b or G1c
}

/*
G1a: Aborted Reads

A history H shows phenomenon G1a if it contains an aborted transaction T1 and a
committed transaction T2 such that T2 has read some object modified by T1

*/
pred G1a {
    some T1 : A, T2 : T, r : T2.ops & Rd, w : T1.ops & Wr | r.sees = w
}


/*
G1b: Intermediate Reads.

A history H shows phenomenon G1b if it contains a committed transaction
T2 that has read a version of object x written by transaction T1 that was not T1’s
final modification of x.
*/
pred G1b {
    some T1 : Transaction, T2 : T, r : T2.ops & Rd | let x = r.obj, wi=r.sees |
    {
        no T1 & T2 // different transactions
        wi.tr = T1
        some wj : (T1.ops - wi) & Wr | {
            wj.obj = x
            wi->wj in eo
        }
    }
}

/*
G1c: Circular Information Flow.

A history H exhibits phenomenon G1c if DSG(H) contains a directed cycle
consisting entirely of dependency edges
*/
pred G1c {
    some iden & ^(ww + wr)
}

fun DSG[] : T -> T {
    ww + wr + rw
}

/*
G2: Anti-dependency Cycles. A history H exhibits
phenomenon G2 if DSG(H) contains a directed cycle
with one or more anti-dependency edges.
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

abstract sig Obj {
    // committed versions
    vs : set V,

    // "next" relation of committed versions
    cvn : V lone -> lone V
}

// transactions
abstract sig Transaction {
    ops : set Op
}

// committed transactions
sig T extends Transaction {
    installs : set V,

    ww : set T, // directly write-depends

    iwr : set T, // directly item-read-depends
    pwr : set T, // directly predicate-read-depends
    wr : set T, // directly read-depends
    irw : set T, // directly item-anti-depends
    prw : set T, // directly directly predicate-anti-depends
    rw : set T, // directly anti-depends
}


// aborted transactions
sig A extends Transaction {}

// Operations, also known as Events
abstract sig Op {
    tr: Transaction,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
}

sig Commit extends Op {}

sig Abort extends Op {}

// read-write operations
abstract sig RWOp extends Op {
    obj: Obj,
    i: N
}

// writes
sig Wr extends RWOp {
    installs : lone V
}


pred first_write_of_obj[wr : Wr] {
    no ww : wr.^~tn & Wr | ww.obj = wr.obj
}

// reads
sig Rd extends RWOp {
    tw: Transaction,  // transaction that did the write
    sees: Wr // operation that did the write
}

// version numbers
sig N {}

// installed (committed) versions
sig V {
    obj: Obj,
    tr: T,
    wo: Wr, // write operation
    i: N,
    vn: lone V // next-version
}


sig Vset {
    vs : set V
}

sig P {
    matches : set V
}

// Predicate read
sig PRead extends Op {
    vset : Vset,
    p: P,
    vs : set V
}

fact {
    all t: T | t.installs = t.ops.installs
}


fact "predicate read is consistent with predicate" {
    all pread : PRead | pread.vs = pread.vset.vs & pread.p.matches
}

fact "Vsets are complete" {
    all vset : Vset |
        Obj in vset.vs.obj
}

fact "only one version per object in a vset" {
    all vset : Vset | no disj v1, v2 : vset.vs |
        v1.obj = v2.obj
}

fact "Vsets are unique" {
    no disj vset1, vset2 : Vset | vset1.vs = vset2.vs
}

fact OpStuff {
    all op : Op | {
        op in op.tr.ops // this op is in the operations of the transactions it is associated with
        one ~ops[op] // this op is associated with exactly one transaction
    }
}

fact "no empty transactions" {
    no t : Transaction | no t.ops - (Commit + Abort)
}

fact "all transactions contain a commit or an abort" {
    all t : Transaction | one t.ops & (Commit + Abort)
}

fact "no transasctions contain both a commit and an abort" {
    no t : Transaction | some Commit & t.ops and some Abort & t.ops
}

fact "nothing comes after an abort" {
    no Abort.tn
}


// This fact is inconsistent with something else!
fact "nothing comes after a commit" {
    no Commit.tn
}

fact "tn is irreflexive" {
    irreflexive[tn]
}


// See 4.2: Transaction histoires
fact {
    partialOrder[eo, Op]
}


// If an event rj (xi:m) exists in E, it is preceded by wi (xi:m) in E.
// Note: sees points in the opposite direction of event order (sees points backwards in time, eo points forward)
fact {
    sees in ~eo
}

// If an event wi (xi:m) is followed by ri (xj ) without an
// intervening event wi (xi:n) in E, xj must be xi:m. This
// condition ensures that if a transaction modifies object
// x and later reads x, it will observe its last update to x.
fact {
    all tr : Transaction, wr : Wr & tr.ops, rd : Rd & tr.ops |
        ((wr->rd in eo) and (no ww : Wr & tr.ops | (wr->ww + ww->rd) in eo)) => rd.sees = wr
}


// Section 4.2:
// It preserves the order of all events within a transaction
// including the commit and abort events
fact {
    tn in eo
}

// all operations in a transaction are reachable from some first operation
fact {
    all t : Transaction | some op : t.ops |
        (t.ops - op) in op.^tn
}

fact CommittedVersionNextVersion {
    vn = Obj.cvn
}

fact CommittedTransaction {
    all t : T | some Commit & t.ops
}

fact AbortedTransaction {
    all t : A | some Abort & t.ops
}


fact InstallsCommittedVersion {
    installs = ~wo
}

fact "installed version is always last write for that object" {
    all t : T, wr : t.ops & Wr |
        (some wr.installs) <=> (no ww : wr.(^tn) & Wr | ww.obj = wr.obj)
}


fact "if a read sees a write in the same transaction, it must be the most recent one" {
    all t : Transaction, rd : t.ops & Rd |
        (rd.sees in t.ops) => no wr : t.ops & Wr | {
            rd.obj = wr.obj
            // wr is before rd
            wr in rd.^~tn

            // wr is after the seen write (rd.sees)
            wr in rd.sees.^tn
        }
}

fact OpStuff {
    all op : Op | {
        op in op.tr.ops // this op is in the operations of the transactions it is associated with
        one ~ops[op] // this op is associated with exactly one transaction
    }
}

fact "committed versions are associated with the object" {
    all o : Obj | o.vs.obj in o
}

fact "cvn relations must be associated with the object" {
    all o : Obj |  {
        no o.cvn.V.obj - o
        no o.cvn[V].obj - o
    }
}

fact "initial write of an object is the first version" {
    all t : Transaction, wr : t.ops & Wr |
        first_write_of_obj[wr] => wr.i = vo/first
}

fact "next writes are always successive versions" {
    all t : Transaction, disj w1,w2 : t.ops & Wr | {
        w1.obj = w2.obj
        w1->w2 in ^tn
        no w3 : t.ops & Wr | {
            w1.obj = w3.obj
            w1->w3 in ^tn
            w3->w2 in ^tn
        }} => w2.i = next[w1.i]
}


fact RdSees {
    all rd : Rd |  {
        rd.i = rd.sees.i // version read is same as verion written
        rd.obj = rd.sees.obj // object read is same as object written
        rd.sees.tr = rd.tw // seen write op belongs to transaction that does the write
    }
}



fact CommittedVersions {
    all v : V |  {
        v in v.obj.vs
        v.wo.i = v.i
        v.wo in v.tr.ops
        v.wo.obj = v.obj
    }
}


fact "transaction can only commit one version" {
    all obj : Obj |
        no disj cv1, cv2 : obj.vs |
            cv1.tr = cv2.tr
}

fact "CV-next relation" {
    all o : Obj | {
        irreflexive[o.cvn]
        totalOrder[*(o.cvn), o.vs]
    }
}

// ++

fact DirectlyWriteDepends {
    irreflexive[ww]

    all disj Ti, Tj : T | Ti->Tj in ww <=>
        some cv1 : Ti.installs, cv2 : Tj.installs | {
            cv1.obj = cv2.obj
            cv1.tr = Ti
            cv2.tr = Tj
            cv1->cv2 in vn
        }
}

fact DirectlyReadDepends {
    wr = iwr + pwr
}


// We say that Tj directly item-read-depends on Ti if Ti installs some object version
// xi and Tj reads xi
fact DirectlyItemReadDepends {
    irreflexive[iwr]

    all disj Ti, Tj : T | Ti->Tj in iwr =>
        some cv : Ti.installs, rd : Rd & Tj.ops {
            rd.sees = cv.wo
        }
}


fact DirectlyAntiDepends {
    rw = irw + prw
}

// True if transaction T has a read that corresponds to this committed version
pred reads[t : Transaction, v: V] {
    some rd : t.ops & Rd | rd.sees.installs = v
}



// Directly item-anti-depends: We say that Tj directly item-anti-depends on
// transaction Ti if Ti reads some object version xk and Tj installs x’s next
// version (after xk ) in the version order. Note that the transaction that wrote
// the later version directly item-anti-depends on the transaction that read the
// earlier version
//
fact DirectlyItemAntiDepends {
    irreflexive[irw]
    all disj Ti, Tj : T | Ti->Tj in irw <=>
        some xk : V | {
            // Ti reads xk
            reads[Ti, xk]

            // Tj modifies the next version of xk
            xk.vn.tr = Tj
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
pred changes_the_matches_of[xi : V, rj : PRead] {
    some xh : vn.xi  |
        let m=rj.p.matches |
            (xh in m and xi not in m) or (xh not in m and xi in m)
}

pred lt[Xi: V, Xk: V] {
    Xi->Xk in ^vn
}
/**
 * Directly predicate-read-depends:
 * 
 * Transaction Tj directly predicate-read-depends on Ti if Tj performs an operation rj (P: Vset(P)),
 * xk ∈ Vset(P), i = k or xi << xk, and xi changes the matches of rj (P: Vset(P)).
 */
fact DirectlyPredicateReadDepends {

    irreflexive[pwr]

    all disj Ti, Tj : T |
        Ti->Tj in pwr <=> some rj : PRead & Tj.ops, xi : Ti.installs, xk : rj.vset.vs | {
            (xi=xk) or lt[xi, xk]
            changes_the_matches_of[xi, rj]
        }
}
/*

Directly predicate-anti-depends: 

We say that Tj directly predicate-anti-depends on Ti if Tj overwrites an
operation ri (P: Vset(P)), i.e., 

Tj installs a later version of some object that changes the matches of a predicate-based read performed by Ti

*/
fact DirectlyPredicateAntiDepends {

    irreflexive[prw]

    all disj Ti, Tj : T | 
        Ti->Tj in prw <=> some ri : PRead & Ti.ops, xj : Tj.installs | 
            changes_the_matches_of[xj, ri]
}