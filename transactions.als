open util/relation
open util/ordering[V] as vo

// transactions
abstract sig Transaction {
    ops : set Op
}


// committed transactions
sig T extends Transaction {} {
    some Commit
    Commit in ops
}

// aborted transactions
sig A extends Transaction {} {
    some Abort
    Abort in ops
}

// Operations, also known as Events
abstract sig Op {
    tr: Transaction,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
}

sig Commit extends Op {}

sig Abort extends Op {}

// commit and abort
fact {
    // all transactions contain a commit or an abort
    all t : Transaction | one t.ops & (Commit + Abort)

    // no transactions contain both a commit and abort
    no t : Transaction | Commit in t.ops and Abort in t.ops

    // commits and aborts come last
    no Commit.tn
    no Abort.tn
}

// See 4.2: Transaction histoires
fact "event ordering" {
    partialOrder[eo, Op]

    // If an event rj (xi:m) exists in E, it is preceded by wi (xi:m) in E.
    // Note: sees points in the opposite direction of event order (sees points backwards in time, eo points forward)
    sees in ~eo

    // If an event wi (xi:m) is followed by ri (xj ) without an
    // intervening event wi (xi:n) in E, xj must be xi:m. This
    // condition ensures that if a transaction modifies object
    // x and later reads x, it will observe its last update to x.
    all tr : Transaction, wr : Wr & tr.ops, rd : Rd & tr.ops |
        ((wr->rd in eo) and (no ww : Wr & tr.ops | (wr->ww + ww->rd) in eo)) => rd.sees = wr
}

fact "transaction-next" {
    irreflexive[tn]

    // Section 4.2:
    // It preserves the order of all events within a transaction
    // including the commit and abort events
    tn in eo

    // every pair of ops in a transaction must be reachable via tn 
    // in one direction or the other
    all t : Transaction, disj o1, o2: t.ops |
        o1->o2 in ^tn + ^~tn
}


// read-write operations
abstract sig RWOp extends Op {
    obj: Obj,
    v: V
}

// writes
sig Wr extends RWOp {}

pred first_write_of_obj[wr : Wr] {
    no ww : wr.^~tn & Wr | ww.obj = wr.obj
}

fact "writes must happen in version order" {
    // initial write is first version
    all t : Transaction, wr : t.ops & Wr |
        first_write_of_obj[wr] => wr.v = vo/first

    // next writes are always successive versions
    all t : Transaction, disj w1,w2 : t.ops & Wr |
        ((w1->w2 in ^tn) and (no w3: t.ops & Wr | (w1->w3 + w3->w2) in ^tn)) => w2.v = next[w1.v]
}

// reads
sig Rd extends RWOp {
    tw: Transaction,  // transaction that did the write
    sees: Wr // operation that did the write
} {
    v = sees.@v // version read is same as verion written
    obj = sees.@obj // object read is same as object written
    sees.@tr = tw // seen write op belongs to transaction that does the write
}


// versions
sig V {}

// committed versions
sig CV {
    obj: Obj,
    tr: T,
    wr: Wr,
    v: V
} {
    this in obj.cvs
    wr in tr.ops
    wr.@obj = obj
    wr.@v = v
}

abstract sig Obj {
    // committed versions
    cvs : set CV
}

fact "transaction can only commit one version" {
    all obj : Obj |
        no disj cv1, cv2 : obj.cvs |
            cv1.tr = cv2.tr

}

one sig X,Y extends Obj {}

pred runner {
    some eo
    some CV
}

run runner for 6